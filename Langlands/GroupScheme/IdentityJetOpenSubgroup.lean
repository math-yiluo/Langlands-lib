import Langlands.GroupScheme.IdentityJetSmoothUnitLocality
import Langlands.GroupScheme.IdentityJetProjectionGeometry
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange

/-! # Identity jets and rank along an open subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} {H N : GroupScheme S} (i : H ⟶ N)

/-- An open subgroup inclusion identifies the actual identity neighborhoods. -/
theorem map_isIso_of_isOpenImmersion [IsSeparated N.X.hom]
    [IsOpenImmersion i.hom.hom.left] (n : ℕ) : IsIso (map i n) := by
  let v := i.hom.hom.left
  have : IsSeparated H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have he : IsPullback H.identitySection (𝟙 S) v N.identitySection :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, identitySection_naturality]⟩
  have hk : N.identitySection.ker.comap v = H.identitySection.ker := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ← he.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  have : IsClosedImmersion (inclusion H n) := inferInstanceAs (IsClosedImmersion (ideal H n).subschemeι)
  have : IsClosedImmersion (inclusion N n) := inferInstanceAs (IsClosedImmersion (ideal N n).subschemeι)
  have hp : IsPullback (inclusion H n) (map i n) v (inclusion N n) := by
    apply isPullback_of_isClosedImmersion _ _ _ _ (map_inclusion i n).symm
    simp only [inclusion, Scheme.IdealSheafData.ker_subschemeι]
    change (ideal N n).comap v = ideal H n
    simp only [ideal, idealSheaf_comap_pow, hk]
  have : IsOpenImmersion (map i n) := MorphismProperty.of_isPullback hp inferInstance
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  refine top_unique (fun x _ => ?_)
  change x ∈ Set.range (map i n)
  rw [RelativeIdentityComponent.range_of_isPullback hp.flip]
  have hx : inclusion N n x ∈ Set.range (inclusion N n) := ⟨x, rfl⟩
  rw [range_inclusion_eq_range_identitySection] at hx
  obtain ⟨s, hs⟩ := hx
  exact ⟨H.identitySection s, by rw [← Scheme.Hom.comp_apply, identitySection_naturality]; exact hs⟩

private theorem smoothAlongUnit_iff_of_open [LocallyOfFinitePresentation N.X.hom]
    [IsOpenImmersion i.hom.hom.left] : SmoothAlongUnit H ↔ SmoothAlongUnit N := by
  let v := i.hom.hom.left
  have : LocallyOfFinitePresentation H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have h (x : S) : v (H.identitySection x) = N.identitySection x := by
    rw [← Scheme.Hom.comp_apply, identitySection_naturality]
  have hs (s : S) : (H.X.hom.stalkMap (H.identitySection s)).hom.FormallySmooth ↔
      (N.X.hom.stalkMap (N.identitySection s)).hom.FormallySmooth := by
    rw [← Scheme.Hom.mem_smoothLocus, ← Scheme.Hom.mem_smoothLocus, ← h s]
    change H.identitySection s ∈ H.X.hom.smoothLocus ↔
      H.identitySection s ∈ v ⁻¹ᵁ N.X.hom.smoothLocus
    have hv : v ⁻¹ᵁ N.X.hom.smoothLocus = H.X.hom.smoothLocus := by
      simpa only [show v ≫ N.X.hom = H.X.hom from Over.w i.hom.hom] using
        Scheme.Hom.preimage_smoothLocus_eq (f := v) (g := N.X.hom)
    rw [hv]
  exact ⟨fun h s => (hs s).mp (h s), fun h s => (hs s).mpr (h s)⟩

/-- Fixed-rank smoothness at the unit is preserved and reflected by an open subgroup inclusion. -/
theorem smoothAlongUnitOfRank_iff_of_open [IsSeparated N.X.hom] [LocallyOfFinitePresentation N.X.hom]
    [IsOpenImmersion i.hom.hom.left] (r : ℕ) :
    SmoothAlongUnitOfRank H r ↔ SmoothAlongUnitOfRank N r := by
  have : IsIso (map i 1) := map_isIso_of_isOpenImmersion i 1
  have h := map_projection i 1
  have hf : Flat (projection H 1) ↔ Flat (projection N 1) := by
    rw [← h]
    exact MorphismProperty.cancel_left_of_respectsIso @Flat (map i 1) (projection N 1)
  have : IsFinite (projection N 1) := finite_projection N 1
  have hr (hN : Flat (projection N 1)) : (projection H 1).finrank = (projection N 1).finrank := by
    rw [← h, Scheme.Hom.finrank_comp_left_of_isIso]
  exact ⟨fun hH => ⟨(smoothAlongUnit_iff_of_open i).mp hH.1, hf.mp hH.2.1,
      fun s => by rw [← hr (hf.mp hH.2.1)]; exact hH.2.2 s⟩,
    fun hN => ⟨(smoothAlongUnit_iff_of_open i).mpr hN.1, hf.mpr hN.2.1,
      fun s => by rw [hr hN.2.1]; exact hN.2.2 s⟩⟩

/-- An open subgroup of a separated locally finitely presented group has the
same actual jets and the same fixed-rank smoothness condition at the unit. -/
def IdentityJetOpenSubgroupStatement : Prop :=
  ∀ (S : Scheme.{u}) (H N : GroupScheme S) (i : H ⟶ N)
    [IsSeparated N.X.hom] [LocallyOfFinitePresentation N.X.hom]
    [IsOpenImmersion i.hom.hom.left],
    (∀ n : ℕ, IsIso (map i n)) ∧
      ∀ r : ℕ, SmoothAlongUnitOfRank H r ↔ SmoothAlongUnitOfRank N r

theorem identityJetOpenSubgroup : IdentityJetOpenSubgroupStatement.{u} :=
  fun _ _ _ i _ _ _ => ⟨map_isIso_of_isOpenImmersion i, smoothAlongUnitOfRank_iff_of_open i⟩

/-- A smooth group has an open neighborhood of every base point over which its
actual first jet has a fixed positive rank. -/
theorem exists_smoothAlongUnitOfRank_open (H : GroupScheme S) [IsSeparated H.X.hom]
    [Smooth H.X.hom] (s : S) :
    ∃ (U : S.Opens) (r : ℕ), s ∈ U ∧ SmoothAlongUnitOfRank ((baseChange U.ι).obj H) r := by
  let p := projection H 1
  obtain ⟨hfin, hflat, hfp⟩ := projection_geometry H 1
  let : IsFinite p := hfin
  let : Flat p := hflat
  let : LocallyOfFinitePresentation p := hfp
  let U : S.Opens := ⟨{x | p.finrank x = p.finrank s}, p.isLocallyConstant_finrank.isOpen_fiber _⟩
  let K := (baseChange U.ι).obj H
  have hpos : 1 ≤ p.finrank s := by
    have hs : p (identityLift H 1 s) = s := by
      rw [← Scheme.Hom.comp_apply, identityLift_projection]
      rfl
    rw [← hs]
    exact p.one_le_finrank_map _
  have : Smooth K.X.hom := inferInstanceAs (Smooth (pullback.snd H.X.hom U.ι))
  have : IsSeparated K.X.hom := inferInstanceAs (IsSeparated (pullback.snd H.X.hom U.ι))
  refine ⟨U, p.finrank s - 1, rfl, fun x => Scheme.Hom.mem_smoothLocus.mp ?_,
    (projection_geometry K 1).2.1, ?_⟩
  · rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  · intro x
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (baseChange_isPullback H U.ι 1)]
    exact x.property.trans (Nat.add_sub_of_le hpos).symm

end Langlands.GroupScheme.IdentityJet

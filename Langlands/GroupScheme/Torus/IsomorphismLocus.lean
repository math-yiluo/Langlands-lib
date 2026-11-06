import Langlands.GroupScheme.Torus.IsomorphismLocusAffine
import Langlands.GroupScheme.Torus.ClosedImmersionLocus
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.BaseChangeReflection

/-! # Isomorphism neighbourhoods over arbitrary bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusIsomorphismLocus

set_option backward.isDefEq.respectTransparency false in
/-- Actual iterated base change preserves the isomorphism condition under the
canonical direct-pullback comparison. -/
theorem isIso_comp_baseChange_iff {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') {H G : GroupScheme S} (i : H ⟶ G) :
    IsIso ((baseChange (c ≫ b)).map i) ↔
      IsIso ((baseChange c).map ((baseChange b).map i)) := by
  let eH := Descent.pullbackComparison b c (c ≫ b) rfl H
  let eG := Descent.pullbackComparison b c (c ≫ b) rfl G
  have hn := Descent.pullbackComparison_naturality b c (c ≫ b) rfl i
  calc
    _ ↔ IsIso (eH.hom ≫ (baseChange (c ≫ b)).map i) :=
      (isIso_comp_left_iff _ _).symm
    _ ↔ IsIso ((baseChange c).map ((baseChange b).map i) ≫ eG.hom) := by
      rw [hn]
    _ ↔ _ := isIso_comp_right_iff _ _

set_option backward.isDefEq.respectTransparency false in
/-- The underlying square of actual group-scheme base change is cartesian. -/
theorem underlying_isPullback {S T : Scheme.{u}} (b : T ⟶ S)
    {H G : GroupScheme S} (i : H ⟶ G) :
    IsPullback (pullback.fst H.X.hom b) ((baseChange b).map i).hom.hom.left
      i.hom.hom.left (pullback.fst G.X.hom b) := by
  have houter : IsPullback
      (((baseChange b).map i).hom.hom.left ≫ pullback.snd G.X.hom b)
      (pullback.fst H.X.hom b) b (i.hom.hom.left ≫ G.X.hom) := by
    change IsPullback (((Over.pullback b).map i.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w i.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback H.X.hom b).flip
  exact (houter.of_right
    (by
      change ((Over.pullback b).map i.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback G.X.hom b).flip).flip

set_option backward.isDefEq.respectTransparency false in
/-- An actual group homomorphism is invertible if its underlying scheme map is. -/
theorem isIso_of_underlying {S : Scheme.{u}} {H G : GroupScheme S}
    (i : H ⟶ G) [IsIso i.hom.hom.left] : IsIso i := by
  have : IsIso ((Over.forget S).map i.hom.hom) := inferInstanceAs (IsIso i.hom.hom.left)
  have : IsIso i.hom.hom := isIso_of_reflects_iso i.hom.hom (Over.forget S)
  let e : H ≅ G := Grp.mkIso' (asIso i.hom.hom)
  change IsIso e.hom
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Invertibility of actual group homomorphisms is local on a base open cover. -/
theorem isIso_of_openCover {S : Scheme.{u}} {H G : GroupScheme S}
    (i : H ⟶ G) (𝒰 : S.OpenCover)
    (hi : ∀ j, IsIso ((baseChange (𝒰.f j)).map i)) : IsIso i := by
  have hu : IsIso i.hom.hom.left := by
    apply (MorphismProperty.isomorphisms Scheme).of_zeroHypercover_target
      (𝒰.pullback₁ G.X.hom)
    intro j
    have h : IsIso ((baseChange (𝒰.f j)).map i).hom.hom.left := by
      have := hi j
      infer_instance
    let hp := underlying_isPullback (𝒰.f j) i
    change IsIso (pullback.snd i.hom.hom.left (pullback.fst G.X.hom (𝒰.f j)))
    apply (isIso_comp_left_iff hp.isoPullback.hom _).mp
    simpa only [hp.isoPullback_hom_snd] using h
  exact isIso_of_underlying i

/-- Over an arbitrary base, a field-valued isomorphism between split tori
extends to an open neighbourhood through which the supplied point factors. -/
theorem exists_open_split {S : Scheme.{u}} {H G : GroupScheme S}
    (hH : IsSplitTorus H) (hG : IsSplitTorus G) (i : H ⟶ G)
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ S)
    (hx : IsIso ((baseChange x).map i)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ S), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V, bx ≫ q = x ∧
        IsIso ((baseChange q).map i) := by
  let C := TorusClosedImmersionLocus.fieldPointAffineChart x
  let hp : IsOpenImmersion C.map := C.isOpen
  have hcx : IsIso ((baseChange (C.lift ≫ C.map)).map i) := by
    rw [C.fac]
    exact hx
  have hxi := (isIso_comp_baseChange_iff C.map C.lift i).mp hcx
  obtain ⟨V, q, hq, bx, hbx, hi⟩ :=
    exists_open_affine (hH.baseChange C.map) (hG.baseChange C.map)
      ((baseChange C.map).map i) K C.lift hxi
  let := hq
  refine ⟨V, q ≫ C.map, inferInstance, bx, ?_, ?_⟩
  · rw [← Category.assoc, hbx]
    exact C.fac
  · exact (isIso_comp_baseChange_iff C.map q i).mpr hi

/-- The union of all base opens over which an actual homomorphism is invertible. -/
def opens {S : Scheme.{u}} {H G : GroupScheme S} (i : H ⟶ G) : S.Opens :=
  ⨆ U : {U : S.Opens // IsIso ((baseChange U.ι).map i)}, U.1

/-- Every morphism whose image lies in this union pulls the homomorphism back
to an isomorphism. This implication does not need a torus hypothesis. -/
theorem isIso_of_range_subset_opens {S T : Scheme.{u}} {H G : GroupScheme S}
    (i : H ⟶ G) (b : T ⟶ S) (hb : Set.range b ⊆ opens i) :
    IsIso ((baseChange b).map i) := by
  let J := {U : S.Opens // IsIso ((baseChange U.ι).map i)}
  let 𝒰 := T.openCoverOfIsOpenCover (fun U : J => b ⁻¹ᵁ U.1) (by
    apply TopologicalSpace.IsOpenCover.mk
    apply top_le_iff.mp
    intro t _
    have ht := hb (Set.mem_range_self t)
    change b t ∈ ⨆ U : J, U.1 at ht
    rw [TopologicalSpace.Opens.mem_iSup] at ht
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨U, hU⟩ := ht
    exact ⟨U, hU⟩)
  apply isIso_of_openCover ((baseChange b).map i) 𝒰
  intro U
  have : IsIso ((baseChange U.1.ι).map i) := U.2
  have h : IsIso ((baseChange ((b ∣_ U.1) ≫ U.1.ι)).map i) :=
    (isIso_comp_baseChange_iff U.1.ι (b ∣_ U.1) i).mpr inferInstance
  rw [morphismRestrict_ι] at h
  exact (isIso_comp_baseChange_iff b (b ⁻¹ᵁ U.1).ι i).mp h

/-- Passing from an open immersion to its actual open range preserves the
isomorphism obtained by base change. -/
theorem isIso_opensRange {S V : Scheme.{u}} {H G : GroupScheme S}
    (i : H ⟶ G) (q : V ⟶ S) [IsOpenImmersion q]
    [IsIso ((baseChange q).map i)] :
    IsIso ((baseChange q.opensRange.ι).map i) := by
  let e := IsOpenImmersion.isoOfRangeEq q q.opensRange.ι (by simp)
  have h : IsIso ((baseChange (e.inv ≫ q)).map i) :=
    (isIso_comp_baseChange_iff q e.inv i).mpr inferInstance
  have heq : e.inv ≫ q = q.opensRange.ι :=
    IsOpenImmersion.isoOfRangeEq_inv_fac q q.opensRange.ι _
  rwa [heq] at h

/-- For two split tori the global open union detects invertibility on every
test scheme, with no reducedness or connectedness restriction on that test. -/
theorem isIso_baseChange_iff_range_subset_opens
    {S T : Scheme.{u}} {H G : GroupScheme S}
    (hH : IsSplitTorus H) (hG : IsSplitTorus G) (i : H ⟶ G) (b : T ⟶ S) :
    IsIso ((baseChange b).map i) ↔ Set.range b ⊆ opens i := by
  refine ⟨fun hi => ?_, isIso_of_range_subset_opens i b⟩
  rintro _ ⟨t, rfl⟩
  have := hi
  let x := T.fromSpecResidueField t
  have hx : IsIso ((baseChange (x ≫ b)).map i) :=
    (isIso_comp_baseChange_iff b x i).mpr inferInstance
  obtain ⟨V, q, hq, bx, hbx, hqi⟩ :=
    exists_open_split hH hG i (T.residueField t) (x ≫ b) hx
  let := hq
  let := hqi
  have hU := isIso_opensRange i q
  apply (show q.opensRange ≤ opens i from
    le_iSup (fun U : {U : S.Opens // IsIso ((baseChange U.ι).map i)} => U.1)
      ⟨q.opensRange, hU⟩)
  change b t ∈ Set.range q
  refine ⟨bx (IsLocalRing.closedPoint (T.residueField t)), ?_⟩
  have hp := congrArg
    (fun f : Spec (T.residueField t) ⟶ S =>
      f (IsLocalRing.closedPoint (T.residueField t))) hbx
  change q (bx (IsLocalRing.closedPoint (T.residueField t))) =
    b (x (IsLocalRing.closedPoint (T.residueField t))) at hp
  have hxt : x (IsLocalRing.closedPoint (T.residueField t)) = t :=
    Scheme.fromSpecResidueField_apply t _
  rwa [hxt] at hp

/-- The actual open immersion of the isomorphism locus represents the
isomorphism condition after all base changes between split tori. -/
theorem isIso_baseChange_iff_factors
    {S T : Scheme.{u}} {H G : GroupScheme S}
    (hH : IsSplitTorus H) (hG : IsSplitTorus G) (i : H ⟶ G) (b : T ⟶ S) :
    IsIso ((baseChange b).map i) ↔
      ∃ a : T ⟶ opens i, a ≫ (opens i).ι = b := by
  rw [isIso_baseChange_iff_range_subset_opens hH hG i b]
  constructor
  · intro h
    have h' : Set.range b ⊆ Set.range (opens i).ι := by simpa using h
    exact ⟨IsOpenImmersion.lift (opens i).ι b h', IsOpenImmersion.lift_fac _ _ _⟩
  · rintro ⟨a, rfl⟩
    simpa only [Set.range_comp, Scheme.Hom.comp_base, TopCat.coe_comp,
      Scheme.Opens.range_ι] using Set.range_comp_subset_range a (opens i).ι

end Langlands.GroupScheme.TorusIsomorphismLocus

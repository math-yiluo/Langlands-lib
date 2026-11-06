import Langlands.GroupScheme.Torus.IsomorphismLocus
import Langlands.GroupScheme.Torus.Relative
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Étale descent of the torus isomorphism locus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusIsomorphismLocus

/-- Surjective flat locally finitely presented base change reflects
invertibility of actual group homomorphisms. -/
theorem isIso_of_fppf_baseChange {S V : Scheme.{u}} (q : V ⟶ S)
    [Surjective q] [Flat q] [LocallyOfFinitePresentation q]
    {H G : GroupScheme S} (i : H ⟶ G) [IsIso ((baseChange q).map i)] :
    IsIso i := by
  have : IsIso ((baseChange q).map i).hom.hom.left := inferInstance
  have : IsIso i.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme)
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
      (underlying_isPullback q i).flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  exact isIso_of_underlying i

/-- The open image of an étale map. -/
def etaleImage {S V : Scheme.{u}} (q : V ⟶ S) [Etale q] : S.Opens :=
  ⟨Set.range q, q.isOpenMap.isOpen_range⟩

/-- Invertibility after an étale map descends to its open image. -/
theorem isIso_etaleImage {S V : Scheme.{u}} {H G : GroupScheme S}
    (i : H ⟶ G) (q : V ⟶ S) [Etale q] [IsIso ((baseChange q).map i)] :
    IsIso ((baseChange (etaleImage q).ι).map i) := by
  let U := etaleImage q
  let q' : V ⟶ U := IsOpenImmersion.lift U.ι q (by simp [U, etaleImage])
  have hq' : q' ≫ U.ι = q := IsOpenImmersion.lift_fac _ _ _
  have : Surjective q' := ⟨fun ⟨x, ⟨y, hy⟩⟩ =>
    ⟨y, by
      apply U.ι.injective
      change (q' ≫ U.ι) y = x
      rw [hq']
      exact hy⟩⟩
  have : Etale (q' ≫ U.ι) := by rw [hq']; infer_instance
  have : Etale q' := Etale.of_comp q' U.ι
  have : IsIso ((baseChange q').map ((baseChange U.ι).map i)) := by
    apply (isIso_comp_baseChange_iff U.ι q' i).mp
    rw [hq']
    infer_instance
  exact isIso_of_fppf_baseChange q' ((baseChange U.ι).map i)

/-- The open image of every étale isomorphism neighbourhood lies in the
union of the base opens of invertibility. -/
theorem etaleImage_le_opens {S V : Scheme.{u}} {H G : GroupScheme S}
    (i : H ⟶ G) (q : V ⟶ S) [Etale q] [IsIso ((baseChange q).map i)] :
    etaleImage q ≤ opens i :=
  le_iSup (fun U : {U : S.Opens // IsIso ((baseChange U.ι).map i)} => U.1)
    ⟨etaleImage q, isIso_etaleImage i q⟩

/-- A common étale splitting cover suffices for the all-test open-locus
criterion. No condition is imposed on the test morphism. -/
theorem isIso_baseChange_iff_range_subset_opens_of_cover
    {S T : Scheme.{u}} {H G : GroupScheme S}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hH : ∀ j, IsSplitTorus ((baseChange (𝒰.f j)).obj H))
    (hG : ∀ j, IsSplitTorus ((baseChange (𝒰.f j)).obj G))
    (i : H ⟶ G) (b : T ⟶ S) :
    IsIso ((baseChange b).map i) ↔ Set.range b ⊆ opens i := by
  refine ⟨fun hi => ?_, isIso_of_range_subset_opens i b⟩
  rintro _ ⟨t, rfl⟩
  have := hi
  let 𝒲 := 𝒰.pullback₁ b
  obtain ⟨j, y, hy⟩ := Scheme.Cover.exists_eq 𝒲 t
  let x := (𝒲.X j).fromSpecResidueField y
  let z := x ≫ pullback.snd b (𝒰.f j)
  have hz : z ≫ 𝒰.f j = (x ≫ 𝒲.f j) ≫ b := by
    change (x ≫ pullback.snd b (𝒰.f j)) ≫ 𝒰.f j =
      (x ≫ pullback.fst b (𝒰.f j)) ≫ b
    simp only [Category.assoc, pullback.condition]
  have hxi : IsIso ((baseChange ((x ≫ 𝒲.f j) ≫ b)).map i) :=
    (isIso_comp_baseChange_iff b (x ≫ 𝒲.f j) i).mpr inferInstance
  rw [← hz] at hxi
  have hzi : IsIso ((baseChange z).map ((baseChange (𝒰.f j)).map i)) :=
    (isIso_comp_baseChange_iff (𝒰.f j) z i).mp hxi
  obtain ⟨V, q, hq, bz, hbz, hqi⟩ :=
    exists_open_split (hH j) (hG j) ((baseChange (𝒰.f j)).map i)
      ((𝒲.X j).residueField y) z hzi
  let := hq
  have : Etale (𝒰.f j) := 𝒰.map_prop j
  have : IsIso ((baseChange (q ≫ 𝒰.f j)).map i) :=
    (isIso_comp_baseChange_iff (𝒰.f j) q i).mpr hqi
  apply etaleImage_le_opens i (q ≫ 𝒰.f j)
  change b t ∈ Set.range (q ≫ 𝒰.f j)
  refine ⟨bz (IsLocalRing.closedPoint ((𝒲.X j).residueField y)), ?_⟩
  have hfac : bz ≫ (q ≫ 𝒰.f j) = (x ≫ 𝒲.f j) ≫ b := by
    rw [← Category.assoc, hbz]
    exact hz
  have hp := congrArg
    (fun f : Spec ((𝒲.X j).residueField y) ⟶ S =>
      f (IsLocalRing.closedPoint ((𝒲.X j).residueField y))) hfac
  change (q ≫ 𝒰.f j) (bz (IsLocalRing.closedPoint ((𝒲.X j).residueField y))) =
    b (𝒲.f j (x (IsLocalRing.closedPoint ((𝒲.X j).residueField y)))) at hp
  have hxy : x (IsLocalRing.closedPoint ((𝒲.X j).residueField y)) = y :=
    Scheme.fromSpecResidueField_apply y _
  rwa [hxy, hy] at hp

/-- An étale form of a split torus and a split target have the same
all-test open isomorphism locus as in the globally split case. -/
theorem isIso_baseChange_iff_range_subset_opens_of_relative_split
    {S T : Scheme.{u}} {H G : GroupScheme S}
    (hH : RelativeTorus.IsTorus H) (hG : IsSplitTorus G)
    (i : H ⟶ G) (b : T ⟶ S) :
    IsIso ((baseChange b).map i) ↔ Set.range b ⊆ opens i := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  exact isIso_baseChange_iff_range_subset_opens_of_cover
    𝒰 h𝒰 (fun j => hG.baseChange (𝒰.f j)) i b

/-- The actual open immersion represents invertibility after every base
change from a relative torus to a split torus. -/
theorem isIso_baseChange_iff_factors_of_relative_split
    {S T : Scheme.{u}} {H G : GroupScheme S}
    (hH : RelativeTorus.IsTorus H) (hG : IsSplitTorus G)
    (i : H ⟶ G) (b : T ⟶ S) :
    IsIso ((baseChange b).map i) ↔
      ∃ a : T ⟶ opens i, a ≫ (opens i).ι = b := by
  rw [isIso_baseChange_iff_range_subset_opens_of_relative_split hH hG i b]
  constructor
  · intro h
    have h' : Set.range b ⊆ Set.range (opens i).ι := by simpa using h
    exact ⟨IsOpenImmersion.lift (opens i).ι b h', IsOpenImmersion.lift_fac _ _ _⟩
  · rintro ⟨a, rfl⟩
    simpa only [Set.range_comp, Scheme.Hom.comp_base, TopCat.coe_comp,
      Scheme.Opens.range_ι] using Set.range_comp_subset_range a (opens i).ι

end Langlands.GroupScheme.TorusIsomorphismLocus

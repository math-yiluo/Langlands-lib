import Langlands.AlgebraicGeometry.GeometricIrreducibilityOpenCover
import Langlands.AlgebraicGeometry.GeometricIrreducibilityTransport
import Langlands.AlgebraicGeometry.GeometricallyIrreducibleGenericSpreadingStatement
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

universe u

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a morphism restricts its set-theoretic image to the target open. -/
theorem mem_range_morphismRestrict_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (y : V) :
    y ∈ Set.range (f ∣_ V) ↔ y.1 ∈ Set.range f := by
  rw [morphismRestrict_base, Set.range_restrictPreimage]
  rfl

/-- Geometric irreducibility of the actual generic fibre entails that the
generic point lies in the image of the original morphism. -/
theorem mem_range_of_geometricallyIrreducible_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (hgeneric : GeometricallyIrreducible (f.fiberToSpecResidueField η)) :
    η ∈ Set.range f := by
  let := hgeneric
  have : IrreducibleSpace (f.fiber η) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (f.fiberToSpecResidueField η)
  have hne : Nonempty (f.fiber η) := inferInstance
  rw [(f.fiberHomeo η).nonempty_congr, Set.nonempty_coe_sort] at hne
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, hx⟩

set_option backward.isDefEq.respectTransparency false in
/-- Two source opens meeting the geometrically irreducible generic fibre
have an affine common part surjecting over some neighbourhood, provided
affine generic spreading is available. -/
theorem exists_open_overlap_surjective_of_affine_spreading
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (η : Y)
    (hgeneric : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (hspread : ∀ (A : Scheme.{u}) [IsAffine A] (g : A ⟶ Y) [LocallyOfFiniteType g],
      GeometricallyIrreducible (g.fiberToSpecResidueField η) →
        ∃ V : Y.Opens, η ∈ V ∧ GeometricallyIrreducible (g ∣_ V))
    (U W : X.Opens) (hU : ∃ x : X, f x = η ∧ x ∈ U)
    (hW : ∃ x : X, f x = η ∧ x ∈ W) :
    ∃ V : Y.Opens, η ∈ V ∧ ∀ y : V, ∃ x : X,
      f x = y.1 ∧ x ∈ U ∧ x ∈ W := by
  obtain ⟨x, hxη, hxU, hxW⟩ :=
    exists_overlap_point_of_geometricallyIrreducible_fiber f η hgeneric U W hU hW
  obtain ⟨Z, hZ, hxZ, hZle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U ⊓ W) ⟨hxU, hxW⟩
  let : IsAffine Z := hZ
  have hZgeneric : GeometricallyIrreducible ((Z.ι ≫ f).fiberToSpecResidueField η) :=
    geometricallyIrreducible_fiber_comp_openImmersion Z.ι f η hgeneric ⟨⟨x, hxZ⟩, hxη⟩
  obtain ⟨V, hηV, hgeom⟩ := hspread Z (Z.ι ≫ f) hZgeneric
  refine ⟨V, hηV, fun y => ?_⟩
  let := hgeom
  obtain ⟨z, hz⟩ := ((Z.ι ≫ f) ∣_ V).surjective y
  refine ⟨z.1.1, ?_, (hZle z.1.property).1, (hZle z.1.property).2⟩
  have heq := congrArg Subtype.val hz
  simpa only [morphismRestrict_base_coe, Scheme.Hom.comp_apply,
    Scheme.Opens.ι_apply] using heq

set_option backward.isDefEq.respectTransparency false in
/-- Over an affine base, the affine spreading assertion implies the same
assertion for every quasi-compact source. -/
theorem exists_geometricallyIrreducible_restrict_of_affine_spreading
    {X Y : Scheme.{u}} [CompactSpace X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (η : Y) (hη : IsGenericPoint η univ)
    (hgeneric : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (hspread : ∀ (A : Scheme.{u}) [IsAffine A] (g : A ⟶ Y) [LocallyOfFiniteType g],
      GeometricallyIrreducible (g.fiberToSpecResidueField η) →
        ∃ V : Y.Opens, η ∈ V ∧ GeometricallyIrreducible (g ∣_ V)) :
    ∃ V : Y.Opens, η ∈ V ∧ GeometricallyIrreducible (f ∣_ V) := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  have hlocal : ∀ i : 𝒰.I₀, ∃ V : Y.Opens, η ∈ V ∧
      (η ∈ Set.range (𝒰.f i ≫ f) → GeometricallyIrreducible ((𝒰.f i ≫ f) ∣_ V)) ∧
      (η ∉ Set.range (𝒰.f i ≫ f) → (𝒰.f i ≫ f) ⁻¹ᵁ V = ⊥) := by
    intro i
    have : IsAffine (𝒰.X i) := by dsimp [𝒰]; infer_instance
    by_cases hi : η ∈ Set.range (𝒰.f i ≫ f)
    · obtain ⟨V, hV, hg⟩ := hspread (𝒰.X i) (𝒰.f i ≫ f)
        (geometricallyIrreducible_fiber_comp_openImmersion (𝒰.f i) f η hgeneric hi)
      exact ⟨V, hV, fun _ => hg, fun h => (h hi).elim⟩
    · obtain ⟨V, hV, he⟩ :=
        exists_open_preimage_eq_bot_of_affine_not_mem_range (𝒰.f i ≫ f) η hη hi
      exact ⟨V, hV, fun h => (hi h).elim, fun _ => he⟩
  choose V₀ hη₀ hgeom₀ hbad₀ using hlocal
  let G := {i : 𝒰.I₀ // η ∈ Set.range (𝒰.f i ≫ f)}
  have : Nonempty G := by
    obtain ⟨x, hx⟩ := mem_range_of_geometricallyIrreducible_fiber f η hgeneric
    obtain ⟨i, z, hz⟩ := 𝒰.exists_eq x
    exact ⟨⟨i, ⟨z, by simpa only [Scheme.Hom.comp_apply, hz] using hx⟩⟩⟩
  have hpair : ∀ i j : G, ∃ V : Y.Opens, η ∈ V ∧
      ∀ y : V, ∃ x : X, f x = y.1 ∧
        x ∈ Set.range (𝒰.f i.1) ∧ x ∈ Set.range (𝒰.f j.1) := by
    intro i j
    apply exists_open_overlap_surjective_of_affine_spreading f η hgeneric hspread
      (𝒰.f i.1).opensRange (𝒰.f j.1).opensRange
    · obtain ⟨z, hz⟩ := i.property
      exact ⟨𝒰.f i.1 z, hz, ⟨z, rfl⟩⟩
    · obtain ⟨z, hz⟩ := j.property
      exact ⟨𝒰.f j.1 z, hz, ⟨z, rfl⟩⟩
  choose V₁ hη₁ hmeet₁ using hpair
  let V : Y.Opens := (⨅ i, V₀ i) ⊓ ⨅ i, ⨅ j, V₁ i j
  have hV₀ (i : 𝒰.I₀) : V ≤ V₀ i := inf_le_left.trans (iInf_le _ i)
  have hV₁ (i j : G) : V ≤ V₁ i j :=
    inf_le_right.trans ((iInf_le _ i).trans (iInf_le _ j))
  refine ⟨V, ?_, ?_⟩
  · change η ∈ ((⨅ i, V₀ i : Y.Opens) : Set Y) ∩
      ((⨅ i, ⨅ j, V₁ i j : Y.Opens) : Set Y)
    simp only [Opens.coe_iInf, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨hη₀, hη₁⟩
  · let 𝒱 := 𝒰.restrict (f ⁻¹ᵁ V)
    apply geometricallyIrreducible_of_openImmersions
      (fun i : G => 𝒱.X i.1) (fun i : G => 𝒱.f i.1) (f ∣_ V)
    · intro x
      obtain ⟨i, z, hz⟩ := 𝒰.exists_eq x.1
      have hi : η ∈ Set.range (𝒰.f i ≫ f) := by
        by_contra h
        have hzV : z ∈ (𝒰.f i ≫ f) ⁻¹ᵁ V₀ i := by
          change f (𝒰.f i z) ∈ V₀ i
          rw [hz]
          exact hV₀ i x.property
        rw [hbad₀ i h] at hzV
        exact hzV
      refine ⟨⟨i, hi⟩, ?_⟩
      change x ∈ Set.range (𝒰.f i ∣_ f ⁻¹ᵁ V)
      exact (mem_range_morphismRestrict_iff _ _ _).mpr ⟨z, hz⟩
    · intro i
      change GeometricallyIrreducible ((𝒰.f i.1 ∣_ f ⁻¹ᵁ V) ≫ f ∣_ V)
      rw [← morphismRestrict_comp]
      exact geometricallyIrreducible_restrict_of_le _ (hV₀ i.1) (hgeom₀ i.1 i.property)
    · intro i j y
      obtain ⟨x, hxy, hxi, hxj⟩ := hmeet₁ i j ⟨y.1, hV₁ i j y.property⟩
      have hxV : x ∈ f ⁻¹ᵁ V := by
        change f x ∈ V
        rw [hxy]
        exact y.property
      refine ⟨⟨x, hxV⟩, ?_, ?_, ?_⟩
      · apply Subtype.ext
        simpa only [morphismRestrict_base_coe] using hxy
      · change (⟨x, hxV⟩ : f ⁻¹ᵁ V) ∈ Set.range (𝒰.f i.1 ∣_ f ⁻¹ᵁ V)
        exact (mem_range_morphismRestrict_iff _ _ _).mpr hxi
      · change (⟨x, hxV⟩ : f ⁻¹ᵁ V) ∈ Set.range (𝒰.f j.1 ∣_ f ⁻¹ᵁ V)
        exact (mem_range_morphismRestrict_iff _ _ _).mpr hxj

set_option backward.isDefEq.respectTransparency false in
/-- The arbitrary-scheme target follows from its assertion for affine
source and target, with the same universe and actual generic fibre. -/
theorem finiteTypeGeometricallyIrreducibleGenericSpreading_of_affine
    (hspread : ∀ (A B : Scheme.{u}) [IsAffine A] [IsAffine B]
      (g : A ⟶ B) [LocallyOfFiniteType g]
      (η : B), IsGenericPoint η univ →
        GeometricallyIrreducible (g.fiberToSpecResidueField η) →
          ∃ V : B.Opens, η ∈ V ∧ GeometricallyIrreducible (g ∣_ V)) :
    FiniteTypeGeometricallyIrreducibleGenericSpreading.{u} := by
  intro X Y f _ _ η hη hgeneric
  obtain ⟨W, hW, hηW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := η) (Opens.mem_top η)
  let : IsAffine W := hW
  let η' : W := ⟨η, hηW⟩
  have hη' : IsGenericPoint η' univ :=
    isGenericPoint_of_isInducing W.ι.isOpenEmbedding.isInducing hη
  have hgeneric' : GeometricallyIrreducible ((f ∣_ W).fiberToSpecResidueField η') :=
    geometricallyIrreducible_fiber_of_isPullback
      (isPullback_morphismRestrict f W).flip η' hgeneric
  let : CompactSpace (f ⁻¹ᵁ W).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ W)
  obtain ⟨U, hηU, hgeom⟩ :=
    exists_geometricallyIrreducible_restrict_of_affine_spreading (f ∣_ W) η' hη' hgeneric'
      (fun A _ g _ hg => hspread A W g η' hη' hg)
  refine ⟨W.ι ''ᵁ U, ⟨η', hηU, rfl⟩, ?_⟩
  exact (geometricallyIrreducible_arrowIso_iff (morphismRestrictRestrict f W U)).mp hgeom

end Langlands.AlgebraicGeometry.SchemeFiberGeometry

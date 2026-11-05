import Langlands.AlgebraicGeometry.ComponentDenseOpenGeometry
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Open-cover assembly of geometric irreducibility of actual components -/

universe u v

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {U X S T : Scheme.{u}}

/-- A component is geometrically irreducible if it meets an open subscheme
whose actual components are geometrically irreducible. -/
theorem geometricallyIrreducible_component_of_open
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (j : U ⟶ X) [IsOpenImmersion j] (C : irreducibleComponents X)
    (hmeet : (C.val ∩ Set.range j).Nonempty)
    (h : ComponentsGeometricallyIrreducible (j ≫ f)) :
    GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ :
          Closeds X)).subschemeι ≫ f) := by
  let D : irreducibleComponents U :=
    ⟨j ⁻¹' C.val,
      preimage_mem_irreducibleComponents C.property j.isOpenEmbedding hmeet⟩
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)
  let i := I.subschemeι
  let a := pullback.fst i j
  let q := pullback.snd i j
  let k := (Scheme.IdealSheafData.vanishingIdeal
    (⟨D.val, isClosed_of_mem_irreducibleComponents D.val D.property⟩ : Closeds U)).subschemeι
  have hr : Set.range q = Set.range k := by
    simp only [q, Scheme.Pullback.range_snd, k, i, I,
      Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hq : GeometricallyIrreducible (q ≫ j ≫ f) :=
    (GenericImagePattern.geometricallyIrreducible_iff_of_closedImmersion_range_eq
      (j ≫ f) q k hr).mpr (h D)
  have haGI : GeometricallyIrreducible (a ≫ i ≫ f) := by
    rw [← Category.assoc, show a ≫ i = q ≫ j from pullback.condition, Category.assoc]
    exact hq
  have hI : IrreducibleSpace I.subscheme :=
    (i.isEmbedding.toHomeomorph.trans
      (.setCongr (show Set.range i = C.val from
        Scheme.IdealSheafData.range_subschemeι I))).irreducibleSpace_iff.mpr
          (Subtype.irreducibleSpace C.property.1)
  have ha : DenseRange a := by
    change Dense (Set.range a)
    dsimp only [a]
    rw [Scheme.Pullback.range_fst]
    apply ((IsOpenImmersion.isOpen_range j).preimage i.continuous).dense
    obtain ⟨x, hxC, hxj⟩ := hmeet
    have hx : x ∈ Set.range i := by
      rw [show Set.range i = C.val from Scheme.IdealSheafData.range_subschemeι I]
      exact hxC
    obtain ⟨z, rfl⟩ := hx
    exact ⟨z, hxj⟩
  exact geometricallyIrreducible_of_dense_open a (i ≫ f) ha

/-- Geometric irreducibility of all actual components assembles over any open cover. -/
theorem ComponentsGeometricallyIrreducible.of_openCover
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K)) (𝒰 : Scheme.OpenCover.{v} X)
    (h : ∀ i, ComponentsGeometricallyIrreducible (𝒰.f i ≫ f)) :
    ComponentsGeometricallyIrreducible f := by
  intro C
  let x := (genericPoints.ofComponent C).1
  exact geometricallyIrreducible_component_of_open f (𝒰.f (𝒰.idx x)) C
    ⟨x, (genericPoints.isGenericPoint_ofComponent C).mem, 𝒰.covers x⟩ (h _)

/-- The scalar extension of a chart is the corresponding chart of the
pulled-back open cover. -/
noncomputable def openCoverBaseChangeIso (f : X ⟶ S) (e : T ⟶ S)
    (𝒰 : Scheme.OpenCover.{v} X) (i : 𝒰.I₀) :
    pullback (𝒰.f i ≫ f) e ≅ (𝒰.pullback₁ (pullback.fst f e)).X i :=
  (pullbackRightPullbackFstIso f e (𝒰.f i)).symm ≪≫
    pullbackSymmetry (𝒰.f i) (pullback.fst f e)

@[reassoc (attr := simp)]
theorem openCoverBaseChangeIso_hom_f_snd (f : X ⟶ S) (e : T ⟶ S)
    (𝒰 : Scheme.OpenCover.{v} X) (i : 𝒰.I₀) :
    (openCoverBaseChangeIso f e 𝒰 i).hom ≫
        (𝒰.pullback₁ (pullback.fst f e)).f i ≫ pullback.snd f e =
      pullback.snd (𝒰.f i ≫ f) e := by
  change ((pullbackRightPullbackFstIso f e (𝒰.f i)).inv ≫
    (pullbackSymmetry (𝒰.f i) (pullback.fst f e)).hom) ≫
      pullback.fst (pullback.fst f e) (𝒰.f i) ≫ pullback.snd f e = _
  simp

/-- Splitting each scalar-extended member of an open cover splits the ambient
scalar extension. -/
theorem ComponentsGeometricallyIrreducible.of_openCover_baseChange
    {L : Type u} [Field L] (f : X ⟶ S) (e : Spec (.of L) ⟶ S)
    (𝒰 : Scheme.OpenCover.{v} X)
    (h : ∀ i, ComponentsGeometricallyIrreducible (pullback.snd (𝒰.f i ≫ f) e)) :
    ComponentsGeometricallyIrreducible (pullback.snd f e) := by
  apply ComponentsGeometricallyIrreducible.of_openCover (pullback.snd f e)
    (𝒰.pullback₁ (pullback.fst f e))
  intro i
  exact (h i).of_iso (openCoverBaseChangeIso f e 𝒰 i)
    (openCoverBaseChangeIso_hom_f_snd f e 𝒰 i)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry

import Langlands.AlgebraicGeometry.ComponentOpenDimension
import Langlands.AlgebraicGeometry.AffineOpenDimension
import Langlands.AlgebraicGeometry.AffineSchemeScalarExtension

/-! # Dimension on opens of components of locally finite-type field schemes -/

universe u v w

open Set Topology TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Every nonempty open retains the dimension of the actual ambient space. -/
def OpenDimensionInvariant (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ U : Opens X, (U : Set X).Nonempty →
    topologicalKrullDim U = topologicalKrullDim X

/-- Every irreducible component has dimension invariant on its nonempty opens. -/
def ComponentOpenDimensionInvariant (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ Z : Set X, Z ∈ irreducibleComponents X → OpenDimensionInvariant Z

theorem OpenDimensionInvariant.of_homeomorph
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h : OpenDimensionInvariant X) (e : X ≃ₜ Y) :
    OpenDimensionInvariant Y := by
  intro U hU
  let V : Opens X := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
  have hV : (V : Set X).Nonempty := by
    obtain ⟨x, hx⟩ := hU
    exact ⟨e.symm x, by simpa [V] using hx⟩
  let eU : V ≃ₜ U := e.subtype (fun _ => Iff.rfl)
  exact (eU.isHomeomorph.topologicalKrullDim_eq _).symm.trans
    ((h V hV).trans (e.isHomeomorph.topologicalKrullDim_eq _))

theorem ComponentOpenDimensionInvariant.of_homeomorph
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h : ComponentOpenDimensionInvariant X) (e : X ≃ₜ Y) :
    ComponentOpenDimensionInvariant Y := by
  intro Z hZ
  have hpre : e ⁻¹' Z ∈ irreducibleComponents X :=
    preimage_mem_irreducibleComponents hZ e.isOpenEmbedding
      (by simpa only [e.surjective.range_eq, inter_univ] using hZ.1.1)
  let eZ : (e ⁻¹' Z) ≃ₜ Z := (e.image (e ⁻¹' Z)).trans
    (Homeomorph.setCongr (image_preimage_eq Z e.surjective))
  exact (h _ hpre).of_homeomorph eZ

/-- The component property follows from the same property on an actual open cover. -/
theorem ComponentOpenDimensionInvariant.of_openCover
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hU : ∀ i, ComponentOpenDimensionInvariant (U i)) :
    ComponentOpenDimensionInvariant X := by
  intro Z hZ
  let : IrreducibleSpace Z := Subtype.irreducibleSpace hZ.1
  apply topologicalKrullDim_open_eq_of_openCover (fun i => openInSubspace Z (U i))
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, hi⟩
  · intro i W hW
    have hmeet : (Z ∩ range (Subtype.val : U i → X)).Nonempty := by
      obtain ⟨x, hx⟩ := hW
      exact ⟨x.1.1, x.1.2, ⟨⟨x.1.1, x.2⟩, rfl⟩⟩
    have hpre := preimage_mem_irreducibleComponents hZ (U i).isOpenEmbedding' hmeet
    exact ((hU i _ hpre).of_homeomorph
      (subtypePreimageCommHomeomorph Z (U i : Set X)).symm) W hW

/-- A component of a finite-type field-algebra spectrum retains its dimension
on every nonempty open, without a reducedness or domain hypothesis on the algebra. -/
theorem componentOpenDimensionInvariant_spec_finiteType
    (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ComponentOpenDimensionInvariant (PrimeSpectrum A) := by
  intro Z hZ
  rw [← PrimeSpectrum.zeroLocus_minimalPrimes A] at hZ
  obtain ⟨p, hp, rfl⟩ := hZ
  let : p.IsPrime := hp.1.1
  intro U hU
  exact (topologicalKrullDim_open_primeZeroLocus k A p U hU).trans
    (topologicalKrullDim_zeroLocus p).symm

/-- The comparison on an affine scheme uses the algebra induced by its actual
structure morphism and the canonical global-section spectrum isomorphism. -/
theorem componentOpenDimensionInvariant_affine
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    ComponentOpenDimensionInvariant X := by
  let : Algebra k Γ(X, ⊤) := (affineStructureMap f).hom.toAlgebra
  let : Algebra.FiniteType k Γ(X, ⊤) := affineStructureMap_finiteType f
  exact (componentOpenDimensionInvariant_spec_finiteType k Γ(X, ⊤)).of_homeomorph
    X.isoSpec.inv.homeomorph

/-- Arbitrary locally finite-type schemes over a field have the component
property; no quasi-compactness or separation hypothesis is imposed. -/
theorem componentOpenDimensionInvariant_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    ComponentOpenDimensionInvariant X := by
  apply ComponentOpenDimensionInvariant.of_openCover
    (fun U : X.affineOpens => (U.1 : Opens X))
  · intro x
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨⟨U, hU⟩, hxU⟩
  · intro U
    exact componentOpenDimensionInvariant_affine k U.1.toScheme (U.1.ι ≫ f)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry

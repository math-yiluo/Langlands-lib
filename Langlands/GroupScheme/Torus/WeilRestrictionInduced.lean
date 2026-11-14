import Langlands.GroupScheme.Torus.Induced
import Langlands.GroupScheme.Torus.WeilRestrictionSeparable
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.StdBasis

/-! # Finite-separable Weil restrictions are induced tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Algebra.SeparableTensor

namespace Langlands.GroupScheme.WeilGm

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [FiniteDimensional k K] [Algebra.IsSeparable k K]
  (hsplit : ∀ x : K, ((minpoly k x).map (algebraMap k Ω)).Splits)

/-- The canonical embedding basis of the actual character lattice of a finite-separable
Weil restriction over a splitting field. -/
def separableEmbeddingCharacterBasis :
    Module.Basis (K →ₐ[k] Ω) ℤ
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj
        (commGroupScheme (CommRingCat.of k) K))) :=
  (Pi.basisFun ℤ (K →ₐ[k] Ω)).map
    (separableEmbeddingCharacterEquiv k K Ω hsplit).symm.toIntLinearEquiv

/-- A coefficient automorphism permutes the embedding basis by postcomposition. -/
theorem separableEmbeddingCharacterBasis_galoisRepresentation (σ : Ω ≃ₐ[k] Ω)
    (τ : K →ₐ[k] Ω) :
    characterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ
        (separableEmbeddingCharacterBasis k K Ω hsplit τ) =
      separableEmbeddingCharacterBasis k K Ω hsplit (embeddingPermutation k K Ω σ τ) := by
  classical
  apply (separableEmbeddingCharacterEquiv k K Ω hsplit).injective
  rw [separableEmbeddingCharacterEquiv_galoisRepresentation]
  simp only [separableEmbeddingCharacterBasis, Module.Basis.map_apply,
    AddEquiv.coe_toIntLinearEquiv, AddEquiv.apply_symm_apply]
  ext υ
  change (Pi.basisFun ℤ (K →ₐ[k] Ω) τ) ((embeddingPermutation k K Ω σ).symm υ) =
    (Pi.basisFun ℤ (K →ₐ[k] Ω) (embeddingPermutation k K Ω σ τ)) υ
  simp only [Pi.basisFun_apply, Pi.single_apply]
  congr 1
  exact propext (embeddingPermutation k K Ω σ).symm_apply_eq

include hsplit in
/-- Over a finite Galois field splitting the minimal polynomials, the embedding basis
witnesses the induced-torus predicate. -/
theorem isInducedTorus_of_separable_splitting
    [FiniteDimensional k Ω] [IsGalois k Ω] :
    IsInducedTorus (commGroupScheme (CommRingCat.of k) K) := by
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨K →ₐ[k] Ω, inferInstance, ⟨separableEmbeddingIso k K Ω hsplit⟩⟩,
    K →ₐ[k] Ω, separableEmbeddingCharacterBasis k K Ω hsplit, ?_⟩
  intro σ τ
  exact ⟨embeddingPermutation k K Ω σ τ,
    separableEmbeddingCharacterBasis_galoisRepresentation k K Ω hsplit σ τ⟩

/-- The Weil restriction of the multiplicative group through a finite separable field
extension is an induced torus. -/
theorem isInducedTorus_of_finite_separable :
    IsInducedTorus (commGroupScheme (CommRingCat.of k) K) := by
  let f : K →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra K (SeparableClosure k) := f.toRingHom.toAlgebra
  let : IsScalarTower k K (SeparableClosure k) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Nonempty (K →ₐ[k] SeparableClosure k) := ⟨f⟩
  let E := IntermediateField.normalClosure k K (SeparableClosure k)
  exact isInducedTorus_of_separable_splitting k K E
    (fun x => IsNormalClosure.splits (F := k) (K := K) (L := E) x)

end Langlands.GroupScheme.WeilGm

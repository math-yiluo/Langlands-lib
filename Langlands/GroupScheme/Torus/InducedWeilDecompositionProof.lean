import Langlands.GroupScheme.Torus.InducedWeilDecompositionStatement
import Langlands.GroupScheme.Torus.InducedBasisTransport
import Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent
import Langlands.GroupScheme.Torus.WeilRestrictionProductCharacters
import Langlands.Algebra.FiniteGaloisOrbits
import Langlands.Algebra.PermutationBasisCoordinates

/-! # Induced tori as Weil restrictions from intermediate-field products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.PermutationBasis

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- An induced torus has a Weil-restriction presentation over any prescribed
finite Galois splitting field, including the rank-zero case. -/
theorem inducedTorusWeilDecomposition : InducedTorusWeilDecompositionStatement.{u} := by
  classical
  intro k _ L _ _ _ _ T hL hT
  obtain ⟨I, hI, b, hb⟩ := hT.exists_permuted_basis L hL
  let : Finite I := hI
  let ρ := characterLattice.galoisRepresentation k L T
  let : MulAction (L ≃ₐ[k] L) I := MulAction.compHom I (indexAction ρ b hb)
  obtain ⟨n, E, e, he⟩ :=
    Langlands.Algebra.FiniteGaloisOrbits.exists_finite_fields k L (I := I)
  let q : ULift.{u} (Fin n) ≃ Fin n := Equiv.ulift
  let E' : ULift.{u} (Fin n) → IntermediateField k L := fun i => E (q i)
  let e' : (Σ i, E' i →ₐ[k] L) ≃ I :=
    (Equiv.sigmaCongrLeft (β := fun i => E i →ₐ[k] L) q).trans e
  let c := coordinateEquiv b e'
  let f := (WeilGm.productEmbeddingCharacterEquiv k L E').trans c.toAddEquiv
  have hf (σ : L ≃ₐ[k] L)
      (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj
        (WeilGm.commGroupScheme (CommRingCat.of k) (∀ i, E' i)))) :
      f (characterLattice.galoisRepresentation k L
          (WeilGm.commGroupScheme (CommRingCat.of k) (∀ i, E' i)) σ χ) =
        characterLattice.galoisRepresentation k L T σ (f χ) := by
    change c (WeilGm.productEmbeddingCharacterEquiv k L E'
      (characterLattice.galoisRepresentation k L
        (WeilGm.commGroupScheme (CommRingCat.of k) (∀ i, E' i)) σ χ)) =
      ρ σ (c (WeilGm.productEmbeddingCharacterEquiv k L E' χ))
    rw [WeilGm.productEmbeddingCharacterEquiv_galoisRepresentation]
    exact coordinateEquiv_equivariant_of_permuted ρ b hb e'
      (WeilGm.productEmbeddingPermutationHom k L E')
      (fun g j => he g (q j.1) j.2) σ
      (WeilGm.productEmbeddingCharacterEquiv k L E' χ)
  have hW : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj
        (WeilGm.commGroupScheme (CommRingCat.of k) (∀ i, E' i))).toGrp := by
    exact ⟨(Σ i, E' i →ₐ[k] L), inferInstance,
      ⟨WeilGm.decompositionIso (CommRingCat.of k) (CommRingCat.of L) (∀ i, E' i)
        (Σ i, E' i →ₐ[k] L) (WeilGm.productEmbeddingDecomposition k L E')⟩⟩
  obtain ⟨a, _⟩ := hL.exists_iso_of_equivariant_characterEquiv hW f hf
  let p : (∀ i, E' i) ≃ₐ[k] (∀ i, E i) :=
    AlgEquiv.piCongrLeft k (fun i => E i) q
  exact ⟨n, E, ⟨a ≪≫ WeilGm.commCongrIso p⟩⟩

end Langlands.GroupScheme

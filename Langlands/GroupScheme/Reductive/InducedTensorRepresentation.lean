import Langlands.GroupScheme.Reductive.PiTensorWeights
import Langlands.GroupScheme.Reductive.GaloisTwistWeights

/-! # Tensor products of Galois conjugates of a representation and their induced intertwiners -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.Algebra.KroneckerInduction

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem galoisTensor_mul_apply (R : Type u) [CommRing R] [Algebra k R] (g g' : K ≃ₐ[k] K)
    (z : K ⊗[k] R) : galoisTensor R (g * g') z = galoisTensor R g (galoisTensor R g' z) := by
  have h : galoisTensor R (g * g') = (galoisTensor R g).comp (galoisTensor R g') :=
    Algebra.TensorProduct.ext' fun _ _ => rfl
  exact DFunLike.congr_fun h z

variable [IsAffineHom G.X.hom]

/-- The universal matrix of a tensor product of a family is the Kronecker product of the
universal matrices. -/
theorem universalMatrix_piTensor {m : ℕ}
    (ρ : Fin (m + 1) → MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n) :
    universalMatrix (piTensor ρ) = piKronecker fun i => universalMatrix (ρ i) :=
  piTensor_affineMatrix ρ _ _


/-- **Induced intertwiners of tensor products of conjugates.** Let `Q h : ρ → ρ^h` intertwine
for every `h ∈ Gal(K/E)`, and let `I` be induction data from `Gal(K/E)` to `Gal(K/k)` on
`Fin (m + 1)`. Then the induced matrix of `τ ∈ Gal(K/k)` intertwines the tensor product
`Π = ⨂_i ρ^{ext i}` of the conjugates of `ρ` with its twist `Π^τ`. -/
theorem intertwines_galoisTwist_piTensor {E : Type u} [Field E] [Algebra k E] [Algebra E K]
    [IsScalarTower k E K] {m : ℕ} (I : InductionData k E K (Fin (m + 1)))
    (Q : (K ≃ₐ[E] K) → Matrix n n K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (hQ : ∀ h : K ≃ₐ[E] K, ρ.Intertwines (galoisTwist (h.restrictScalars k) ρ) (Q h))
    (τ : K ≃ₐ[k] K) :
    (piTensor fun i => galoisTwist (I.ext i) ρ).Intertwines
      (galoisTwist τ (piTensor fun i => galoisTwist (I.ext i) ρ)) (inducedMatrix I Q τ) := by
  rw [intertwines_iff_universalMatrix, universalMatrix_galoisTwist, universalMatrix_piTensor]
  simp only [universalMatrix_galoisTwist]
  exact inducedMatrix_mul_piKronecker I Q
    (fun g => (galoisTensor (CharacterUnits.Coord G) g).toRingHom)
    (fun g g' x => galoisTensor_mul_apply _ g g' x) (fun g c => rfl)
    (fun _ => universalMatrix ρ)
    (fun _ h => by
      have := (intertwines_iff_universalMatrix _ _ _).mp (hQ h)
      rw [universalMatrix_galoisTwist] at this
      exact this) τ

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G) {n : Type} [Fintype n] [DecidableEq n]

/-- The Galois twist by `σ` of a representation with top weight `lam` has top weight `σ ⋆ lam`
(the star action). -/
theorem hasTopWeight_galoisTwist (σ : K ≃ₐ[k] K)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {lam : characterLattice d.toSplitPinning.torus} (hρ : d.toSplitPinning.HasTopWeight ρ lam) :
    d.toSplitPinning.HasTopWeight (galoisTwist σ ρ) ((d.starAction σ).val • lam) := by
  obtain ⟨w, hw⟩ := d.exists_weyl_mul_galoisAction_eq_starAction σ
  have hstar : ∀ mu : characterLattice d.toSplitPinning.torus,
      (d.starAction σ).val • mu = w.val • (d.galoisAction σ • mu) := by
    intro mu
    rw [← hw, mul_smul]
  refine ⟨?_, fun mu hmu => ?_⟩
  · rw [hstar, d.finrank_representationWeightSpace_weyl _ w.val w.2,
      representationWeightSpace_galoisTwist_smul, finrank_galoisComap, hρ.1]
  · let nu : characterLattice d.toSplitPinning.torus := (d.galoisAction σ)⁻¹ • (w.val⁻¹ • mu)
    have hgnu : d.galoisAction σ • nu = w.val⁻¹ • mu := smul_inv_smul _ _
    have hnu : d.toSplitPinning.representationWeightSpace ρ nu ≠ ⊥ := by
      rw [Ne, ← Submodule.finrank_eq_zero] at hmu ⊢
      have h1 := d.finrank_representationWeightSpace_weyl (galoisTwist σ ρ) w.val⁻¹
        (inv_mem w.2) mu
      rw [← hgnu, representationWeightSpace_galoisTwist_smul, finrank_galoisComap] at h1
      rw [h1]
      exact hmu
    have h2 := d.smul_mem_positiveRootMonoid (d.starAction σ).val (d.starAction σ).2 (hρ.2 nu hnu)
    rw [smul_sub, hstar nu, hgnu, smul_inv_smul] at h2
    exact h2

end Langlands.GroupScheme.GaloisPinningData

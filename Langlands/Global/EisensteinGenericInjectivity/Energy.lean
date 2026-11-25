import Langlands.Global.EisensteinGenericInjectivity.PlaceHeight
import Langlands.GroupScheme.MatrixRepresentationDenseCompact

/-! # Invariant archimedean energies from an invariant positive definite Hermitian form -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Matrix ComplexOrder

set_option autoImplicit false

namespace Langlands.Global.EisensteinGenericInjectivity

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} {N : ℕ}

theorem continuous_placeMatrix (σ : MatrixRepresentation G (Fin N)) (w : InfinitePlace F) :
    Continuous (placeMatrix σ w) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact (continuous_placeHom w).comp
    ((Units.continuous_val.comp (adelicMatrix F G σ).continuous).matrix_elem a b)

/-- A positive invariant energy given by a real quadratic expression. -/
structure IsQuadraticEnergy (σ : MatrixRepresentation G (Fin N)) (w : InfinitePlace F)
    (K : Subgroup (AdelicGroupPoints F G)) (Q : (Fin N → ℂ) → ℝ)
    (B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ) : Prop extends IsInvariantEnergy σ w K Q where
  expand : ∀ (n : ℕ) (a : Fin n → ℝ) (y : Fin n → Fin N → ℂ),
    Q (∑ r, (a r : ℂ) • y r) = ∑ r, ∑ s, a r * a s * B (y r) (y s)

variable [IsAffine G.X.left]

/-- **Invariant energies.** At each infinite place, a compact subgroup of `G(𝔸)` preserves a
positive quadratic energy: the Hermitian form `z ↦ Re (z* J z)` of a positive definite matrix
`J` invariant under the image of the subgroup in `GL N ℂ`, as given by
`DenseCompactForm.exists_posDef_invariant` (the Haar average of the pulled-back standard
Hermitian form). -/
theorem exists_quadraticEnergy (σ : MatrixRepresentation G (Fin N)) (w : InfinitePlace F)
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsCompact (K : Set (AdelicGroupPoints F G))) :
    ∃ (Q : (Fin N → ℂ) → ℝ) (B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ),
      IsQuadraticEnergy σ w K Q B := by
  let ρ : AdelicGroupPoints F G →* GL (Fin N) ℂ :=
    (Matrix.GeneralLinearGroup.map (placeHom w)).comp (adelicMatrix F G σ).toMonoidHom
  have hρ : ∀ x, ((ρ x : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = placeMatrix σ w x :=
    fun x => rfl
  have hρc : Continuous ρ := by
    refine Units.continuous_iff.mpr ⟨continuous_placeMatrix σ w, ?_⟩
    have h : (fun x => (((ρ x)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) =
        fun x => placeMatrix σ w x⁻¹ := by
      funext x
      rw [← map_inv, hρ]
    rw [h]
    exact (continuous_placeMatrix σ w).comp continuous_inv
  have hK₀ : IsCompact ((K.map ρ : Subgroup (GL (Fin N) ℂ)) : Set (GL (Fin N) ℂ)) := by
    rw [Subgroup.coe_map]
    exact hK.image hρc
  obtain ⟨J, hJ, hJK⟩ := Langlands.Group.DenseCompactForm.exists_posDef_invariant (K.map ρ) hK₀
  let H : (Fin N → ℂ) → (Fin N → ℂ) → ℂ := fun y y' =>
    star y' ⬝ᵥ ((J : Matrix (Fin N) (Fin N) ℂ) *ᵥ y)
  refine ⟨fun z => (H z z).re, fun y y' => (H y y').re, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · intro z hz
    exact (Complex.pos_iff.mp (hJ.dotProduct_mulVec_pos hz)).1
  · intro c z
    have h : H (c • z) (c • z) = ((‖c‖ ^ 2 : ℝ) : ℂ) * H z z := by
      simp only [H, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        RCLike.star_def, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [h, Complex.re_ofReal_mul]
  · intro k hk z
    have h := congrArg Units.val (hJK (ρ k) ⟨k, hk, rfl⟩)
    simp only [Units.val_mul, Units.coe_star, hρ] at h
    rw [Matrix.star_eq_conjTranspose] at h
    simp only [H]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, h]
  · intro n a y
    have h : H (∑ r, (a r : ℂ) • y r) (∑ r, (a r : ℂ) • y r) =
        ∑ r, ∑ s, ((a r * a s : ℝ) : ℂ) * H (y r) (y s) := by
      simp only [H, Matrix.mulVec_sum, Matrix.mulVec_smul, star_sum, star_smul, sum_dotProduct,
        dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def,
        Complex.conj_ofReal, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      push_cast
      ring
    simp only [h, Complex.re_sum, Complex.re_ofReal_mul]

end Langlands.Global.EisensteinGenericInjectivity

import Langlands.LocalFactor.Inductive.Statement

/-!
# Gallagher's determinant formula for actual finite-index induction

Worker 1767 proves the published `GallagherDeterminantStatement` by inverse
left-coset coordinates on the existing coinduced space. The subgroup factors
match Mathlib's transfer, and scalar basis coordinates give the determinant
power for the coset permutation. This is an algebraic proof of Deligne 1973,
Proposition 1.2, preserving the statement's independent universes.
-/

noncomputable section

universe uK uG uV

namespace Langlands.LocalFactor.Inductive

namespace Gallagher

variable {K : Type uK} [Field K]
variable {V : Type uV} [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {ι : Type uG} [Fintype ι]

/-- Write each value in a finite basis, then transpose the two function indices. -/
def scalarCoordinates : (ι → V) ≃ₗ[K] (Fin (Module.finrank K V) → ι → K) where
  toFun v j i := (Module.finBasis K V).equivFun (v i) j
  invFun v i := (Module.finBasis K V).equivFun.symm (fun j => v j i)
  left_inv v := by
    funext i
    exact (Module.finBasis K V).equivFun.symm_apply_apply (v i)
  right_inv v := by
    funext j i
    exact congrFun ((Module.finBasis K V).equivFun.apply_symm_apply (fun j => v j i)) j
  map_add' v w := by
    funext j i
    simp only [Pi.add_apply, map_add]
  map_smul' c v := by
    funext j i
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]

/-- Repeating a scalar permutation on each basis coordinate raises its determinant
to the dimension, including dimension zero. -/
theorem det_funLeft (p : ι ≃ ι) :
    LinearMap.det (LinearMap.funLeft K V p) =
      LinearMap.det (LinearMap.funLeft K K p) ^ Module.finrank K V := by
  let e := scalarCoordinates (K := K) (V := V) (ι := ι)
  have hc : e.toLinearMap ∘ₗ LinearMap.funLeft K V p ∘ₗ e.symm.toLinearMap =
      LinearMap.pi (fun j : Fin (Module.finrank K V) =>
        (LinearMap.funLeft K K p).comp (LinearMap.proj j)) := by
    apply LinearMap.ext
    intro v
    funext j i
    exact congrFun ((Module.finBasis K V).equivFun.apply_symm_apply (fun j => v j (p i))) j
  rw [← LinearMap.det_conj (LinearMap.funLeft K V p) e, hc, LinearMap.det_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

open FiniteRepresentation

variable {G : Type uG} [Group G] (H : Subgroup G)

/-- The left coset of the inverse of an element. -/
def inverseCoset (g : G) : G ⧸ H := QuotientGroup.mk g⁻¹

/-- The subgroup component relative to inverse left-coset representatives. -/
def leftFactor (g : G) : H :=
  ⟨g * (inverseCoset H g).out, by
    have h := H.inv_mem (QuotientGroup.leftRel_apply.mp
      (Quotient.exact (inverseCoset H g).out_eq))
    simpa only [inverseCoset, mul_inv_rev, inv_inv] using h⟩

theorem inverseCoset_mul (s : H) (g : G) :
    inverseCoset H ((s : G) * g) = inverseCoset H g := by
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  simpa only [mul_inv_rev, inv_mul_cancel_left, inv_inv, mul_assoc, mul_inv_cancel,
    mul_one] using s.property

theorem leftFactor_mul (s : H) (g : G) :
    leftFactor H ((s : G) * g) = s * leftFactor H g := by
  apply Subtype.ext
  simp only [leftFactor, inverseCoset_mul, Subgroup.coe_mul, mul_assoc]

theorem inverseCoset_out_inv (q : G ⧸ H) :
    inverseCoset H q.out⁻¹ = q := by
  simpa only [inverseCoset, inv_inv] using q.out_eq

/-- Coordinates on the actual coinduced space, evaluated on inverse left-coset
representatives, chosen to agree termwise with transfer. -/
def leftCoordinates (A : FiniteRepresentation.{uK, uG, uV} K H) :
    Representation.coindV H.subtype A.representation ≃ₗ[K] (G ⧸ H → A) where
  toFun f q := f.val q.out⁻¹
  invFun v := ⟨fun g => A.representation (leftFactor H g) (v (inverseCoset H g)), by
    intro s g
    simp only [Subgroup.coe_subtype, inverseCoset_mul, leftFactor_mul, map_mul]
    rfl⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    have hf := f.property (leftFactor H g) (inverseCoset H g).out⁻¹
    simpa only [Subgroup.coe_subtype, leftFactor, mul_inv_cancel_right] using hf.symm
  right_inv v := by
    funext q
    simp only [inverseCoset_out_inv]
    have h : leftFactor H q.out⁻¹ = 1 := by
      apply Subtype.ext
      simp only [leftFactor, inverseCoset_out_inv, inv_mul_cancel, Subgroup.coe_one]
    simp only [h, map_one, Module.End.one_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem inverseCoset_out_inv_mul (q : G ⧸ H) (g : G) :
    inverseCoset H (q.out⁻¹ * g) = g⁻¹ • q := by
  simp only [inverseCoset, mul_inv_rev, inv_inv]
  exact MulAction.Quotient.coe_smul_out H g⁻¹ q

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable [H.FiniteIndex]

/-- The product of the subgroup factors is Mathlib's transfer, with its actual
left-transversal convention. -/
theorem transfer_leftFactors (φ : H →* Kˣ) (g : G) :
    φ.transfer g = ∏ q : G ⧸ H, φ (leftFactor H (q.out⁻¹ * g)) := by
  classical
  rw [MonoidHom.transfer_def φ (default : H.LeftTransversal) g]
  unfold Subgroup.leftTransversals.diff
  apply Finset.prod_congr rfl
  intro q _
  congr 1
  apply Subtype.ext
  change (↑((default : H.LeftTransversal).2.leftQuotientEquiv q) : G)⁻¹ *
    ↑((g • (default : H.LeftTransversal)).2.leftQuotientEquiv q) = _
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul]
  have hout (r : G ⧸ H) :
      (↑((default : H.LeftTransversal).2.leftQuotientEquiv r) : G) = r.out :=
    Subgroup.IsComplement.leftQuotientEquiv_apply Quotient.out_eq' r
  rw [hout, hout]
  change q.out⁻¹ * (g * (g⁻¹ • q).out) =
    (leftFactor H (q.out⁻¹ * g) : G)
  simp only [leftFactor, inverseCoset_out_inv_mul, mul_assoc]

/-- In coset coordinates the action is the product of a diagonal block action
and the inverse left-coset permutation. -/
theorem det_induce (A : FiniteRepresentation.{uK, uG, uV} K H) (g : G) :
    LinearMap.det ((induce H A).representation g) =
      LinearMap.det (LinearMap.funLeft K K
        (MulAction.toPerm g⁻¹ : Equiv.Perm (G ⧸ H))) ^ A.rank *
      ∏ q : G ⧸ H, LinearMap.det (A.representation (leftFactor H (q.out⁻¹ * g))) := by
  let e : (induce H A) ≃ₗ[K] (G ⧸ H → A) := leftCoordinates H A
  have hc : e.toLinearMap ∘ₗ (induce H A).representation g ∘ₗ e.symm.toLinearMap =
      (LinearMap.pi (fun q : G ⧸ H =>
        (A.representation (leftFactor H (q.out⁻¹ * g))).comp (LinearMap.proj q))).comp
        (LinearMap.funLeft K A (MulAction.toPerm g⁻¹ : Equiv.Perm (G ⧸ H))) := by
    apply LinearMap.ext
    intro v
    funext q
    change A.representation (leftFactor H (q.out⁻¹ * g))
        (v (inverseCoset H (q.out⁻¹ * g))) =
      A.representation (leftFactor H (q.out⁻¹ * g)) (v (g⁻¹ • q))
    rw [inverseCoset_out_inv_mul]
  rw [← LinearMap.det_conj ((induce H A).representation g) e, hc,
    LinearMap.det_comp, LinearMap.det_pi, det_funLeft]
  exact mul_comm _ _

/-- For the trivial line the block action is the identity, leaving exactly the
scalar coset permutation determinant. -/
theorem det_induce_trivial (g : G) :
    LinearMap.det ((induce H (of (Representation.trivial K H K))).representation g) =
      LinearMap.det (LinearMap.funLeft K K
        (MulAction.toPerm g⁻¹ : Equiv.Perm (G ⧸ H))) := by
  rw [det_induce]
  change LinearMap.det (LinearMap.funLeft K K
      (MulAction.toPerm g⁻¹ : Equiv.Perm (G ⧸ H))) ^ Module.finrank K K *
    (∏ _q : G ⧸ H, LinearMap.det (1 : Module.End K K)) = _
  simp only [Module.finrank_self, pow_one, map_one, Finset.prod_const_one, mul_one]

end Gallagher

/-- Gallagher's determinant-transfer formula for the actual finite-index induced
representation, with independent field, group and carrier universes. -/
theorem gallagherDeterminant : GallagherDeterminantStatement.{uK, uG, uV} := by
  intro K _ G _ H _ A
  let := H.fintypeQuotientOfFiniteIndex
  ext g
  change LinearMap.det ((FiniteRepresentation.induce H A).representation g) =
    LinearMap.det ((FiniteRepresentation.induce H
      (FiniteRepresentation.of (Representation.trivial K H K))).representation g) ^ A.rank *
      ((FiniteRepresentation.determinantCharacter A).transfer g : K)
  rw [Gallagher.det_induce, Gallagher.det_induce_trivial, Gallagher.transfer_leftFactors]
  simp only [Units.coe_prod, FiniteRepresentation.determinantCharacter_apply]

end Langlands.LocalFactor.Inductive

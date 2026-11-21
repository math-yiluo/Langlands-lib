import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.BaseChange.TwistedCharacter
import Langlands.Representation.Conductor.RankOneCharacterLevel
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Norm pullback for rank-one Shintani lifts

The character of a rank-one Shintani lift is the norm pullback of the
base character. The algebraic norm is the cyclic matrix norm in rank one.
-/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear JacquetLanglands RankinSelberg
open scoped BigOperators

universe u v uV uW

section Norm

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {l : ℕ}

/-- For a cyclic field extension the algebra norm is the product of the powers
of the given generator. -/
theorem IsCyclicAlgebra.norm_eq_prod_powers (h : IsCyclicAlgebra σ l) (x : E) :
    algebraMap F E (Algebra.norm F x) = ∏ i ∈ Finset.range l, (σ ^ i) x := by
  classical
  let : Module.Finite F E := h.1
  let : IsGalois F E := h.isGalois
  let p (i : Fin l) : E ≃ₐ[F] E := σ ^ (i : ℕ)
  have hp : Function.Bijective p := by
    apply (Fintype.bijective_iff_injective_and_card p).mpr
    constructor
    · intro i j hij
      have hi : (i : ℕ) < orderOf σ := h.2.2.2.1.symm ▸ i.isLt
      have hj : (j : ℕ) < orderOf σ := h.2.2.2.1.symm ▸ j.isLt
      exact Fin.ext (pow_injOn_Iio_orderOf hi hj hij)
    · calc
        Fintype.card (Fin l) = l := Fintype.card_fin l
        _ = Module.finrank F E := h.2.1.symm
        _ = Nat.card (E ≃ₐ[F] E) := (IsGalois.card_aut_eq_finrank F E).symm
        _ = Fintype.card (E ≃ₐ[F] E) := Nat.card_eq_fintype_card
  rw [Algebra.norm_eq_prod_automorphisms, Finset.prod_range]
  exact (Fintype.prod_equiv (Equiv.ofBijective p hp) _ _ (fun _ => rfl)).symm

private theorem det_cyclicNorm_scalar (σ : E ≃ₐ[F] E) (l : ℕ) (x : Eˣ) :
    (determinant (cyclicNorm σ l (scalar (n := 1) x)) : E) =
      ∏ i ∈ Finset.range l, (σ ^ i) (x : E) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [cyclicNorm_succ, map_mul, Units.val_mul, ih, Finset.prod_range_succ]
    congr 1
    change ((entrywiseAut (σ ^ l) 1 (scalar x) : GeneralLinear 1 E) :
      Matrix (Fin 1) (Fin 1) E).det = _
    rw [Matrix.det_fin_one, entrywiseAut_apply_apply]
    simp [Matrix.GeneralLinearGroup.coe_scalar]

/-- The rank-one matrix given by a unit is associated with the unit's field norm. -/
theorem IsCyclicAlgebra.isNormAssociated_rankOne (h : IsCyclicAlgebra σ l) (x : Eˣ) :
    IsNormAssociated σ l (scalar (n := 1) x)
      (scalar (n := 1) (Units.map (Algebra.norm F) x)) := by
  refine ⟨1, ?_⟩
  simp only [inv_one, one_mul, mul_one]
  have hinj : Function.Injective (determinant (n := 1) (R := E)) := fun a b hab =>
    (scalar_determinant_rankOne a).symm.trans ((congrArg scalar hab).trans
      (scalar_determinant_rankOne b))
  apply hinj
  apply Units.ext
  rw [det_cyclicNorm_scalar, ← h.norm_eq_prod_powers]
  change algebraMap F E (Algebra.norm F (x : E)) =
    ((baseChange F E 1 (scalar (Units.map (Algebra.norm F) x)) : GeneralLinear 1 E) :
      Matrix (Fin 1) (Fin 1) E).det
  rw [Matrix.det_fin_one, baseChange_apply_apply]
  simp [Matrix.GeneralLinearGroup.coe_scalar]

end Norm

section Characters

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {E : Type v} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [Algebra F E]
variable [T2Space (GeneralLinear 1 F)] [LocallyCompactSpace (GeneralLinear 1 F)]
  [TotallyDisconnectedSpace (GeneralLinear 1 F)]
variable [T2Space (GeneralLinear 1 E)] [LocallyCompactSpace (GeneralLinear 1 E)]
  [TotallyDisconnectedSpace (GeneralLinear 1 E)]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem rankOne_act_scalar {ρ : Representation ℂ (GeneralLinear 1 F) V}
    {χ : Fˣ →* ℂˣ} (e : ρ.Equiv (rankOneCharacter χ)) (g : GeneralLinear 1 F) :
    ρ g = (χ (determinant g) : ℂ) • LinearMap.id := by
  ext x
  apply e.toLinearEquiv.injective
  change e (ρ g x) = e ((χ (determinant g) : ℂ) • x)
  rw [Conductor.rankOneCharacterEquiv_apply e, map_smul, smul_eq_mul]

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem isRegularSemisimple_rankOne (g : GeneralLinear 1 F) :
    IsRegularSemisimple g := by
  rw [← scalar_determinant_rankOne g]
  change ((Matrix.diagonal fun _ : Fin 1 => (determinant g : F)).charpoly).Separable
  rw [Matrix.charpoly_diagonal, Fin.prod_univ_one]
  exact Polynomial.separable_X_sub_C

/-- A rank-one Shintani lift has character obtained by pullback along the field norm. -/
theorem IsShintaniLift.rankOne_normPullback {σ : E ≃ₐ[F] E} {l : ℕ} (hcyc : IsCyclicAlgebra σ l)
    {π : Representation ℂ (GeneralLinear 1 F) V} {hπ : IsAdmissible π}
    {P : Representation ℂ (GeneralLinear 1 E) W} {hP : IsAdmissible P}
    {A : SigmaIntertwiner σ 1 P} {c : ℂ} (hlift : IsShintaniLift σ l π hπ P hP A c)
    {χ : Fˣ →* ℂˣ} {η : Eˣ →* ℂˣ}
    (eπ : π.Equiv (rankOneCharacter χ)) (eP : P.Equiv (rankOneCharacter η)) :
    η = χ.comp (Units.map (Algebra.norm F : E →* F)) := by
  let : FiniteDimensional ℂ V :=
    FiniteDimensional.of_injective eπ.toLinearEquiv.toLinearMap eπ.toLinearEquiv.injective
  let : FiniteDimensional ℂ W :=
    FiniteDimensional.of_injective eP.toLinearEquiv.toLinearMap eP.toLinearEquiv.injective
  have hdim : Module.finrank ℂ V = 1 :=
    eπ.toLinearEquiv.finrank_eq.trans (Module.finrank_self ℂ)
  have hpoint (δ : GeneralLinear 1 E) (γ : GeneralLinear 1 F)
      (hassoc : IsNormAssociated σ l δ γ) :
      (η (determinant δ) : ℂ) * LinearMap.trace ℂ W A.toLinearMap =
        c * (χ (determinant γ) : ℂ) := by
    obtain ⟨a, ha, hb⟩ := hlift.2 δ γ hassoc (isRegularSemisimple_rankOne γ)
    have hF := hasCharacterValue_trace π hπ γ
    rw [rankOne_act_scalar eπ γ, map_smul, LinearMap.trace_id, hdim, Nat.cast_one,
      smul_eq_mul, mul_one] at hF
    have hE := hasTwistedCharacterValue_trace P hP A.toLinearMap δ
    rw [rankOne_act_scalar eP δ, LinearMap.smul_comp, LinearMap.id_comp, map_smul,
      smul_eq_mul] at hE
    rw [ha.unique hF] at hb
    exact hE.unique hb
  have hunit : IsNormAssociated σ l (1 : GeneralLinear 1 E) (1 : GeneralLinear 1 F) := by
    simpa only [map_one] using hcyc.isNormAssociated_rankOne (1 : Eˣ)
  have hc : LinearMap.trace ℂ W A.toLinearMap = c := by simpa using hpoint 1 1 hunit
  ext x
  apply mul_right_cancel₀ hlift.1
  have hx := hpoint (scalar x) (scalar (Units.map (Algebra.norm F) x))
    (hcyc.isNormAssociated_rankOne x)
  simpa [hc, Matrix.GeneralLinearGroup.det_scalar, mul_comm] using hx

end Characters

end Langlands.BaseChange

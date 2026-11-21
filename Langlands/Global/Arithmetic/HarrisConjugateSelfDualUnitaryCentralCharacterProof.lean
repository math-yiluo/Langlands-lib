import Langlands.Global.Arithmetic.HarrisAuxiliaryConjugatePairStatement
import Langlands.Automorphic.IrreducibleCentralCharacterProof
import Langlands.Global.HeckeConjugateInverseUnitary
import Langlands.Global.IdeleClosedSubgroupDensity

/-!
# Conjugate self-dual cuspidal realizations have unitary central characters

The finite invariance of a conjugate contragredient pairing, applied to the scalar matrices
of finite ideles, gives `ω(c z) ω(z) = 1` for the central character `ω`. The ideles where
this holds form a closed subgroup containing the principal ideles and every local finite
group, hence all ideles. So `ω` is conjugate-inverse, hence unitary.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic Langlands.Global.CMConjugation
open Langlands.Automorphic.ContinuousRationalFunctions
open Langlands.Global.AdelicFunctoriality
  (adeleEquiv ideleEquiv infiniteAdeleEquiv ideleClassComplexConj ideleEquiv_diagonal)

variable {E : Type u} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

local instance : AddCommGroup (RationalInvariantFunctions E n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions E n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions E n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms E n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions E n) := Submodule.addCommGroup _
local instance (S : OperatorRealization E n) : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Entrywise CM conjugation of a scalar matrix is the scalar matrix of the conjugate
idele. -/
private theorem adelicConj_scalar (z : Ideles E) :
    adelicConj E n (AdelicGL.scalar E n z) =
      AdelicGL.scalar E n (ideleEquiv (fieldConj E) z) := by
  apply Units.ext
  ext i j
  change adeleEquiv (fieldConj E) (Matrix.scalar (Fin n) (z : Adeles E) i j) =
    Matrix.scalar (Fin n) (adeleEquiv (fieldConj E) (z : Adeles E)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero _

/-- Conjugation keeps the infinite part of an idele equal to one. -/
private theorem infPart_ideleEquiv (z : Ideles E) (h : IdeleDensity.infPart z = 1) :
    IdeleDensity.infPart (ideleEquiv (fieldConj E) z) = 1 := by
  change infiniteAdeleEquiv (fieldConj E) (IdeleDensity.infPart z) = 1
  rw [h, map_one]

omit [IsCMField E] in
/-- The scalar matrix of an idele with infinite part one lies in the finite factor. -/
private theorem ofFinite_finite_scalar (z : Ideles E) (h : IdeleDensity.infPart z = 1) :
    AdelicGL.ofFinite E n (AdelicGL.finite E n (AdelicGL.scalar E n z)) =
      AdelicGL.scalar E n z := by
  have h' : (z : Adeles E).1 = 1 := h
  apply Units.ext
  ext i j
  apply Prod.ext
  · change (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E)) i j =
      (Matrix.scalar (Fin n) (z : Adeles E) i j).1
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs
    · exact h'.symm
    · rfl
  · rfl

omit [IsCMField E] in
/-- With central character `ω`, the finite scalar matrix of an idele with infinite part one
acts by `ω` of that idele. -/
private theorem finiteRepresentation_scalar (S : OperatorRealization E n)
    (ω : HeckeCharacter E) (hω : S.HasCentralCharacter ω) (z : Ideles E)
    (h : IdeleDensity.infPart z = 1) (f : S.Space) :
    S.finiteRepresentation (AdelicGL.finite E n (AdelicGL.scalar E n z)) f =
      (centralIdeleCharacter E ω z : ℂ) • f := by
  apply S.toContinuous_injective
  apply toContinuousMap_injective E n
  ext x
  change evaluate E n (S.toContinuous
      (S.finiteRepresentation (AdelicGL.finite E n (AdelicGL.scalar E n z)) f)) x =
    evaluate E n (S.toContinuous ((centralIdeleCharacter E ω z : ℂ) • f)) x
  rw [S.evaluate_finiteRepresentation, ofFinite_finite_scalar z h,
    ← (AdelicGL.scalar_commute E n z x).eq, S.centralCharacter_evaluate ω hω,
    S.evaluate_toContinuous_smul]

omit [IsCMField E] in
/-- An irreducible realization with an injective partial pairing has a nonzero pairing
value. -/
private theorem exists_pairing_ne_zero (S : OperatorRealization E n) (hS : S.IsIrreducible)
    (B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ) (hinj : Function.Injective B.flip) :
    ∃ y x : S.Space, B y x ≠ 0 := by
  obtain ⟨f₀, x₀, h0⟩ := S.exists_evaluate_ne_zero hS
  by_contra! hB
  have hzero : ∀ f : S.Space, f = 0 := by
    intro f
    apply hinj
    ext y
    simp only [map_zero, LinearMap.zero_apply, LinearMap.flip_apply, hB]
  apply h0
  have h := S.evaluate_toContinuous_smul 0 f₀ x₀
  rw [zero_mul, zero_smul] at h
  rw [hzero f₀]
  exact h

/-- If a bilinear form keeps a nonzero value after scaling its arguments by `a` and `b`,
then `a * b = 1`. -/
private theorem mul_eq_one_of_bilinear {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) {y x y' x' : V} {a b : ℂ} (hy : y' = a • y) (hx : x' = b • x)
    (hB : B y' x' = B y x) (hyx : B y x ≠ 0) : a * b = 1 := by
  rw [hy, hx, LinearMap.map_smul₂, LinearMap.map_smul, smul_smul, smul_eq_mul] at hB
  exact (mul_eq_right₀ hyx).mp hB

/-- The finite invariance of the pairing on finite scalar matrices gives `ω(c z) ω(z) = 1`
for ideles with infinite part one. -/
private theorem mul_eq_one_of_pairing (S : OperatorRealization E n) (ω : HeckeCharacter E)
    (hω : S.HasCentralCharacter ω) (B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ)
    (hd : ∀ (d : FiniteAdelicGL E n) (y x : S.Space),
      B (S.finiteRepresentation (finiteConj E n d) y) (S.finiteRepresentation d x) = B y x)
    {y x : S.Space} (hyx : B y x ≠ 0) (z : Ideles E) (h : IdeleDensity.infPart z = 1) :
    (centralIdeleCharacter E ω (ideleEquiv (fieldConj E) z) : ℂ) *
      (centralIdeleCharacter E ω z : ℂ) = 1 := by
  have hconj : finiteConj E n (AdelicGL.finite E n (AdelicGL.scalar E n z)) =
      AdelicGL.finite E n (AdelicGL.scalar E n (ideleEquiv (fieldConj E) z)) := by
    rw [← finite_adelicConj, adelicConj_scalar]
  have h1 : S.finiteRepresentation
      (finiteConj E n (AdelicGL.finite E n (AdelicGL.scalar E n z))) y =
      (centralIdeleCharacter E ω (ideleEquiv (fieldConj E) z) : ℂ) • y := by
    rw [hconj]
    exact finiteRepresentation_scalar S ω hω _ (infPart_ideleEquiv z h) y
  have h2 : S.finiteRepresentation (AdelicGL.finite E n (AdelicGL.scalar E n z)) x =
      (centralIdeleCharacter E ω z : ℂ) • x :=
    finiteRepresentation_scalar S ω hω z h x
  exact mul_eq_one_of_bilinear B h1 h2 (hd _ y x) hyx

/-- A Hecke character with `ω(c z) ω(z) = 1` on all ideles of infinite part one is
conjugate-inverse. -/
private theorem isConjugateInverse_of_mul_eq_one (ω : HeckeCharacter E)
    (hloc : ∀ z : Ideles E, IdeleDensity.infPart z = 1 →
      (centralIdeleCharacter E ω (ideleEquiv (fieldConj E) z) : ℂ) *
        (centralIdeleCharacter E ω z : ℂ) = 1) :
    IsConjugateInverse ω := by
  let φ : Ideles E →* ℂˣ :=
    (centralIdeleCharacter E ω).toMonoidHom.comp (ideleEquiv (fieldConj E)).toMonoidHom *
      (centralIdeleCharacter E ω).toMonoidHom
  have hφ : ∀ z, φ z = centralIdeleCharacter E ω (ideleEquiv (fieldConj E) z) *
      centralIdeleCharacter E ω z := fun z => rfl
  have hφc : Continuous φ := by
    change Continuous (fun z => centralIdeleCharacter E ω (ideleEquiv (fieldConj E) z) *
      centralIdeleCharacter E ω z)
    exact ((centralIdeleCharacter E ω).continuous.comp
      (ideleEquiv (fieldConj E)).continuous).mul (centralIdeleCharacter E ω).continuous
  have hclosed : IsClosed (φ.ker : Set (Ideles E)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hφc
  have htop : φ.ker = ⊤ := by
    refine IdeleDensity.eq_top_of_isClosed φ.ker ∅ hclosed ?_ ?_
    · intro a
      rw [MonoidHom.mem_ker, hφ, ideleEquiv_diagonal, centralIdeleCharacter_principal,
        centralIdeleCharacter_principal, one_mul]
    · intro v _ a
      rw [MonoidHom.mem_ker, hφ]
      apply Units.ext
      rw [Units.val_mul, Units.val_one]
      exact hloc _ (IdeleDensity.infPart_finiteIdeleInclusion v a)
  intro q
  induction q using QuotientGroup.induction_on with
  | H z =>
    have hz : φ z = 1 := by
      rw [← MonoidHom.mem_ker, htop]
      exact Subgroup.mem_top z
    rw [hφ] at hz
    exact eq_inv_of_mul_eq_one_left hz

/-- **Conjugate self-dual cuspidal realizations have unitary central characters.** -/
theorem conjugateSelfDualUnitaryCentralCharacter :
    ConjugateSelfDualUnitaryCentralCharacterStatement.{u} := by
  intro E _ _ _ _ r S hS
  obtain ⟨B, ⟨hd, -, -⟩, -, hinj, -⟩ :=
    (CuspidalOperatorRealization.isoClass_isConjugateSelfDual_iff S).mp hS
  obtain ⟨ω, hω, -⟩ := S.realization.existsUnique_hasCentralCharacter S.irreducible
  obtain ⟨y, x, hyx⟩ := exists_pairing_ne_zero S.realization S.irreducible B hinj
  exact ⟨ω, HeckeConjugateInverse.isUnitary_of_isConjugateInverse ω
    (isConjugateInverse_of_mul_eq_one ω fun z hz =>
      mul_eq_one_of_pairing S.realization ω hω B hd hyx z hz), hω⟩

end Langlands.Global.Harris

import Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleSplit
import Langlands.Representation.Archimedean.ComplexStandardDualityProof
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesInfinitesimalCharacter
import Langlands.Representation.Archimedean.MaximallyFaithfulAnnihilator

/-!
# Non-largeness of linked Langlands quotients from a small submodule of the dual

`ComplexDualSubmoduleAnnihilatorStatement`: for a Langlands-ordered list `ds` of `n` complex
characters with a linked pair, and a list `ds'` of pointwise inverse position characters, the
`U(n)`-finite functions of the standard module of `ds'` have a nonzero `(𝔤, K)`-submodule `S`
and an element `u` of `U(𝔤)` that kills `S` but not the whole module.

`complexLinkedLanglandsQuotientNotLarge_of_dualSubmodule` derives
`ComplexLinkedLanglandsQuotientNotLargeStatement` from it, by the duality of
`complexStandardDuality`: the annihilator `K'` of `S` in the standard module of `ds` is a
proper `(𝔤, K)`-submodule, hence lies in the largest one `R`; the transpose `w` of `u` maps
the standard module into `K' ≤ R` and is nonzero. With the infinitesimal character of the
standard module, `maximallyFaithfulAnnihilator` then rules out maximal faithfulness modulo `R`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

-- As in `ComplexLargeStandardIrreducibleReduction`: the charts on units need reduction through
-- the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

universe uL uV uW

namespace ComplexLinkedLanglandsQuotientDuality

/-! ## The transpose on the universal enveloping algebra -/

section Transpose

variable {L : Type uL} [LieRing L] [LieAlgebra ℂ L]

/-- `x ↦ -x`, as a Lie algebra map from `L` to the opposite algebra of `U(L)`. -/
def negOp : L →ₗ⁅ℂ⁆ (UniversalEnvelopingAlgebra ℂ L)ᵐᵒᵖ where
  toFun x := MulOpposite.op (-(UniversalEnvelopingAlgebra.ι ℂ x))
  map_add' x y := by
    rw [map_add, neg_add, MulOpposite.op_add]
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply, smul_neg, MulOpposite.op_neg, MulOpposite.op_smul]
  map_lie' {x y} := by
    simp only [LieRing.of_associative_ring_bracket, LieHom.map_lie, ← MulOpposite.op_mul,
      ← MulOpposite.op_sub, neg_mul_neg, neg_sub]

/-- The principal anti-automorphism of `U(L)` (`x ↦ -x` on `L`), as an algebra map into the
opposite algebra. -/
def transpose : UniversalEnvelopingAlgebra ℂ L →ₐ[ℂ] (UniversalEnvelopingAlgebra ℂ L)ᵐᵒᵖ :=
  UniversalEnvelopingAlgebra.lift ℂ negOp

/-- The transpose of `u ∈ U(L)`, as an element of `U(L)`. -/
def tr (u : UniversalEnvelopingAlgebra ℂ L) : UniversalEnvelopingAlgebra ℂ L :=
  MulOpposite.unop (transpose u)

theorem tr_ι (x : L) : tr (UniversalEnvelopingAlgebra.ι ℂ x) =
    -(UniversalEnvelopingAlgebra.ι ℂ x) := by
  simp only [tr, transpose, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

theorem tr_mul (a b : UniversalEnvelopingAlgebra ℂ L) : tr (a * b) = tr b * tr a := by
  simp only [tr, map_mul, MulOpposite.unop_mul]

theorem tr_add (a b : UniversalEnvelopingAlgebra ℂ L) : tr (a + b) = tr a + tr b := by
  simp only [tr, map_add, MulOpposite.unop_add]

theorem tr_algebraMap (r : ℂ) :
    tr (algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) r) =
      algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) r := by
  simp only [tr, AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- **Transposition for an invariant bilinear form.** If `B (x v, w) + B (v, x w) = 0` for
`x ∈ L`, then `B (v, u w) = B (uᵀ v, w)` for every `u ∈ U(L)`. -/
theorem bilin_envelopingAction (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ (x : L) (v : V) (w : W), B (π x v) w + B v (π' x w) = 0)
    (u : UniversalEnvelopingAlgebra ℂ L) (v : V) (w : W) :
    B v (envelopingAction π' u w) = B (envelopingAction π (tr u) v) w := by
  induction u using InfinitesimalCharacter.envInduction generalizing v w with
  | algebraMap r =>
    rw [tr_algebraMap, AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul, LinearMap.map_smul₂]
  | ι x =>
    rw [tr_ι, map_neg, UniversalEnvelopingAlgebra.lift_ι_apply,
      UniversalEnvelopingAlgebra.lift_ι_apply, LinearMap.neg_apply, map_neg,
      LinearMap.neg_apply]
    linear_combination (hB x v w)
  | mul a b ha hb =>
    rw [tr_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
    rw [tr_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha, hb,
      LinearMap.map_add₂]

end Transpose

/-! ## Lie invariance of the duality on all of `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` -/

variable {n : ℕ}

theorem lie_one_tmul_eq (ds : List ComplexCharacterData) (X : Matrix (Fin n) (Fin n) ℂ)
    (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) :
    ∃ hf : rightDerivative (matrixModel ℂ n) X (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
        kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
      complexStandardLie n ds (1 ⊗ₜ X) f = ⟨_, hf⟩ := by
  have h := principalSeriesLie_one_tmul_apply_coe ℂ n (complexPositionCharacter ds) X f
  refine ⟨h ▸ (complexStandardLie n ds (1 ⊗ₜ X) f).2, Subtype.ext ?_⟩
  exact h

theorem pairing_lie {ds ds' : List ComplexCharacterData}
    (Q : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n) →ₗ[ℂ] ℂ)
    (hQ : ∀ (X : Matrix (Fin n) (Fin n) ℂ)
      (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))
      (h : kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n))
      (hf : rightDerivative (matrixModel ℂ n) X (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
        kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))
      (hh : rightDerivative (matrixModel ℂ n) X (h : Langlands.GeneralLinear n ℂ → ℂ) ∈
        kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n)),
      Q ⟨_, hf⟩ h + Q f ⟨_, hh⟩ = 0)
    (a : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))
    (h : kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n)) :
    Q (complexStandardLie n ds a f) h + Q f (complexStandardLie n ds' a h) = 0 := by
  induction a using TensorProduct.inductionOn with
  | tmul c X =>
    have hc : (c ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) = c • (1 ⊗ₜ X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    obtain ⟨hf, ef⟩ := lie_one_tmul_eq ds X f
    obtain ⟨hh, eh⟩ := lie_one_tmul_eq ds' X h
    rw [hc, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, ef, eh,
      map_smul, LinearMap.smul_apply, map_smul, ← smul_add, hQ X f h hf hh, smul_zero]
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add,
      LinearMap.add_apply, map_add]
    linear_combination ha + hb

end ComplexLinkedLanglandsQuotientDuality

open ComplexLinkedLanglandsQuotientDuality

/-! ## The statement and the reduction -/

/-- **A small `(𝔤, K)`-submodule of the dual standard module.** For a Langlands-ordered list `ds`
of `n` complex characters, two of which are linked, and a list `ds'` whose position characters
are pointwise inverse to those of `ds`, the `U(n)`-finite functions of the standard module of
`ds'` have a nonzero `(𝔤, K)`-submodule `S` and an element `u` of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℂ))` that acts
by `0` on `S` but not on the whole module. -/
def ComplexDualSubmoduleAnnihilatorStatement : Prop :=
  ∀ (n : ℕ) (ds ds' : List ComplexCharacterData), ds.length = n → IsComplexLanglandsOrdered ds →
    ¬ IsComplexUnlinked ds →
    (∀ (i : ℕ) (z : ℂˣ), complexPositionCharacter ds i z * complexPositionCharacter ds' i z = 1) →
      ∃ S : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n)),
        IsGKSubmodule (complexStandardRep n ds') (complexStandardLie n ds') S ∧ S ≠ ⊥ ∧
        ∃ u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ),
          (∀ s ∈ S, envelopingAction (complexStandardLie n ds') u s = 0) ∧
          envelopingAction (complexStandardLie n ds') u ≠ 0

/-- **The reduction.** A small submodule of the dual standard module gives, by duality, an
element of `U(𝔤)` that maps the standard module of `ds` into `R` and acts by a nonzero
operator. By `maximallyFaithfulAnnihilator` this contradicts maximal faithfulness modulo `R`. -/
theorem complexLinkedLanglandsQuotientNotLarge_of_dualSubmodule
    (hS : ComplexDualSubmoduleAnnihilatorStatement) :
    ComplexLinkedLanglandsQuotientNotLargeStatement := by
  intro n ds R hlen hord hlink _hRgk hRtop hRmax hmf
  set ds' := ds.map complexCharacterDataInv
  have hχ : ∀ (i : ℕ) (z : ℂˣ),
      complexPositionCharacter ds i z * complexPositionCharacter ds' i z = 1 := fun i z => by
    rw [mul_comm]
    exact complexPositionCharacter_map_inv_mul ds i z
  obtain ⟨Q, hQK, hQX, hQnd⟩ := complexStandardDuality n ds ds' hχ
  obtain ⟨S, hSgk, hS0, u, huS, hu0⟩ := hS n ds ds' hlen hord hlink hχ
  -- The annihilator of `S` in the standard module of `ds`.
  let K' : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) :=
    { carrier := {f | ∀ s ∈ S, Q f s = 0}
      add_mem' := fun {a b} ha hb s hs => by
        rw [map_add, LinearMap.add_apply, ha s hs, hb s hs, add_zero]
      zero_mem' := fun s _ => by rw [map_zero, LinearMap.zero_apply]
      smul_mem' := fun c f hf s hs => by
        rw [map_smul, LinearMap.smul_apply, hf s hs, smul_zero] }
  have hK'gk : IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) K' := by
    refine ⟨fun k f hf s hs => ?_, fun X f hf s hs => ?_⟩
    · have hs' : complexStandardRep n ds' k⁻¹ s ∈ S := hSgk.1 k⁻¹ s hs
      have hk : (Unitary.toUnits k : Langlands.GeneralLinear n ℂ) ∈ unitaryCompact ℂ n := k.2
      have e := hQK ⟨_, hk⟩ f (complexStandardRep n ds' k⁻¹ s)
        (complexStandardRep n ds k f).2 (complexStandardRep n ds' k (complexStandardRep n ds' k⁻¹ s)).2
      have e1 : complexStandardRep n ds' k (complexStandardRep n ds' k⁻¹ s) = s := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      calc Q (complexStandardRep n ds k f) s
          = Q ⟨_, (complexStandardRep n ds k f).2⟩
              ⟨_, (complexStandardRep n ds' k (complexStandardRep n ds' k⁻¹ s)).2⟩ := by
            rw [Subtype.coe_eta, Subtype.coe_eta, e1]
        _ = Q f (complexStandardRep n ds' k⁻¹ s) := e
        _ = 0 := hf _ hs'
    · have e := pairing_lie Q hQX X f s
      rw [hf _ (hSgk.2 X s hs), add_zero] at e
      exact e
  have hK'top : K' ≠ ⊤ := by
    obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
    obtain ⟨f, hf⟩ := hQnd s hs0
    intro htop
    have hfK : f ∈ K' := htop ▸ Submodule.mem_top
    exact hf (hfK s hs)
  have hK'R : K' ≤ R := hRmax K' hK'gk hK'top
  -- The transpose of `u`.
  have hw : ∀ v, envelopingAction (complexStandardLie n ds) (tr u) v ∈ R := by
    intro f
    refine hK'R fun s hs => ?_
    rw [← bilin_envelopingAction (complexStandardLie n ds) (complexStandardLie n ds') Q
      (fun X f h => pairing_lie Q hQX X f h) u f s, huS s hs, map_zero]
  have hw0 := MaximallyFaithfulAnnihilator.envelopingAction_eq_zero
    (complexStandardLie_hasInfinitesimalCharacter n ds) hRtop hmf hw
  apply hu0
  refine LinearMap.ext fun h => ?_
  by_contra hne
  rw [LinearMap.zero_apply] at hne
  obtain ⟨f, hf⟩ := hQnd _ hne
  rw [bilin_envelopingAction (complexStandardLie n ds) (complexStandardLie n ds') Q
    (fun X f h => pairing_lie Q hQX X f h) u f h, hw0, LinearMap.zero_apply, map_zero,
    LinearMap.zero_apply] at hf
  exact hf rfl

end Langlands.Archimedean

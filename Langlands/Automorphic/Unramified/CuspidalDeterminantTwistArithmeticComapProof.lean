import Langlands.Automorphic.Unramified.CuspidalWeakBaseChangeTwistStatement

/-! # Finite-order determinant twists under arithmetic pullback

For a number-field isomorphism `e : K ≃+* L`, arithmetic transport of actual operator
realizations carries a finite-order determinant twist by `χ` to a finite-order determinant
twist by `HeckeCharacter.comap e χ`. The twisting linear equivalence is conjugated by the
linear equivalences of the two arithmetic transports. The scalars of the finite and compact
equations are compared through `AdelicGLTransport.determinant_adelicEquiv`, the compatibility
of the adelic determinant with arithmetic transport. Applied to the transports
`OperatorRealization.isArithmeticTransport_arithmeticComap`, this gives the statement
`Unramified.CuspidalDeterminantTwistArithmeticComapStatement` on actual cuspidal classes.
-/

noncomputable section

universe uF uE

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

section Transport

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] {n : ℕ}

local instance determinantTwistComapRationalGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance determinantTwistComapContinuousGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance determinantTwistComapFiniteSmoothGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance determinantTwistComapFormGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance determinantTwistComapStableGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance determinantTwistComapSpaceGroup {F : Type*} [Field F] [NumberField F]
    (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- The determinant character of the pulled-back Hecke character at `g` is the original
determinant character at the entrywise transported adelic matrix. -/
theorem determinantTwistScalar_comap (e : K ≃+* L) (χ : HeckeCharacter L)
    (g : AdelicGL K n) :
    determinantTwistScalar (HeckeCharacter.comap e χ) g =
      determinantTwistScalar χ (AdelicGLTransport.adelicEquiv n e g) := by
  unfold determinantTwistScalar
  rw [HeckeCharacter.comap_onIdeles, AdelicGLTransport.determinant_adelicEquiv]

/-- The finite-adelic case of `determinantTwistScalar_comap`. -/
theorem determinantTwistScalar_comap_ofFinite (e : K ≃+* L) (χ : HeckeCharacter L)
    (d : FiniteAdelicGL K n) :
    determinantTwistScalar (HeckeCharacter.comap e χ) (AdelicGL.ofFinite K n d) =
      determinantTwistScalar χ (AdelicGL.ofFinite L n (AdelicGLTransport.finiteEquiv n e d)) := by
  rw [determinantTwistScalar_comap, AdelicGLTransport.adelicEquiv_ofFinite]

/-- The case of the standard compact subgroup at the infinite places. -/
theorem determinantTwistScalar_comap_ofInfinite (e : K ≃+* L) (χ : HeckeCharacter L)
    (k : standardInfiniteCompact K n) :
    determinantTwistScalar (HeckeCharacter.comap e χ) (AdelicGL.ofInfinite K n k.val) =
      determinantTwistScalar χ
        (AdelicGL.ofInfinite L n (ArchimedeanCompactTransport.compactEquiv n e k).val) := by
  rw [determinantTwistScalar_comap, AdelicGLTransport.adelicEquiv_ofInfinite]
  rfl

namespace OperatorRealization

variable {χ : HeckeCharacter L}

/-- One scalar twist equation conjugated by two intertwining linear equivalences. -/
private theorem conjugate_equation
    {V' W' V W : Type*} [AddCommGroup V'] [AddCommGroup W'] [AddCommGroup V] [AddCommGroup W]
    [Module ℂ V'] [Module ℂ W'] [Module ℂ V] [Module ℂ W]
    (φ : V' ≃ₗ[ℂ] V) (ψ : W' ≃ₗ[ℂ] W) (q : V ≃ₗ[ℂ] W)
    (A' : Module.End ℂ V') (B' : Module.End ℂ W') (A : Module.End ℂ V) (B : Module.End ℂ W)
    {c c' : ℂ} (hc : c' = c) (hφ : ∀ f, φ (A' f) = A (φ f)) (hψ : ∀ g, ψ (B' g) = B (ψ g))
    (hq : ∀ f, B (q f) = c • q (A f)) (f : V') :
    B' (((φ.trans q).trans ψ.symm) f) = c' • ((φ.trans q).trans ψ.symm) (A' f) := by
  apply ψ.injective
  rw [hc, hψ, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.map_smul, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, hφ, hq]

/-- Determinant-twist equations transported along arithmetic transports: if `φ` and `ψ`
carry the actions on `S'` and `T'` over `K` to those of their arithmetic images on `S` and
`T` over `L`, the composite `ψ⁻¹ ∘ q ∘ φ` satisfies the twist equations for the pulled-back
character whenever `q` satisfies them for `χ`. -/
theorem DeterminantTwistEquations.of_arithmeticTransportEquations (e : K ≃+* L)
    {S' T' : OperatorRealization K n} {S T : OperatorRealization L n}
    {φ : S'.Space ≃ₗ[ℂ] S.Space} {ψ : T'.Space ≃ₗ[ℂ] T.Space} {q : S.Space ≃ₗ[ℂ] T.Space}
    (hφ : ArithmeticTransportEquations e S' S φ) (hψ : ArithmeticTransportEquations e T' T ψ)
    (hq : DeterminantTwistEquations χ S T q) :
    DeterminantTwistEquations (HeckeCharacter.comap e χ) S' T' ((φ.trans q).trans ψ.symm) :=
  ⟨fun d f => conjugate_equation φ ψ q _ _ _ _ (determinantTwistScalar_comap_ofFinite e χ d)
      (hφ.1 d) (hψ.1 d) (hq.1 _) f,
    fun k f => conjugate_equation φ ψ q _ _ _ _ (determinantTwistScalar_comap_ofInfinite e χ k)
      (hφ.2.1 k) (hψ.2.1 k) (hq.2.1 _) f,
    fun a f => (conjugate_equation φ ψ q _ _ _ _ (c := 1) rfl (hφ.2.2 a) (hψ.2.2 a)
      (fun g => (hq.2.2 _ g).trans (one_smul ℂ _).symm) f).trans (one_smul ℂ _)⟩

/-- The finite-order determinant twist relation is transported along arithmetic transports
of source and target, with the pulled-back character. -/
theorem IsFiniteOrderDeterminantTwist.of_isArithmeticTransport (e : K ≃+* L)
    {S' T' : OperatorRealization K n} {S T : OperatorRealization L n}
    (hS : IsArithmeticTransport e S' S) (hT : IsArithmeticTransport e T' T)
    (h : IsFiniteOrderDeterminantTwist χ S T) :
    IsFiniteOrderDeterminantTwist (HeckeCharacter.comap e χ) S' T' := by
  obtain ⟨φ, hφ⟩ := hS
  obtain ⟨ψ, hψ⟩ := hT
  obtain ⟨hχ, q, hq⟩ := h
  exact ⟨(HeckeCharacter.hasFiniteOrder_comap_iff e χ).mpr hχ, _,
    hq.of_arithmeticTransportEquations e hφ hψ⟩

/-- Arithmetic pullback of supplied full realizations transports the finite-order
determinant twist relation with the pulled-back character. -/
theorem IsFiniteOrderDeterminantTwist.arithmeticComap (e : K ≃+* L)
    {S T : OperatorRealization L n} (h : IsFiniteOrderDeterminantTwist χ S T) :
    IsFiniteOrderDeterminantTwist (HeckeCharacter.comap e χ) (S.arithmeticComap e)
      (T.arithmeticComap e) :=
  h.of_isArithmeticTransport e (S.isArithmeticTransport_arithmeticComap e)
    (T.isArithmeticTransport_arithmeticComap e)

end OperatorRealization
end Transport

namespace Unramified

/-- Arithmetic pullback of actual cuspidal classes transports the finite-order
determinant twist relation with the pullback of the character. -/
theorem cuspidalDeterminantTwistArithmeticComap :
    CuspidalDeterminantTwistArithmeticComapStatement.{uF, uE} := by
  intro F E _ _ _ _ _ _ e r c c' χ h
  revert h
  refine Quotient.inductionOn₂ c c' ?_
  intro S T h
  exact OperatorRealization.IsFiniteOrderDeterminantTwist.arithmeticComap e h

end Unramified
end Langlands.Automorphic

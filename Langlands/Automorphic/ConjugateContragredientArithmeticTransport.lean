import Langlands.Automorphic.ConjugateContragredient
import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.Global.CMConjugationArithmeticTransport

/-!
# Arithmetic pullback of conjugate-contragredient pairings

For CM fields `K`, `L`, a ring isomorphism `e : K ≃+* L` and an actual realization `S`
over `L`, let `φ = S.arithmeticComapEquiv e` be the linear equivalence from `S` onto its
arithmetic pullback `S.arithmeticComap e`. If `B` is a conjugate-contragredient pairing
of `S`, then `B' y x = B (φ⁻¹ y) (φ⁻¹ x)` is one of the pullback. The invariance
identities follow because `φ` intertwines the finite, compact and Lie algebra actions
through the arithmetic transports along `e`, which commute with the CM conjugations.
The bijection onto the contragredient functionals follows because `l ↦ l ∘ φ⁻¹` and
`l ↦ l ∘ φ` exchange the contragredient functionals of `S` and of the pullback.

The functional transport rests on two general facts proved first: along a linear map
intertwining two representations through a group homomorphism `α`, pulling back a
functional preserves finiteness of its orbit span under the dual actions, and, for `α`
continuous, smoothness under the dual actions.
-/

noncomputable section

universe uk uG uH uV uW uK uL

set_option autoImplicit false

namespace Langlands

section DualPullback

variable {k : Type uk} [Field k] {G : Type uG} {H : Type uH} [Group G] [Group H]
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (ρ : Representation k G V) (τ : Representation k H W) (α : H →* G) (ψ : W →ₗ[k] V)

/-- Pulling back a functional along `ψ` intertwines the dual actions through `α`. -/
theorem dual_apply_comp_of_intertwining (hψ : ∀ h w, ψ (τ h w) = ρ (α h) (ψ w)) (h : H)
    (l : Module.Dual k V) :
    τ.dual h (l ∘ₗ ψ) = ρ.dual (α h) l ∘ₗ ψ := by
  apply LinearMap.ext
  intro w
  change l (ψ (τ h⁻¹ w)) = l (ρ (α h)⁻¹ (ψ w))
  rw [hψ, map_inv]

/-- Pulling back along an intertwiner through a continuous homomorphism preserves smooth
vectors of the dual actions. -/
theorem isSmoothVector_dual_comp_of_intertwining [TopologicalSpace G] [TopologicalSpace H]
    (hψ : ∀ h w, ψ (τ h w) = ρ (α h) (ψ w)) (hα : Continuous α) {l : Module.Dual k V}
    (hl : IsSmoothVector ρ.dual l) : IsSmoothVector τ.dual (l ∘ₗ ψ) := by
  obtain ⟨U, hU⟩ := hl
  refine ⟨U.comap α hα, ?_⟩
  rintro ⟨h, hh⟩
  change τ.dual h (l ∘ₗ ψ) = l ∘ₗ ψ
  rw [dual_apply_comp_of_intertwining ρ τ α ψ hψ h l]
  exact congrArg (fun m : Module.Dual k V => m ∘ₗ ψ) (hU ⟨α h, hh⟩)

/-- Pulling back along an intertwiner through a homomorphism preserves finite vectors of
the dual actions. -/
theorem isFiniteVector_dual_comp_of_intertwining (hψ : ∀ h w, ψ (τ h w) = ρ (α h) (ψ w))
    {l : Module.Dual k V} (hl : FiniteVectors.IsFiniteVector ρ.dual l) :
    FiniteVectors.IsFiniteVector τ.dual (l ∘ₗ ψ) := by
  have : Module.Finite k (FiniteVectors.orbitSpan ρ.dual l) := hl
  have hle : FiniteVectors.orbitSpan τ.dual (l ∘ₗ ψ) ≤
      (FiniteVectors.orbitSpan ρ.dual l).map ψ.dualMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    change τ.dual h (l ∘ₗ ψ) ∈ _
    rw [dual_apply_comp_of_intertwining ρ τ α ψ hψ h l]
    exact Submodule.mem_map_of_mem (FiniteVectors.action_mem_orbitSpan ρ.dual (α h) l)
  exact Submodule.finiteDimensional_of_le hle

end DualPullback

namespace Automorphic

open NumberField Langlands.Global Langlands.Global.CMConjugation AdelicGLTransport

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]
  {n : ℕ}

local instance conjugateArithmeticRationalAddCommGroup {F : Type*} [Field F] [NumberField F] :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance conjugateArithmeticContinuousAddCommGroup {F : Type*} [Field F]
    [NumberField F] : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance conjugateArithmeticSmoothAddCommGroup {F : Type*} [Field F] [NumberField F] :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance conjugateArithmeticFormsAddCommGroup {F : Type*} [Field F] [NumberField F] :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance conjugateArithmeticStableAddCommGroup {F : Type*} [Field F] [NumberField F] :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

local instance conjugateArithmeticSpaceAddCommGroup {F : Type*} [Field F] [NumberField F]
    (T : OperatorRealization F n) : AddCommGroup T.Space := Submodule.addCommGroup _

variable (e : K ≃+* L) (S : OperatorRealization L n)

/-- The inverse of the arithmetic pullback equivalence intertwines the real Lie algebra
actions through the arithmetic transport of the Lie algebra. -/
theorem arithmeticComapEquiv_symm_lieAction (X : ArchimedeanGL.RealLieAlgebra K n)
    (f : (S.arithmeticComap e).Space) :
    (S.arithmeticComapEquiv e).symm ((S.arithmeticComap e).lieAction X f) =
      S.lieAction (ArchimedeanLieTransport.realLieEquiv n e X)
        ((S.arithmeticComapEquiv e).symm f) := by
  have hu : ArchimedeanLieTransport.envelopingEquiv n e
      (ArchimedeanGL.envelopingGenerator K n (ArchimedeanGL.complexify K n X)) =
        ArchimedeanGL.envelopingGenerator L n
          (ArchimedeanGL.complexify L n (ArchimedeanLieTransport.realLieEquiv n e X)) :=
    ArchimedeanLieTransport.envelopingEquiv_generator n e _
  exact (S.arithmeticComapEquiv_symm_differential e _ f).trans
    (congrArg (fun u => S.envelopingAction u ((S.arithmeticComapEquiv e).symm f)) hu)

/-- Contragredient functionals of `S` pulled back along the inverse equivalence are
contragredient functionals of the arithmetic pullback. -/
theorem isContragredientFunctional_comp_arithmeticComapEquiv_symm {l : Module.Dual ℂ S.Space}
    (hl : S.IsContragredientFunctional l) :
    (S.arithmeticComap e).IsContragredientFunctional
      (l ∘ₗ ((S.arithmeticComapEquiv e).symm.toLinearEquiv.toLinearMap)) :=
  ⟨isSmoothVector_dual_comp_of_intertwining S.finiteRepresentation
      (S.arithmeticComap e).finiteRepresentation
      (AdelicGLTransport.finiteEquiv n e).toMulEquiv.toMonoidHom _
      (fun d f => S.arithmeticComapEquiv_symm_finite e d f)
      (AdelicGLTransport.finiteEquiv n e).continuous hl.1,
    isFiniteVector_dual_comp_of_intertwining S.compactRepresentation
      (S.arithmeticComap e).compactRepresentation
      (ArchimedeanCompactTransport.compactEquiv n e).toMonoidHom _
      (fun k f => S.arithmeticComapEquiv_symm_compact e k f) hl.2⟩

/-- Contragredient functionals of the arithmetic pullback pulled back along the
equivalence are contragredient functionals of `S`. -/
theorem isContragredientFunctional_comp_arithmeticComapEquiv
    {l : Module.Dual ℂ (S.arithmeticComap e).Space}
    (hl : (S.arithmeticComap e).IsContragredientFunctional l) :
    S.IsContragredientFunctional (l ∘ₗ (S.arithmeticComapEquiv e).toLinearEquiv.toLinearMap) := by
  refine ⟨isSmoothVector_dual_comp_of_intertwining _ _
      (AdelicGLTransport.finiteEquiv n e).symm.toMulEquiv.toMonoidHom _ (fun d f => ?_)
      (AdelicGLTransport.finiteEquiv n e).symm.continuous hl.1,
    isFiniteVector_dual_comp_of_intertwining _ _
      (ArchimedeanCompactTransport.compactEquiv n e).symm.toMonoidHom _ (fun k f => ?_) hl.2⟩
  · exact (congrArg (fun g => S.arithmeticComapEquiv e (S.finiteRepresentation g f))
      ((AdelicGLTransport.finiteEquiv n e).apply_symm_apply d)).symm.trans
        (S.arithmeticComapEquiv_finite e ((AdelicGLTransport.finiteEquiv n e).symm d) f).symm
  · exact (congrArg (fun g => S.arithmeticComapEquiv e (S.compactRepresentation g f))
      ((ArchimedeanCompactTransport.compactEquiv n e).apply_symm_apply k)).symm.trans
        (S.arithmeticComapEquiv_compact e
          ((ArchimedeanCompactTransport.compactEquiv n e).symm k) f).symm

variable {S} [IsCMField K] [IsCMField L]

/-- The pulled-back pairing satisfies the finite twisted invariance identity. -/
theorem arithmeticComap_conjugateInvariant_finite {B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ}
    (hd : ∀ (d : FiniteAdelicGL L n) (y x : S.Space),
      B (S.finiteRepresentation (finiteConj L n d) y) (S.finiteRepresentation d x) = B y x)
    (d : FiniteAdelicGL K n) (y x : (S.arithmeticComap e).Space) :
    B ((S.arithmeticComapEquiv e).symm
        ((S.arithmeticComap e).finiteRepresentation (finiteConj K n d) y))
      ((S.arithmeticComapEquiv e).symm ((S.arithmeticComap e).finiteRepresentation d x)) =
      B ((S.arithmeticComapEquiv e).symm y) ((S.arithmeticComapEquiv e).symm x) :=
  (congrArg₂ (fun a b => B a b)
    ((S.arithmeticComapEquiv_symm_finite e (finiteConj K n d) y).trans
      (congrArg (fun g => S.finiteRepresentation g ((S.arithmeticComapEquiv e).symm y))
        (finiteEquiv_finiteConj n e d)))
    (S.arithmeticComapEquiv_symm_finite e d x)).trans
    (hd (AdelicGLTransport.finiteEquiv n e d) _ _)

/-- The pulled-back pairing satisfies the compact twisted invariance identity. -/
theorem arithmeticComap_conjugateInvariant_compact {B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ}
    (hk : ∀ (k : standardInfiniteCompact L n) (y x : S.Space),
      B (S.compactRepresentation (compactConj L n k) y) (S.compactRepresentation k x) = B y x)
    (k : standardInfiniteCompact K n) (y x : (S.arithmeticComap e).Space) :
    B ((S.arithmeticComapEquiv e).symm
        ((S.arithmeticComap e).compactRepresentation (compactConj K n k) y))
      ((S.arithmeticComapEquiv e).symm ((S.arithmeticComap e).compactRepresentation k x)) =
      B ((S.arithmeticComapEquiv e).symm y) ((S.arithmeticComapEquiv e).symm x) :=
  (congrArg₂ (fun a b => B a b)
    ((S.arithmeticComapEquiv_symm_compact e (compactConj K n k) y).trans
      (congrArg (fun g => S.compactRepresentation g ((S.arithmeticComapEquiv e).symm y))
        (compactEquiv_compactConj n e k)))
    (S.arithmeticComapEquiv_symm_compact e k x)).trans
    (hk (ArchimedeanCompactTransport.compactEquiv n e k) _ _)

/-- The pulled-back pairing satisfies the twisted Lie algebra identity. -/
theorem arithmeticComap_conjugateInvariant_lie {B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ}
    (hX : ∀ (X : ArchimedeanGL.RealLieAlgebra L n) (y x : S.Space),
      B (S.lieAction (lieConj L n X) y) x + B y (S.lieAction X x) = 0)
    (X : ArchimedeanGL.RealLieAlgebra K n) (y x : (S.arithmeticComap e).Space) :
    B ((S.arithmeticComapEquiv e).symm ((S.arithmeticComap e).lieAction (lieConj K n X) y))
        ((S.arithmeticComapEquiv e).symm x) +
      B ((S.arithmeticComapEquiv e).symm y)
        ((S.arithmeticComapEquiv e).symm ((S.arithmeticComap e).lieAction X x)) = 0 :=
  (congrArg₂ (fun a b => B a ((S.arithmeticComapEquiv e).symm x) +
      B ((S.arithmeticComapEquiv e).symm y) b)
    ((S.arithmeticComapEquiv_symm_lieAction e (lieConj K n X) y).trans
      (congrArg (fun Z => S.lieAction Z ((S.arithmeticComapEquiv e).symm y))
        (realLieEquiv_lieConj n e X)))
    (S.arithmeticComapEquiv_symm_lieAction e X x)).trans
    (hX (ArchimedeanLieTransport.realLieEquiv n e X) _ _)

/-- Arithmetic pullback between CM fields preserves conjugate self-duality: a
conjugate-contragredient pairing `B` of `S` gives the pairing
`B (φ⁻¹ ·) (φ⁻¹ ·)` of `S.arithmeticComap e`, with `φ = S.arithmeticComapEquiv e`. -/
theorem IsConjugateSelfDual.arithmeticComap (hS : S.IsConjugateSelfDual) :
    (S.arithmeticComap e).IsConjugateSelfDual := by
  obtain ⟨B, ⟨hd, hk, hX⟩, hB, hinj, hsurj⟩ := hS
  refine ⟨B.compl₁₂ (S.arithmeticComapEquiv e).symm.toLinearEquiv.toLinearMap
    (S.arithmeticComapEquiv e).symm.toLinearEquiv.toLinearMap, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact arithmeticComap_conjugateInvariant_finite e hd
  · exact arithmeticComap_conjugateInvariant_compact e hk
  · exact arithmeticComap_conjugateInvariant_lie e hX
  · intro x
    exact S.isContragredientFunctional_comp_arithmeticComapEquiv_symm e
      (hB ((S.arithmeticComapEquiv e).symm x))
  · intro x₁ x₂ h
    apply (S.arithmeticComapEquiv e).symm.injective
    apply hinj
    apply LinearMap.ext
    intro y
    have h₀ := LinearMap.congr_fun h (S.arithmeticComapEquiv e y)
    have h₁ : ∀ x, B.flip ((S.arithmeticComapEquiv e).symm x) y =
        (B.compl₁₂ (S.arithmeticComapEquiv e).symm.toLinearEquiv.toLinearMap
          (S.arithmeticComapEquiv e).symm.toLinearEquiv.toLinearMap).flip x
          (S.arithmeticComapEquiv e y) := by
      intro x
      exact (congrArg (fun z => B z ((S.arithmeticComapEquiv e).symm x))
        ((S.arithmeticComapEquiv e).symm_apply_apply y)).symm
    exact (h₁ x₁).trans (h₀.trans (h₁ x₂).symm)
  · intro l hl
    obtain ⟨x, hx⟩ := hsurj (l ∘ₗ (S.arithmeticComapEquiv e).toLinearEquiv.toLinearMap)
      (S.isContragredientFunctional_comp_arithmeticComapEquiv e hl)
    refine ⟨S.arithmeticComapEquiv e x, ?_⟩
    apply LinearMap.ext
    intro y
    have h₀ := LinearMap.congr_fun hx ((S.arithmeticComapEquiv e).symm y)
    have h₁ : (B.compl₁₂ (S.arithmeticComapEquiv e).symm.toLinearEquiv.toLinearMap
          (S.arithmeticComapEquiv e).symm.toLinearEquiv.toLinearMap).flip
          (S.arithmeticComapEquiv e x) y = B.flip x ((S.arithmeticComapEquiv e).symm y) :=
      congrArg (fun z => B ((S.arithmeticComapEquiv e).symm y) z)
        ((S.arithmeticComapEquiv e).symm_apply_apply x)
    have h₂ : (l ∘ₗ (S.arithmeticComapEquiv e).toLinearEquiv.toLinearMap)
        ((S.arithmeticComapEquiv e).symm y) = l y :=
      congrArg l ((S.arithmeticComapEquiv e).apply_symm_apply y)
    exact h₁.trans (h₀.trans h₂)

/-- Arithmetic pullback between CM fields preserves conjugate self-duality of
full-operator classes. -/
theorem IsoClass.IsConjugateSelfDual.arithmeticComap {c : IsoClass L n}
    (hc : c.IsConjugateSelfDual) : (IsoClass.arithmeticComap e c).IsConjugateSelfDual := by
  obtain ⟨S, rfl, hS⟩ := hc
  exact ⟨S.arithmeticComap e, rfl, hS.arithmeticComap e⟩

end OperatorRealization

namespace CuspidalOperatorRealization

variable [IsCMField K] [IsCMField L] [CompactSpace (AdeleQuotient K)]
  [CompactSpace (AdeleQuotient L)] {r : ℕ} (e : K ≃+* L)

/-- Arithmetic pullback between CM fields preserves conjugate self-duality of
irreducible cuspidal classes. -/
theorem IsoClass.IsConjugateSelfDual.arithmeticComap {c : IsoClass L r}
    (hc : c.IsConjugateSelfDual) : (IsoClass.arithmeticComap e c).IsConjugateSelfDual := by
  change (IsoClass.arithmeticComap e c).toOperatorClass.IsConjugateSelfDual
  rw [IsoClass.toOperatorClass_arithmeticComap]
  exact OperatorRealization.IsoClass.IsConjugateSelfDual.arithmeticComap e hc

end CuspidalOperatorRealization

end Automorphic

end Langlands

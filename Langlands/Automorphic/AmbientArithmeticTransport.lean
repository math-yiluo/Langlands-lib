import Langlands.Automorphic.Ambient
import Langlands.Global.AdelicGLTransport
import Langlands.Global.HeckeCharacterTransport
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.RingTheory.Finiteness.Basic

/-! # Arithmetic pullback on actual continuous rational-invariant functions -/

noncomputable section
universe uK uL uM

set_option autoImplicit false

namespace Langlands.Automorphic.ContinuousRationalFunctions

open Langlands.Global AdelicGLTransport

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

/-- Precomposition by the actual arithmetic adelic GL equivalence. -/
def arithmeticComap (n : ℕ) (e : K ≃+* L) :
    ContinuousRationalFunctions L n →ₗ[ℂ] ContinuousRationalFunctions K n where
  toFun f :=
    ⟨⟨fun x => evaluate L n f (adelicEquiv n e x), by
      intro γ x
      change evaluate L n f (adelicEquiv n e (AdelicGL.rational K n γ * x)) =
        evaluate L n f (adelicEquiv n e x)
      rw [map_mul, adelicEquiv_rational]
      exact evaluate_rational L n f _ _⟩,
      (continuous_evaluate L n f).comp (adelicEquiv n e).continuous⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evaluate_arithmeticComap (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) (x : AdelicGL K n) :
    evaluate K n (arithmeticComap n e f) x = evaluate L n f (adelicEquiv n e x) := rfl

@[simp] theorem arithmeticComap_refl (n : ℕ) (f : ContinuousRationalFunctions K n) :
    arithmeticComap n (RingEquiv.refl K) f = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evaluate K n f (adelicEquiv n (RingEquiv.refl K) x) = evaluate K n f x
  rw [adelicEquiv_refl]
  rfl

/-- Arithmetic pullback is contravariant under composition. -/
theorem arithmeticComap_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M)
    (f : ContinuousRationalFunctions M n) :
    arithmeticComap n (e.trans a) f = arithmeticComap n e (arithmeticComap n a f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evaluate M n f (adelicEquiv n (e.trans a) x) =
    evaluate M n f (adelicEquiv n a (adelicEquiv n e x))
  rw [adelicEquiv_trans]
  rfl

@[simp] theorem arithmeticComap_symm_apply (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e.symm (arithmeticComap n e f) = f := by
  rw [← arithmeticComap_trans]
  simp only [RingEquiv.symm_trans_self, arithmeticComap_refl]

@[simp] theorem arithmeticComap_apply_symm (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions K n) :
    arithmeticComap n e (arithmeticComap n e.symm f) = f := by
  rw [← arithmeticComap_trans]
  simp only [RingEquiv.self_trans_symm, arithmeticComap_refl]

/-- Continuity uses actual compact-open precomposition and the induced topology. -/
theorem continuous_arithmeticComap (n : ℕ) (e : K ≃+* L) :
    Continuous (arithmeticComap n e) := by
  rw [continuous_induced_rng]
  let a : C(AdelicGL K n, AdelicGL L n) :=
    ⟨adelicEquiv n e, (adelicEquiv n e).continuous⟩
  exact (ContinuousMap.continuous_precomp a).comp
    (show Continuous (toContinuousMap L n) from continuous_induced_dom)

/-- The actual continuous linear equivalence, with inverse arithmetic pullback. -/
def arithmeticEquiv (n : ℕ) (e : K ≃+* L) :
    ContinuousRationalFunctions L n ≃L[ℂ] ContinuousRationalFunctions K n where
  __ := arithmeticComap n e
  invFun := arithmeticComap n e.symm
  left_inv := arithmeticComap_symm_apply n e
  right_inv := arithmeticComap_apply_symm n e
  continuous_toFun := continuous_arithmeticComap n e
  continuous_invFun := continuous_arithmeticComap n e.symm

@[simp] theorem evaluate_arithmeticEquiv (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) (x : AdelicGL K n) :
    evaluate K n (arithmeticEquiv n e f) x = evaluate L n f (adelicEquiv n e x) := rfl

@[simp] theorem evaluate_arithmeticEquiv_symm (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions K n) (x : AdelicGL L n) :
    evaluate L n ((arithmeticEquiv n e).symm f) x =
      evaluate K n f (adelicEquiv n e.symm x) := rfl

/-- Full right translation is intertwined through the actual arithmetic group map. -/
theorem arithmeticComap_rightAction (n : ℕ) (e : K ≃+* L) (g : AdelicGL K n)
    (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e (continuousRightAction L n (adelicEquiv n e g) f) =
      continuousRightAction K n g (arithmeticComap n e f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evaluate L n f (adelicEquiv n e x * adelicEquiv n e g) =
    evaluate L n f (adelicEquiv n e (x * g))
  rw [map_mul]

/-- Finite-factor covariance uses the genuine factor inclusion. -/
theorem arithmeticComap_finite_rightAction (n : ℕ) (e : K ≃+* L)
    (g : FiniteAdelicGL K n) (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e
      (continuousRightAction L n (AdelicGL.ofFinite L n (finiteEquiv n e g)) f) =
    continuousRightAction K n (AdelicGL.ofFinite K n g) (arithmeticComap n e f) := by
  rw [← adelicEquiv_ofFinite]
  exact arithmeticComap_rightAction n e _ f

/-- Infinite-factor covariance uses the genuine factor inclusion. -/
theorem arithmeticComap_infinite_rightAction (n : ℕ) (e : K ≃+* L)
    (g : InfiniteAdelicGL K n) (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e
      (continuousRightAction L n (AdelicGL.ofInfinite L n (infiniteEquiv n e g)) f) =
    continuousRightAction K n (AdelicGL.ofInfinite K n g) (arithmeticComap n e f) := by
  rw [← adelicEquiv_ofInfinite]
  exact arithmeticComap_rightAction n e _ f

private theorem arithmeticComap_map_eq (n : ℕ) (e : K ≃+* L)
    (P : Submodule ℂ (ContinuousRationalFunctions L n))
    (Q : Submodule ℂ (ContinuousRationalFunctions K n))
    (h : ∀ f, arithmeticComap n e f ∈ Q ↔ f ∈ P) :
    P.map (arithmeticComap n e) = Q := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (h g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (arithmeticEquiv n e).surjective f
    exact ⟨g, (h g).mp hf, rfl⟩

/-- The actual scalar-idele character transforms by arithmetic idele transport. -/
@[simp] theorem centralIdeleCharacter_comap (e : K ≃+* L) (χ : HeckeCharacter L)
    (z : Ideles K) :
    centralIdeleCharacter K (HeckeCharacter.comap e χ) z =
      centralIdeleCharacter L χ (AdelicFunctoriality.ideleEquiv e z) := rfl

/-- Arithmetic pullback preserves and reflects the specified central-character equation. -/
theorem arithmeticComap_mem_centralCharacter_iff (n : ℕ) (e : K ≃+* L)
    (χ : HeckeCharacter L) (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e f ∈
        (centralCharacterSubrepresentation K n (HeckeCharacter.comap e χ)).toSubmodule ↔
      f ∈ (centralCharacterSubrepresentation L n χ).toSubmodule := by
  change (∀ z x,
    evaluate K n (arithmeticComap n e f) (AdelicGL.scalar K n z * x) =
      (centralIdeleCharacter K (HeckeCharacter.comap e χ) z : ℂ) *
        evaluate K n (arithmeticComap n e f) x) ↔
    (∀ z x, evaluate L n f (AdelicGL.scalar L n z * x) =
      (centralIdeleCharacter L χ z : ℂ) * evaluate L n f x)
  simp only [evaluate_arithmeticComap, map_mul, adelicEquiv_scalar,
    centralIdeleCharacter_comap]
  constructor
  · intro h z x
    obtain ⟨w, rfl⟩ := (AdelicFunctoriality.ideleEquiv e).surjective z
    obtain ⟨y, rfl⟩ := (adelicEquiv n e).surjective x
    exact h w y
  · intro h z x
    exact h _ _

/-- Actual arithmetic pullback restricted to the corresponding central-character spaces. -/
def centralCharacterEquiv (n : ℕ) (e : K ≃+* L) (χ : HeckeCharacter L) :
    CentralCharacterFunctions L n χ ≃L[ℂ]
      CentralCharacterFunctions K n (HeckeCharacter.comap e χ) :=
  (arithmeticEquiv n e).ofSubmodules _ _
    (arithmeticComap_map_eq n e _ _ (arithmeticComap_mem_centralCharacter_iff n e χ))

@[simp] theorem evaluate_centralCharacterEquiv (n : ℕ) (e : K ≃+* L)
    (χ : HeckeCharacter L) (f : CentralCharacterFunctions L n χ) (x : AdelicGL K n) :
    evaluate K n (centralCharacterEquiv n e χ f).val x =
      evaluate L n f.val (adelicEquiv n e x) := rfl

/-- The restricted equivalence intertwines the actual full right representations. -/
theorem centralCharacterEquiv_rightAction (n : ℕ) (e : K ≃+* L)
    (χ : HeckeCharacter L) (g : AdelicGL K n) (f : CentralCharacterFunctions L n χ) :
    centralCharacterEquiv n e χ
        (centralCharacterRightAction L n χ (adelicEquiv n e g) f) =
      centralCharacterRightAction K n (HeckeCharacter.comap e χ) g
        (centralCharacterEquiv n e χ f) := by
  apply Subtype.ext
  exact arithmeticComap_rightAction n e g f.val

/-- Fixed vectors correspond for the actual preimage finite subgroup. -/
theorem arithmeticComap_mem_level_iff (n : ℕ) (e : K ≃+* L)
    (U : Subgroup (FiniteAdelicGL L n)) (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e f ∈ levelSubmodule K n (U.comap (finiteEquiv n e).toMonoidHom) ↔
      f ∈ levelSubmodule L n U := by
  constructor
  · intro hf u
    let v : U.comap (finiteEquiv n e).toMonoidHom :=
      ⟨(finiteEquiv n e).symm u, by
        change finiteEquiv n e ((finiteEquiv n e).symm u) ∈ U
        simpa only [ContinuousMulEquiv.apply_symm_apply] using u.property⟩
    apply (arithmeticEquiv n e).injective
    change arithmeticComap n e
      (continuousRightAction L n (AdelicGL.ofFinite L n u) f) = arithmeticComap n e f
    have h := arithmeticComap_finite_rightAction n e v.val f
    simpa only [v, ContinuousMulEquiv.apply_symm_apply] using h.trans (hf v)
  · intro hf v
    have h := congrArg (arithmeticComap n e) (hf ⟨finiteEquiv n e v, v.property⟩)
    exact (arithmeticComap_finite_rightAction n e v.val f).symm.trans h

/-- Pullback on the actual finite-level fixed submodules, with induced topologies. -/
def levelEquiv (n : ℕ) (e : K ≃+* L) (U : Subgroup (FiniteAdelicGL L n)) :
    levelSubmodule L n U ≃L[ℂ]
      levelSubmodule K n (U.comap (finiteEquiv n e).toMonoidHom) :=
  (arithmeticEquiv n e).ofSubmodules _ _
    (arithmeticComap_map_eq n e _ _ (arithmeticComap_mem_level_iff n e U))

@[simp] theorem evaluate_levelEquiv (n : ℕ) (e : K ≃+* L)
    (U : Subgroup (FiniteAdelicGL L n)) (f : levelSubmodule L n U) (x : AdelicGL K n) :
    evaluate K n (levelEquiv n e U f).val x =
      evaluate L n f.val (adelicEquiv n e x) := rfl

/-- The preimage level is open exactly when the original level is open. -/
theorem isOpen_finite_comap_iff (n : ℕ) (e : K ≃+* L)
    (U : Subgroup (FiniteAdelicGL L n)) :
    IsOpen (U.comap (finiteEquiv n e).toMonoidHom : Set (FiniteAdelicGL K n)) ↔
      IsOpen (U : Set (FiniteAdelicGL L n)) :=
  (finiteEquiv n e).toHomeomorph.isOpen_preimage

/-- The preimage level is compact exactly when the original level is compact. -/
theorem isCompact_finite_comap_iff (n : ℕ) (e : K ≃+* L)
    (U : Subgroup (FiniteAdelicGL L n)) :
    IsCompact (U.comap (finiteEquiv n e).toMonoidHom : Set (FiniteAdelicGL K n)) ↔
      IsCompact (U : Set (FiniteAdelicGL L n)) :=
  (finiteEquiv n e).toHomeomorph.isCompact_preimage

theorem hasFiniteLevel_arithmeticComap (n : ℕ) (e : K ≃+* L)
    {f : ContinuousRationalFunctions L n} (hf : HasFiniteLevel L n f) :
    HasFiniteLevel K n (arithmeticComap n e f) := by
  obtain ⟨U, ho, hc, hf⟩ := hf
  exact ⟨U.comap (finiteEquiv n e).toMonoidHom,
    (isOpen_finite_comap_iff n e U).mpr ho,
    (isCompact_finite_comap_iff n e U).mpr hc,
    (arithmeticComap_mem_level_iff n e U f).mpr hf⟩

/-- Existence of an actual compact open finite level is preserved and reflected. -/
theorem hasFiniteLevel_arithmeticComap_iff (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    HasFiniteLevel K n (arithmeticComap n e f) ↔ HasFiniteLevel L n f := by
  constructor
  · intro hf
    simpa only [arithmeticComap_symm_apply] using hasFiniteLevel_arithmeticComap n e.symm hf
  · exact hasFiniteLevel_arithmeticComap n e

/-- The corresponding infinite-subgroup orbit span is exactly the linear image. -/
theorem infiniteOrbitSpan_arithmeticComap (n : ℕ) (e : K ≃+* L)
    (U : Subgroup (InfiniteAdelicGL L n)) (f : ContinuousRationalFunctions L n) :
    infiniteOrbitSpan K n (U.comap (infiniteEquiv n e).toMonoidHom)
        (arithmeticComap n e f) =
      (infiniteOrbitSpan L n U f).map (arithmeticComap n e) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change continuousRightAction K n (AdelicGL.ofInfinite K n v.val)
      (arithmeticComap n e f) ∈ _
    rw [← arithmeticComap_infinite_rightAction]
    exact Submodule.mem_map_of_mem (Submodule.subset_span
      ⟨⟨infiniteEquiv n e v, v.property⟩, rfl⟩)
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    change arithmeticComap n e
      (continuousRightAction L n (AdelicGL.ofInfinite L n u.val) f) ∈
        infiniteOrbitSpan K n (U.comap (infiniteEquiv n e).toMonoidHom)
          (arithmeticComap n e f)
    let v : U.comap (infiniteEquiv n e).toMonoidHom :=
      ⟨(infiniteEquiv n e).symm u, by
        change infiniteEquiv n e ((infiniteEquiv n e).symm u) ∈ U
        simpa only [ContinuousMulEquiv.apply_symm_apply] using u.property⟩
    have h := arithmeticComap_infinite_rightAction n e v.val f
    have hv : continuousRightAction K n (AdelicGL.ofInfinite K n v.val)
        (arithmeticComap n e f) ∈
      infiniteOrbitSpan K n (U.comap (infiniteEquiv n e).toMonoidHom)
        (arithmeticComap n e f) := Submodule.subset_span ⟨v, rfl⟩
    rw [← h] at hv
    simpa only [v, ContinuousMulEquiv.apply_symm_apply] using hv

/-- Pullback on the actual corresponding infinite-subgroup orbit spans. -/
def infiniteOrbitEquiv (n : ℕ) (e : K ≃+* L)
    (U : Subgroup (InfiniteAdelicGL L n)) (f : ContinuousRationalFunctions L n) :
    infiniteOrbitSpan L n U f ≃L[ℂ]
      infiniteOrbitSpan K n (U.comap (infiniteEquiv n e).toMonoidHom)
        (arithmeticComap n e f) :=
  (arithmeticEquiv n e).ofSubmodules _ _ (infiniteOrbitSpan_arithmeticComap n e U f).symm

@[simp] theorem evaluate_infiniteOrbitEquiv (n : ℕ) (e : K ≃+* L)
    (U : Subgroup (InfiniteAdelicGL L n)) (f : ContinuousRationalFunctions L n)
    (h : infiniteOrbitSpan L n U f) (x : AdelicGL K n) :
    evaluate K n (infiniteOrbitEquiv n e U f h).val x =
      evaluate L n h.val (adelicEquiv n e x) := rfl

/-- Subgroup finiteness is preserved and reflected for the corresponding subgroup. -/
theorem isInfiniteFinite_arithmeticComap_iff (n : ℕ) (e : K ≃+* L)
    (U : Subgroup (InfiniteAdelicGL L n)) (f : ContinuousRationalFunctions L n) :
    IsInfiniteFinite K n (U.comap (infiniteEquiv n e).toMonoidHom)
        (arithmeticComap n e f) ↔ IsInfiniteFinite L n U f :=
  (LinearMap.finite_iff_of_bijective
    (infiniteOrbitEquiv n e U f).toLinearMap
    (infiniteOrbitEquiv n e U f).bijective).symm

/-- Rational field automorphisms act by inverse arithmetic pullback on actual functions. -/
def galoisAut (n : ℕ) : (K ≃ₐ[ℚ] K) →*
    (ContinuousRationalFunctions K n ≃L[ℂ] ContinuousRationalFunctions K n) where
  toFun σ := arithmeticEquiv n σ.toRingEquiv.symm
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact arithmeticComap_refl n f
  map_mul' σ τ := by
    apply ContinuousLinearEquiv.ext
    funext f
    change arithmeticComap n (σ * τ).toRingEquiv.symm f =
      arithmeticComap n σ.toRingEquiv.symm (arithmeticComap n τ.toRingEquiv.symm f)
    exact arithmeticComap_trans n σ.toRingEquiv.symm τ.toRingEquiv.symm f

@[simp] theorem evaluate_galoisAut (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (f : ContinuousRationalFunctions K n) (x : AdelicGL K n) :
    evaluate K n (galoisAut n σ f) x =
      evaluate K n f (AdelicGLTransport.adelicAut n (σ⁻¹) x) := rfl

/-- An installable distributive left action, without a global action instance. -/
@[instance_reducible]
def galoisAction (n : ℕ) : DistribMulAction (K ≃ₐ[ℚ] K) (ContinuousRationalFunctions K n) where
  smul σ f := galoisAut n σ f
  one_smul f := by
    change galoisAut n 1 f = f
    rw [map_one]
    rfl
  mul_smul σ τ f := by
    change galoisAut n (σ * τ) f = galoisAut n σ (galoisAut n τ f)
    rw [map_mul]
    rfl
  smul_zero σ := map_zero (galoisAut n σ)
  smul_add σ := map_add (galoisAut n σ)

/-- Central characters transform by the same inverse-pullback Galois convention. -/
theorem galoisAut_mem_centralCharacter_iff (n : ℕ) (σ : K ≃ₐ[ℚ] K)
    (χ : HeckeCharacter K) (f : ContinuousRationalFunctions K n) :
    galoisAut n σ f ∈
        (centralCharacterSubrepresentation K n (HeckeCharacter.galoisAut σ χ)).toSubmodule ↔
      f ∈ (centralCharacterSubrepresentation K n χ).toSubmodule :=
  arithmeticComap_mem_centralCharacter_iff n σ.toRingEquiv.symm χ f

section CM
variable [NumberField.IsCMField K]

private theorem fieldComplexConj_trans :
    (NumberField.IsCMField.complexConj K).toRingEquiv.trans
      (NumberField.IsCMField.complexConj K).toRingEquiv = RingEquiv.refl K := by
  apply RingEquiv.ext
  intro x
  exact NumberField.IsCMField.complexConj_apply_apply K x

/-- Direct pullback along the actual CM involution, with complex values fixed. -/
def complexConj (n : ℕ) :
    ContinuousRationalFunctions K n ≃L[ℂ] ContinuousRationalFunctions K n :=
  arithmeticEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv

@[simp] theorem evaluate_complexConj (n : ℕ) (f : ContinuousRationalFunctions K n)
    (x : AdelicGL K n) :
    evaluate K n (complexConj n f) x =
      evaluate K n f (CMConjugation.adelicConj K n x) := by
  change evaluate K n f (adelicEquiv n _ x) = _
  rw [adelicEquiv_complexConj]

@[simp] theorem complexConj_complexConj (n : ℕ) (f : ContinuousRationalFunctions K n) :
    complexConj n (complexConj n f) = f := by
  change arithmeticComap n (NumberField.IsCMField.complexConj K).toRingEquiv
    (arithmeticComap n (NumberField.IsCMField.complexConj K).toRingEquiv f) = f
  rw [← arithmeticComap_trans, fieldComplexConj_trans, arithmeticComap_refl]

/-- The rational inverse-pullback convention reduces to direct CM pullback. -/
@[simp] theorem galoisAut_complexConj (n : ℕ) (f : ContinuousRationalFunctions K n) :
    galoisAut n ((NumberField.IsCMField.complexConj K).restrictScalars ℚ) f =
      complexConj n f := by
  have h : (NumberField.IsCMField.complexConj K).toRingEquiv.symm =
      (NumberField.IsCMField.complexConj K).toRingEquiv := by
    apply RingEquiv.ext
    intro x
    apply (NumberField.IsCMField.complexConj K).injective
    exact ((NumberField.IsCMField.complexConj K).apply_symm_apply x).trans
      (NumberField.IsCMField.complexConj_apply_apply K x).symm
  change arithmeticComap n (NumberField.IsCMField.complexConj K).toRingEquiv.symm f =
    complexConj n f
  rw [h]
  rfl

@[simp] theorem complexConj_mem_centralCharacter_iff (n : ℕ)
    (χ : HeckeCharacter K) (f : ContinuousRationalFunctions K n) :
    complexConj n f ∈
        (centralCharacterSubrepresentation K n χ.complexConj).toSubmodule ↔
      f ∈ (centralCharacterSubrepresentation K n χ).toSubmodule :=
  arithmeticComap_mem_centralCharacter_iff n _ χ f

@[simp] theorem hasFiniteLevel_complexConj_iff (n : ℕ)
    (f : ContinuousRationalFunctions K n) :
    HasFiniteLevel K n (complexConj n f) ↔ HasFiniteLevel K n f :=
  hasFiniteLevel_arithmeticComap_iff n _ f

private theorem infiniteEquiv_complexConj_involutive (n : ℕ) :
    Function.Involutive (infiniteEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv) := by
  intro g
  have h := congrArg (fun a : InfiniteAdelicGL K n ≃ₜ* InfiniteAdelicGL K n => a g)
    (infiniteEquiv_trans n (NumberField.IsCMField.complexConj K).toRingEquiv
      (NumberField.IsCMField.complexConj K).toRingEquiv)
  simpa only [fieldComplexConj_trans, infiniteEquiv_refl,
    ContinuousMulEquiv.refl_apply, ContinuousMulEquiv.trans_apply] using h.symm

/-- The genuine standard infinite compact subgroup is its own CM preimage. -/
theorem complexConj_comap_standardInfiniteCompact (n : ℕ) :
    (standardInfiniteCompact K n).comap
        (infiniteEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv).toMonoidHom =
      standardInfiniteCompact K n := by
  ext g
  change infiniteEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv g ∈
      standardInfiniteCompact K n ↔ g ∈ standardInfiniteCompact K n
  have hpres {x : InfiniteAdelicGL K n} (hx : x ∈ standardInfiniteCompact K n) :
      infiniteEquiv n (NumberField.IsCMField.complexConj K).toRingEquiv x ∈
        standardInfiniteCompact K n := by
    rw [infiniteEquiv_complexConj]
    exact CMConjugation.infiniteConj_mem_standardInfiniteCompact K n hx
  constructor
  · intro hg
    simpa only [infiniteEquiv_complexConj_involutive n g] using hpres hg
  · exact hpres

/-- CM pullback preserves and reflects finiteness for the actual standard compact. -/
@[simp] theorem isStandardInfiniteFinite_complexConj_iff (n : ℕ)
    (f : ContinuousRationalFunctions K n) :
    IsInfiniteFinite K n (standardInfiniteCompact K n) (complexConj n f) ↔
      IsInfiniteFinite K n (standardInfiniteCompact K n) f := by
  have h := isInfiniteFinite_arithmeticComap_iff n
    (NumberField.IsCMField.complexConj K).toRingEquiv (standardInfiniteCompact K n) f
  rwa [complexConj_comap_standardInfiniteCompact] at h

end CM
end Langlands.Automorphic.ContinuousRationalFunctions

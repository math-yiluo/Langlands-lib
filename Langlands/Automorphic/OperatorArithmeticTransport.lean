import Langlands.Automorphic.AutomorphicArithmeticTransport
import Langlands.Automorphic.ArithmeticTransportRelation

/-! # Arithmetic pullback of actual automorphic operator realizations

For a number-field isomorphism `e : K ≃+* L`, conjugation by arithmetic pullback identifies
the concrete automorphic operator algebras over `L` and `K`, and restricts to the stable
automorphic cores. Every actual operator realization over `L` therefore has an actual
image realization over `K`, which is its arithmetic transport in the sense of
`ArithmeticTransportRelation`. Irreducibility, central characters (through `χ ↦ χ ∘ e`)
and cuspidality are preserved and reflected.
-/

noncomputable section
universe uK uL uM

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands

/-- Image and preimage identify the invariant subspaces of two representations of different
monoids that are intertwined by a linear equivalence along a monoid isomorphism. -/
def covariantSubrepresentationOrderIso
    {G H V W : Type*} [Monoid G] [Monoid H]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ H W)
    (α : H ≃* G) (e : V ≃ₗ[ℂ] W)
    (hc : ∀ h f, τ h (e f) = e (ρ (α h) f)) :
    Subrepresentation ρ ≃o Subrepresentation τ where
  toFun P :=
    { toSubmodule := P.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule h _ hf := by
        change ∃ f, f ∈ P.toSubmodule ∧ e f = _ at hf
        obtain ⟨f, hf, rfl⟩ := hf
        rw [hc]
        exact Submodule.mem_map_of_mem (P.apply_mem_toSubmodule (α h) hf) }
  invFun Q :=
    { toSubmodule := Q.toSubmodule.comap e.toLinearMap
      apply_mem_toSubmodule g f hf := by
        change e (ρ g f) ∈ Q
        have hcov := hc (α.symm g) f
        rw [α.apply_symm_apply] at hcov
        rw [← hcov]
        exact Q.apply_mem_toSubmodule (α.symm g) hf }
  left_inv P := Subrepresentation.toSubmodule_injective
    ((Submodule.orderIsoMapComap e).symm_apply_apply P.toSubmodule)
  right_inv Q := Subrepresentation.toSubmodule_injective
    ((Submodule.orderIsoMapComap e).apply_symm_apply Q.toSubmodule)
  map_rel_iff' := (Submodule.orderIsoMapComap e).map_rel_iff

end Langlands

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions AdelicGLTransport

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

local instance operatorArithmeticRationalGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance operatorArithmeticContinuousGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance operatorArithmeticFiniteSmoothGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance operatorArithmeticFormGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance operatorArithmeticStableGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

section Generators

variable (n : ℕ) (e : K ≃+* L)

theorem finiteSmoothEquiv_finiteRightAction (d : FiniteAdelicGL K n)
    (f : FiniteSmoothRationalFunctions L n) :
    finiteSmoothEquiv n e (finiteSmoothFiniteRightAction L n (finiteEquiv n e d) f) =
      finiteSmoothFiniteRightAction K n d (finiteSmoothEquiv n e f) := by
  change finiteSmoothEquiv n e
      (finiteSmoothRightAction L n (AdelicGL.ofFinite L n (finiteEquiv n e d)) f) =
    finiteSmoothRightAction K n (AdelicGL.ofFinite K n d) (finiteSmoothEquiv n e f)
  rw [← adelicEquiv_ofFinite]
  exact finiteSmoothEquiv_rightAction n e _ f

theorem finiteSmoothEquiv_compactRightAction (k : standardInfiniteCompact K n)
    (f : FiniteSmoothRationalFunctions L n) :
    finiteSmoothEquiv n e (finiteSmoothCompactRightAction L n
        (ArchimedeanCompactTransport.compactEquiv n e k) f) =
      finiteSmoothCompactRightAction K n k (finiteSmoothEquiv n e f) := by
  change finiteSmoothEquiv n e
      (finiteSmoothRightAction L n (AdelicGL.ofInfinite L n (infiniteEquiv n e k.val)) f) =
    finiteSmoothRightAction K n (AdelicGL.ofInfinite K n k.val) (finiteSmoothEquiv n e f)
  rw [← adelicEquiv_ofInfinite]
  exact finiteSmoothEquiv_rightAction n e _ f

/-- Conjugation of ambient operators by arithmetic pullback. -/
def finiteSmoothArithmeticConjugation : FiniteSmoothEnd L n ≃ₐ[ℂ] FiniteSmoothEnd K n :=
  (finiteSmoothEquiv n e).toLinearEquiv.conjAlgEquiv ℂ

@[simp] theorem finiteSmoothArithmeticConjugation_apply (a : FiniteSmoothEnd L n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothArithmeticConjugation n e a f =
      finiteSmoothEquiv n e (a ((finiteSmoothEquiv n e).symm f)) := rfl

theorem finiteSmoothArithmeticConjugation_symm_apply (a : FiniteSmoothEnd K n)
    (f : FiniteSmoothRationalFunctions L n) :
    (finiteSmoothArithmeticConjugation n e).symm a f =
      (finiteSmoothEquiv n e).symm (a (finiteSmoothEquiv n e f)) := rfl

theorem finiteSmoothArithmeticConjugation_symm :
    (finiteSmoothArithmeticConjugation n e).symm = finiteSmoothArithmeticConjugation n e.symm := by
  apply AlgEquiv.ext
  intro a
  apply LinearMap.ext
  intro f
  rw [finiteSmoothArithmeticConjugation_symm_apply, finiteSmoothArithmeticConjugation_apply,
    finiteSmoothEquiv_symm, finiteSmoothEquiv_symm, RingEquiv.symm_symm]

theorem finiteSmoothArithmeticConjugation_finite (d : FiniteAdelicGL L n) :
    finiteSmoothArithmeticConjugation n e (finiteSmoothFiniteRightAction L n d) =
      finiteSmoothFiniteRightAction K n ((finiteEquiv n e).symm d) := by
  apply LinearMap.ext
  intro f
  rw [finiteSmoothArithmeticConjugation_apply]
  have h := finiteSmoothEquiv_finiteRightAction n e ((finiteEquiv n e).symm d)
    ((finiteSmoothEquiv n e).symm f)
  rwa [ContinuousMulEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply] at h

theorem finiteSmoothArithmeticConjugation_compact (k : standardInfiniteCompact L n) :
    finiteSmoothArithmeticConjugation n e (finiteSmoothCompactRightAction L n k) =
      finiteSmoothCompactRightAction K n
        ((ArchimedeanCompactTransport.compactEquiv n e).symm k) := by
  apply LinearMap.ext
  intro f
  rw [finiteSmoothArithmeticConjugation_apply]
  have h := finiteSmoothEquiv_compactRightAction n e
    ((ArchimedeanCompactTransport.compactEquiv n e).symm k) ((finiteSmoothEquiv n e).symm f)
  rwa [MulEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply] at h

theorem finiteSmoothArithmeticConjugation_differential
    (u : ArchimedeanGL.EnvelopingAlgebra L n) :
    finiteSmoothArithmeticConjugation n e (finiteSmoothEnvelopingAction L n u) =
      finiteSmoothEnvelopingAction K n
        ((ArchimedeanLieTransport.envelopingEquiv n e).symm u) := by
  apply LinearMap.ext
  intro f
  rw [finiteSmoothArithmeticConjugation_apply]
  have h := finiteSmoothEquiv_envelopingAction n e
    ((ArchimedeanLieTransport.envelopingEquiv n e).symm u) ((finiteSmoothEquiv n e).symm f)
  rwa [AlgEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply] at h

private theorem finiteSmoothArithmeticConjugation_mem (a : FiniteSmoothEnd L n)
    (ha : a ∈ automorphicOperatorAlgebra L n) :
    finiteSmoothArithmeticConjugation n e a ∈ automorphicOperatorAlgebra K n := by
  refine Algebra.adjoin_induction
    (p := fun a _ => finiteSmoothArithmeticConjugation n e a ∈ automorphicOperatorAlgebra K n)
    ?_ ?_ ?_ ?_ ha
  · rintro a ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩)
    · rw [finiteSmoothArithmeticConjugation_finite]
      exact Algebra.subset_adjoin (Or.inl (Or.inl ⟨_, rfl⟩))
    · rw [finiteSmoothArithmeticConjugation_compact]
      exact Algebra.subset_adjoin (Or.inl (Or.inr ⟨_, rfl⟩))
    · rw [finiteSmoothArithmeticConjugation_differential]
      exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
  · intro c
    rw [AlgEquiv.commutes]
    exact (automorphicOperatorAlgebra K n).algebraMap_mem c
  · intro _ _ _ _ hca hcb
    rw [map_add]
    exact (automorphicOperatorAlgebra K n).add_mem hca hcb
  · intro _ _ _ _ hca hcb
    rw [map_mul]
    exact (automorphicOperatorAlgebra K n).mul_mem hca hcb

/-- The concrete operator algebras correspond under arithmetic conjugation. -/
def operatorArithmeticConjugation :
    automorphicOperatorAlgebra L n ≃ₐ[ℂ] automorphicOperatorAlgebra K n where
  toFun a := ⟨finiteSmoothArithmeticConjugation n e a.val,
    finiteSmoothArithmeticConjugation_mem n e _ a.property⟩
  invFun a := ⟨(finiteSmoothArithmeticConjugation n e).symm a.val, by
    rw [finiteSmoothArithmeticConjugation_symm]
    exact finiteSmoothArithmeticConjugation_mem n e.symm _ a.property⟩
  left_inv a := Subtype.ext ((finiteSmoothArithmeticConjugation n e).symm_apply_apply a.val)
  right_inv a := Subtype.ext ((finiteSmoothArithmeticConjugation n e).apply_symm_apply a.val)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)
  map_add' a b := Subtype.ext (map_add _ a.val b.val)
  commutes' c := Subtype.ext (AlgEquiv.commutes _ c)

@[simp] theorem operatorArithmeticConjugation_val (a : automorphicOperatorAlgebra L n) :
    (operatorArithmeticConjugation n e a).val = finiteSmoothArithmeticConjugation n e a.val :=
  rfl

@[simp] theorem operatorArithmeticConjugation_symm_val (a : automorphicOperatorAlgebra K n) :
    ((operatorArithmeticConjugation n e).symm a).val =
      (finiteSmoothArithmeticConjugation n e).symm a.val := rfl

@[simp] theorem operatorArithmeticConjugation_finite (d : FiniteAdelicGL K n) :
    operatorArithmeticConjugation n e (finiteOperator L n (finiteEquiv n e d)) =
      finiteOperator K n d := by
  apply Subtype.ext
  change finiteSmoothArithmeticConjugation n e (finiteSmoothFiniteRightAction L n _) = _
  rw [finiteSmoothArithmeticConjugation_finite, ContinuousMulEquiv.symm_apply_apply]
  rfl

@[simp] theorem operatorArithmeticConjugation_compact (k : standardInfiniteCompact K n) :
    operatorArithmeticConjugation n e
        (compactOperator L n (ArchimedeanCompactTransport.compactEquiv n e k)) =
      compactOperator K n k := by
  apply Subtype.ext
  change finiteSmoothArithmeticConjugation n e (finiteSmoothCompactRightAction L n _) = _
  rw [finiteSmoothArithmeticConjugation_compact, MulEquiv.symm_apply_apply]
  rfl

@[simp] theorem operatorArithmeticConjugation_differential
    (u : ArchimedeanGL.EnvelopingAlgebra K n) :
    operatorArithmeticConjugation n e
        (differentialOperator L n (ArchimedeanLieTransport.envelopingEquiv n e u)) =
      differentialOperator K n u := by
  apply Subtype.ext
  change finiteSmoothArithmeticConjugation n e (finiteSmoothEnvelopingAction L n _) = _
  rw [finiteSmoothArithmeticConjugation_differential, AlgEquiv.symm_apply_apply]
  rfl

/-- Whole-algebra covariance of arithmetic pullback on finite-smooth functions. -/
theorem operatorAction_finiteSmoothEquiv (a : automorphicOperatorAlgebra L n)
    (f : FiniteSmoothRationalFunctions L n) :
    (operatorArithmeticConjugation n e a).val (finiteSmoothEquiv n e f) =
      finiteSmoothEquiv n e (a.val f) := by
  rw [operatorArithmeticConjugation_val, finiteSmoothArithmeticConjugation_apply,
    ContinuousLinearEquiv.symm_apply_apply]

end Generators

section Core

variable (n : ℕ) (e : K ≃+* L)

theorem mem_automorphicOperatorCore_finiteSmoothEquiv
    {f : FiniteSmoothRationalFunctions L n} (hf : f ∈ automorphicOperatorCore L n) :
    finiteSmoothEquiv n e f ∈ automorphicOperatorCore K n := by
  intro a
  have h := operatorAction_finiteSmoothEquiv n e ((operatorArithmeticConjugation n e).symm a) f
  rw [AlgEquiv.apply_symm_apply] at h
  rw [h]
  exact (finiteSmoothEquiv_mem_automorphic_iff n e _).mpr (hf _)

@[simp] theorem finiteSmoothEquiv_mem_automorphicOperatorCore_iff
    (f : FiniteSmoothRationalFunctions L n) :
    finiteSmoothEquiv n e f ∈ automorphicOperatorCore K n ↔
      f ∈ automorphicOperatorCore L n := by
  constructor
  · intro hf
    have h := mem_automorphicOperatorCore_finiteSmoothEquiv n e.symm hf
    rwa [← finiteSmoothEquiv_symm, ContinuousLinearEquiv.symm_apply_apply] at h
  · exact mem_automorphicOperatorCore_finiteSmoothEquiv n e

private theorem automorphicOperatorCore_map_finiteSmoothEquiv :
    (automorphicOperatorCore L n).toSubmodule.map (finiteSmoothEquiv n e).toLinearMap =
      (automorphicOperatorCore K n).toSubmodule := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact mem_automorphicOperatorCore_finiteSmoothEquiv n e hg
  · intro hf
    obtain ⟨g, rfl⟩ := (finiteSmoothEquiv n e).surjective f
    exact ⟨g, (finiteSmoothEquiv_mem_automorphicOperatorCore_iff n e g).mp hf, rfl⟩

namespace StableAutomorphicFunctions

/-- Arithmetic pullback restricted to the actual stable automorphic cores. -/
def arithmeticEquiv : StableAutomorphicFunctions L n ≃L[ℂ] StableAutomorphicFunctions K n :=
  (finiteSmoothEquiv n e).ofSubmodules _ _ (automorphicOperatorCore_map_finiteSmoothEquiv n e)

@[simp] theorem arithmeticEquiv_val (f : StableAutomorphicFunctions L n) :
    (arithmeticEquiv n e f).val = finiteSmoothEquiv n e f.val := rfl

@[simp] theorem arithmeticEquiv_refl (f : StableAutomorphicFunctions K n) :
    arithmeticEquiv n (RingEquiv.refl K) f = f := by
  apply Subtype.ext
  exact finiteSmoothEquiv_refl n f.val

theorem arithmeticEquiv_trans (a : L ≃+* M) (f : StableAutomorphicFunctions M n) :
    arithmeticEquiv n (e.trans a) f = arithmeticEquiv n e (arithmeticEquiv n a f) := by
  apply Subtype.ext
  exact finiteSmoothEquiv_trans n e a f.val

@[simp] theorem arithmeticEquiv_symm :
    (arithmeticEquiv n e).symm = arithmeticEquiv n e.symm := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  change (finiteSmoothEquiv n e).symm f.val = finiteSmoothEquiv n e.symm f.val
  rw [finiteSmoothEquiv_symm]

/-- Every actual operator is carried to its arithmetic conjugate. -/
theorem operatorAction_arithmeticEquiv (a : automorphicOperatorAlgebra L n)
    (f : StableAutomorphicFunctions L n) :
    stableAutomorphicAction K n (operatorArithmeticConjugation n e a) (arithmeticEquiv n e f) =
      arithmeticEquiv n e (stableAutomorphicAction L n a f) := by
  apply Subtype.ext
  exact operatorAction_finiteSmoothEquiv n e a f.val

theorem operatorAction_arithmeticEquiv_symm (a : automorphicOperatorAlgebra K n)
    (f : StableAutomorphicFunctions L n) :
    stableAutomorphicAction K n a (arithmeticEquiv n e f) =
      arithmeticEquiv n e
        (stableAutomorphicAction L n ((operatorArithmeticConjugation n e).symm a) f) := by
  have h := operatorAction_arithmeticEquiv n e ((operatorArithmeticConjugation n e).symm a) f
  rwa [AlgEquiv.apply_symm_apply] at h

theorem finiteAction_arithmeticEquiv (d : FiniteAdelicGL K n)
    (f : StableAutomorphicFunctions L n) :
    stableAutomorphicFiniteAction K n d (arithmeticEquiv n e f) =
      arithmeticEquiv n e (stableAutomorphicFiniteAction L n (finiteEquiv n e d) f) := by
  apply Subtype.ext
  exact (finiteSmoothEquiv_finiteRightAction n e d f.val).symm

theorem compactAction_arithmeticEquiv (k : standardInfiniteCompact K n)
    (f : StableAutomorphicFunctions L n) :
    stableAutomorphicCompactAction K n k (arithmeticEquiv n e f) =
      arithmeticEquiv n e (stableAutomorphicCompactAction L n
        (ArchimedeanCompactTransport.compactEquiv n e k) f) := by
  apply Subtype.ext
  exact (finiteSmoothEquiv_compactRightAction n e k f.val).symm

theorem envelopingAction_arithmeticEquiv (u : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : StableAutomorphicFunctions L n) :
    stableAutomorphicEnvelopingAction K n u (arithmeticEquiv n e f) =
      arithmeticEquiv n e (stableAutomorphicEnvelopingAction L n
        (ArchimedeanLieTransport.envelopingEquiv n e u) f) := by
  apply Subtype.ext
  exact (finiteSmoothEquiv_envelopingAction n e u f.val).symm

@[simp] theorem inclusion_arithmeticEquiv (f : StableAutomorphicFunctions L n) :
    stableAutomorphicInclusion K n (arithmeticEquiv n e f) =
      AutomorphicForms.arithmeticEquiv n e (stableAutomorphicInclusion L n f) := rfl

@[simp] theorem evaluate_arithmeticEquiv (f : StableAutomorphicFunctions L n)
    (g : AdelicGL K n) :
    evaluate K n (arithmeticEquiv n e f).val.val g =
      evaluate L n f.val.val (adelicEquiv n e g) := rfl

end StableAutomorphicFunctions
end Core

namespace OperatorRealization

variable {n : ℕ}

/-- Arithmetic pullback is an order equivalence of the embedded realizations. -/
def arithmeticComapOrderIso (e : K ≃+* L) :
    OperatorRealization L n ≃o OperatorRealization K n :=
  covariantSubrepresentationOrderIso (stableAutomorphicAction L n)
    (stableAutomorphicAction K n) (operatorArithmeticConjugation n e).symm.toMulEquiv
    (StableAutomorphicFunctions.arithmeticEquiv n e).toLinearEquiv
    (StableAutomorphicFunctions.operatorAction_arithmeticEquiv_symm n e)

variable (e : K ≃+* L) (S : OperatorRealization L n)

local instance operatorArithmeticSpaceGroup {F : Type*} [Field F] [NumberField F]
    (T : OperatorRealization F n) : AddCommGroup T.Space :=
  Submodule.addCommGroup _

/-- The actual image of the realized function space under arithmetic pullback. -/
def arithmeticComap : OperatorRealization K n := arithmeticComapOrderIso e S

@[simp] theorem arithmeticComap_toSubmodule :
    (S.arithmeticComap e).toSubmodule =
      S.toSubmodule.map (StableAutomorphicFunctions.arithmeticEquiv n e).toLinearMap := rfl

@[simp] theorem arithmeticComap_refl (T : OperatorRealization K n) :
    T.arithmeticComap (RingEquiv.refl K) = T := by
  apply Subrepresentation.toSubmodule_injective
  rw [arithmeticComap_toSubmodule]
  have h : (StableAutomorphicFunctions.arithmeticEquiv n (RingEquiv.refl K)).toLinearMap =
      LinearMap.id := by
    apply LinearMap.ext
    exact StableAutomorphicFunctions.arithmeticEquiv_refl n
  rw [h, Submodule.map_id]

theorem arithmeticComap_trans (a : L ≃+* M) (T : OperatorRealization M n) :
    T.arithmeticComap (e.trans a) = (T.arithmeticComap a).arithmeticComap e := by
  apply Subrepresentation.toSubmodule_injective
  rw [arithmeticComap_toSubmodule, arithmeticComap_toSubmodule, arithmeticComap_toSubmodule,
    ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  exact StableAutomorphicFunctions.arithmeticEquiv_trans n e a

@[simp] theorem arithmeticComap_symm_arithmeticComap :
    (S.arithmeticComap e).arithmeticComap e.symm = S := by
  rw [← arithmeticComap_trans, RingEquiv.symm_trans_self, arithmeticComap_refl]

@[simp] theorem arithmeticComap_arithmeticComap_symm (T : OperatorRealization K n) :
    (T.arithmeticComap e.symm).arithmeticComap e = T := by
  rw [← arithmeticComap_trans, RingEquiv.self_trans_symm, arithmeticComap_refl]

/-- Restrict the actual continuous pullback to the original space and its image. -/
def arithmeticComapEquiv : S.Space ≃L[ℂ] (S.arithmeticComap e).Space :=
  (StableAutomorphicFunctions.arithmeticEquiv n e).ofSubmodules _ _ rfl

@[simp] theorem arithmeticComapEquiv_val (f : S.Space) :
    (S.arithmeticComapEquiv e f).val = StableAutomorphicFunctions.arithmeticEquiv n e f.val :=
  rfl

theorem arithmeticComapEquiv_operatorAction (a : automorphicOperatorAlgebra K n) (f : S.Space) :
    (S.arithmeticComap e).representation a (S.arithmeticComapEquiv e f) =
      S.arithmeticComapEquiv e
        (S.representation ((operatorArithmeticConjugation n e).symm a) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.operatorAction_arithmeticEquiv_symm n e a f.val

theorem arithmeticComapEquiv_finite (d : FiniteAdelicGL K n) (f : S.Space) :
    (S.arithmeticComap e).finiteRepresentation d (S.arithmeticComapEquiv e f) =
      S.arithmeticComapEquiv e
        (S.finiteRepresentation (AdelicGLTransport.finiteEquiv n e d) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.finiteAction_arithmeticEquiv n e d f.val

theorem arithmeticComapEquiv_compact (k : standardInfiniteCompact K n) (f : S.Space) :
    (S.arithmeticComap e).compactRepresentation k (S.arithmeticComapEquiv e f) =
      S.arithmeticComapEquiv e
        (S.compactRepresentation (ArchimedeanCompactTransport.compactEquiv n e k) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.compactAction_arithmeticEquiv n e k f.val

theorem arithmeticComapEquiv_differential (u : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : S.Space) :
    (S.arithmeticComap e).envelopingAction u (S.arithmeticComapEquiv e f) =
      S.arithmeticComapEquiv e
        (S.envelopingAction (ArchimedeanLieTransport.envelopingEquiv n e u) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.envelopingAction_arithmeticEquiv n e u f.val

@[simp] theorem formInclusion_arithmeticComapEquiv (f : S.Space) :
    (S.arithmeticComap e).formInclusion (S.arithmeticComapEquiv e f) =
      AutomorphicForms.arithmeticEquiv n e (S.formInclusion f) := rfl

@[simp] theorem toContinuous_arithmeticComapEquiv (f : S.Space) :
    (S.arithmeticComap e).toContinuous (S.arithmeticComapEquiv e f) =
      ContinuousRationalFunctions.arithmeticComap n e (S.toContinuous f) := rfl

@[simp] theorem evaluate_arithmeticComapEquiv (f : S.Space) (g : AdelicGL K n) :
    evaluate K n ((S.arithmeticComap e).toContinuous (S.arithmeticComapEquiv e f)) g =
      evaluate L n (S.toContinuous f) (adelicEquiv n e g) := rfl

theorem arithmeticComapEquiv_symm_finite (d : FiniteAdelicGL K n)
    (f : (S.arithmeticComap e).Space) :
    (S.arithmeticComapEquiv e).symm ((S.arithmeticComap e).finiteRepresentation d f) =
      S.finiteRepresentation (AdelicGLTransport.finiteEquiv n e d)
        ((S.arithmeticComapEquiv e).symm f) := by
  have h := (congrArg (fun x => (S.arithmeticComap e).finiteRepresentation d x)
    ((S.arithmeticComapEquiv e).apply_symm_apply f)).symm.trans
      (S.arithmeticComapEquiv_finite e d ((S.arithmeticComapEquiv e).symm f))
  exact (congrArg (S.arithmeticComapEquiv e).symm h).trans
    ((S.arithmeticComapEquiv e).symm_apply_apply _)

theorem arithmeticComapEquiv_symm_compact (k : standardInfiniteCompact K n)
    (f : (S.arithmeticComap e).Space) :
    (S.arithmeticComapEquiv e).symm ((S.arithmeticComap e).compactRepresentation k f) =
      S.compactRepresentation (ArchimedeanCompactTransport.compactEquiv n e k)
        ((S.arithmeticComapEquiv e).symm f) := by
  have h := (congrArg (fun x => (S.arithmeticComap e).compactRepresentation k x)
    ((S.arithmeticComapEquiv e).apply_symm_apply f)).symm.trans
      (S.arithmeticComapEquiv_compact e k ((S.arithmeticComapEquiv e).symm f))
  exact (congrArg (S.arithmeticComapEquiv e).symm h).trans
    ((S.arithmeticComapEquiv e).symm_apply_apply _)

theorem arithmeticComapEquiv_symm_differential (u : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : (S.arithmeticComap e).Space) :
    (S.arithmeticComapEquiv e).symm ((S.arithmeticComap e).envelopingAction u f) =
      S.envelopingAction (ArchimedeanLieTransport.envelopingEquiv n e u)
        ((S.arithmeticComapEquiv e).symm f) := by
  have h := (congrArg (fun x => (S.arithmeticComap e).envelopingAction u x)
    ((S.arithmeticComapEquiv e).apply_symm_apply f)).symm.trans
      (S.arithmeticComapEquiv_differential e u ((S.arithmeticComapEquiv e).symm f))
  exact (congrArg (S.arithmeticComapEquiv e).symm h).trans
    ((S.arithmeticComapEquiv e).symm_apply_apply _)

/-- The image realization is the arithmetic transport of the original one along `e`. -/
theorem isArithmeticTransport_arithmeticComap :
    IsArithmeticTransport e (S.arithmeticComap e) S :=
  ⟨(S.arithmeticComapEquiv e).symm.toLinearEquiv, S.arithmeticComapEquiv_symm_finite e,
    S.arithmeticComapEquiv_symm_compact e, S.arithmeticComapEquiv_symm_differential e⟩

/-- Every realization over `K` has an actual arithmetic transport over `L`. -/
theorem exists_isArithmeticTransport (T : OperatorRealization K n) :
    ∃ U : OperatorRealization L n, IsArithmeticTransport e T U := by
  refine ⟨T.arithmeticComap e.symm, ?_⟩
  have h := (T.arithmeticComap e.symm).isArithmeticTransport_arithmeticComap e
  rw [arithmeticComap_arithmeticComap_symm] at h
  exact h

/-- A realization over `L` is the transport of `T` exactly when `T` is equivalent to its
arithmetic pullback. -/
theorem isArithmeticTransport_iff (T : OperatorRealization K n) :
    IsArithmeticTransport e T S ↔ Nonempty (T.Equivalence (S.arithmeticComap e)) := by
  have hS := S.isArithmeticTransport_arithmeticComap e
  constructor
  · intro h
    have h' := h.trans hS.symm
    rw [RingEquiv.self_trans_symm] at h'
    exact isArithmeticTransport_refl_iff.mp h'
  · intro h
    have h' := (isArithmeticTransport_refl_iff.mpr h).trans hS
    have he : (RingEquiv.refl K).trans e = e := by ext x; rfl
    rwa [he] at h'

/-- Arithmetic pullback identifies all invariant subspaces of the restricted actions. -/
def arithmeticComapSubrepresentationOrderIso :
    Subrepresentation S.representation ≃o
      Subrepresentation (S.arithmeticComap e).representation :=
  covariantSubrepresentationOrderIso S.representation (S.arithmeticComap e).representation
    (operatorArithmeticConjugation n e).symm.toMulEquiv
    (S.arithmeticComapEquiv e).toLinearEquiv (S.arithmeticComapEquiv_operatorAction e)

/-- Irreducibility for all three operator families is preserved and reflected. -/
theorem arithmeticComap_isIrreducible_iff :
    (S.arithmeticComap e).IsIrreducible ↔ S.IsIrreducible :=
  (S.arithmeticComapSubrepresentationOrderIso e).isSimpleOrder_iff.symm

/-- Central characters are transported by the Hecke-character comap. -/
theorem arithmeticComap_hasCentralCharacter_iff (χ : HeckeCharacter L) :
    (S.arithmeticComap e).HasCentralCharacter (HeckeCharacter.comap e χ) ↔
      S.HasCentralCharacter χ := by
  rw [hasCentralCharacter_iff, hasCentralCharacter_iff]
  constructor
  · intro ht f
    have hf := ht (S.arithmeticComapEquiv e f)
    rw [formInclusion_arithmeticComapEquiv,
      AutomorphicForms.arithmeticEquiv_mem_centralCharacter_iff] at hf
    exact hf
  · intro hs f
    obtain ⟨g, rfl⟩ := (S.arithmeticComapEquiv e).surjective f
    rw [formInclusion_arithmeticComapEquiv,
      AutomorphicForms.arithmeticEquiv_mem_centralCharacter_iff]
    exact hs g

section Cuspidal

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]

/-- The pullback has vanishing constant terms exactly when the source does. -/
theorem arithmeticComap_isCuspidal_iff : (S.arithmeticComap e).IsCuspidal ↔ S.IsCuspidal := by
  rw [isCuspidal_iff, isCuspidal_iff]
  constructor
  · intro ht f
    have hf := ht (S.arithmeticComapEquiv e f)
    rw [toContinuous_arithmeticComapEquiv,
      isCuspidal_arithmeticComap_iff n e (S.toContinuous f)] at hf
    exact hf
  · intro hs f
    obtain ⟨g, rfl⟩ := (S.arithmeticComapEquiv e).surjective f
    rw [toContinuous_arithmeticComapEquiv,
      isCuspidal_arithmeticComap_iff n e (S.toContinuous g)]
    exact hs g

end Cuspidal
end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
  [CompactSpace (AdeleQuotient M)] {r : ℕ} (e : K ≃+* L)

/-- Arithmetic pullback of an actual irreducible cuspidal realization of rank `r + 1`. -/
def arithmeticComap (S : CuspidalOperatorRealization L r) : CuspidalOperatorRealization K r where
  realization := S.realization.arithmeticComap e
  irreducible := (S.realization.arithmeticComap_isIrreducible_iff e).mpr S.irreducible
  cuspidal := (S.realization.arithmeticComap_isCuspidal_iff e).mpr S.cuspidal

@[simp] theorem arithmeticComap_realization (S : CuspidalOperatorRealization L r) :
    (S.arithmeticComap e).realization = S.realization.arithmeticComap e := rfl

@[simp] theorem arithmeticComap_symm_arithmeticComap (S : CuspidalOperatorRealization L r) :
    (S.arithmeticComap e).arithmeticComap e.symm = S := by
  cases S
  simp only [arithmeticComap, OperatorRealization.arithmeticComap_symm_arithmeticComap]

@[simp] theorem arithmeticComap_arithmeticComap_symm (T : CuspidalOperatorRealization K r) :
    (T.arithmeticComap e.symm).arithmeticComap e = T := by
  cases T
  simp only [arithmeticComap, OperatorRealization.arithmeticComap_arithmeticComap_symm]

theorem arithmeticComap_hasCentralCharacter_iff (S : CuspidalOperatorRealization L r)
    (χ : HeckeCharacter L) :
    (S.arithmeticComap e).HasCentralCharacter (HeckeCharacter.comap e χ) ↔
      S.HasCentralCharacter χ :=
  S.realization.arithmeticComap_hasCentralCharacter_iff e χ

theorem isArithmeticTransport_arithmeticComap (S : CuspidalOperatorRealization L r) :
    IsArithmeticTransport e (S.arithmeticComap e) S :=
  S.realization.isArithmeticTransport_arithmeticComap e

end CuspidalOperatorRealization
end Langlands.Automorphic

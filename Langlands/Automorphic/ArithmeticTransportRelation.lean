import Langlands.Global.ArchimedeanCompactTransport
import Langlands.Global.ArchimedeanLieTransport
import Langlands.Automorphic.CuspidalOperatorRealization
import Mathlib.FieldTheory.Galois.Basic

/-! # Arithmetic transport and Galois conjugacy between supplied full realizations

For a number-field isomorphism `e : K ≃+* L`, a realization `T` over `L` is the arithmetic
transport of a realization `S` over `K` when a linear equivalence carries the action of every
finite adelic element, standard compact element and enveloping-algebra element over `K` to
the action of its arithmetic image over `L`. For a Galois automorphism this is the
conjugate representation `π ∘ σ⁻¹`. The relation asserts no existence of a transported
realization.
-/

noncomputable section

universe uK uL uM

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

local instance arithmeticTransportRationalInvariantAddCommGroup
    {F : Type*} [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance arithmeticTransportContinuousRationalAddCommGroup
    {F : Type*} [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance arithmeticTransportFiniteSmoothRationalAddCommGroup
    {F : Type*} [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance arithmeticTransportAutomorphicFormsAddCommGroup
    {F : Type*} [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance arithmeticTransportStableAutomorphicAddCommGroup
    {F : Type*} [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M] {n : ℕ}

namespace OperatorRealization

local instance arithmeticTransportSpaceAddCommGroup {F : Type*} [Field F] [NumberField F]
    (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- All three transport equations for a supplied linear equivalence. The element acting on
the target is the arithmetic image of the element acting on the source. -/
def ArithmeticTransportEquations (e : K ≃+* L) (S : OperatorRealization K n)
    (T : OperatorRealization L n) (φ : S.Space ≃ₗ[ℂ] T.Space) : Prop :=
  (∀ (d : FiniteAdelicGL K n) (f : S.Space),
    φ (S.finiteRepresentation d f) =
      T.finiteRepresentation (AdelicGLTransport.finiteEquiv n e d) (φ f)) ∧
  (∀ (k : standardInfiniteCompact K n) (f : S.Space),
    φ (S.compactRepresentation k f) =
      T.compactRepresentation (ArchimedeanCompactTransport.compactEquiv n e k) (φ f)) ∧
  (∀ (a : ArchimedeanGL.EnvelopingAlgebra K n) (f : S.Space),
    φ (S.envelopingAction a f) =
      T.envelopingAction (ArchimedeanLieTransport.envelopingEquiv n e a) (φ f))

namespace ArithmeticTransportEquations

private theorem finiteEquiv_apply_symm (e : K ≃+* L) (d : FiniteAdelicGL L n) :
    AdelicGLTransport.finiteEquiv n e (AdelicGLTransport.finiteEquiv n e.symm d) = d := by
  rw [← ContinuousMulEquiv.trans_apply, ← AdelicGLTransport.finiteEquiv_trans,
    RingEquiv.symm_trans_self, AdelicGLTransport.finiteEquiv_refl]
  rfl

private theorem finiteEquiv_trans_apply (e : K ≃+* L) (f : L ≃+* M) (d : FiniteAdelicGL K n) :
    AdelicGLTransport.finiteEquiv n (e.trans f) d =
      AdelicGLTransport.finiteEquiv n f (AdelicGLTransport.finiteEquiv n e d) := by
  rw [AdelicGLTransport.finiteEquiv_trans]
  rfl

/-- The identity field map with the identity linear equivalence. -/
theorem refl (S : OperatorRealization K n) :
    ArithmeticTransportEquations (RingEquiv.refl K) S S (LinearEquiv.refl ℂ S.Space) := by
  refine ⟨fun d f => ?_, fun k f => ?_, fun a f => ?_⟩
  · have h : AdelicGLTransport.finiteEquiv n (RingEquiv.refl K) d = d := by
      rw [AdelicGLTransport.finiteEquiv_refl]
      rfl
    exact congrArg (fun x => S.finiteRepresentation x f) h.symm
  · exact congrArg (fun x => S.compactRepresentation x f)
      (ArchimedeanCompactTransport.compactEquiv_refl n k).symm
  · have h : ArchimedeanLieTransport.envelopingEquiv n (RingEquiv.refl K) a = a := by
      rw [ArchimedeanLieTransport.envelopingEquiv_refl]
      rfl
    exact congrArg (fun x => S.envelopingAction x f) h.symm

/-- Successive transports compose along the composite field isomorphism. -/
theorem trans {e : K ≃+* L} {e' : L ≃+* M} {S : OperatorRealization K n}
    {T : OperatorRealization L n} {U : OperatorRealization M n}
    {φ : S.Space ≃ₗ[ℂ] T.Space} {ψ : T.Space ≃ₗ[ℂ] U.Space}
    (hφ : ArithmeticTransportEquations e S T φ) (hψ : ArithmeticTransportEquations e' T U ψ) :
    ArithmeticTransportEquations (e.trans e') S U (φ.trans ψ) := by
  refine ⟨fun d f => ?_, fun k f => ?_, fun a f => ?_⟩
  · exact (congrArg ψ (hφ.1 d f)).trans ((hψ.1 _ (φ f)).trans
      (congrArg (fun x => U.finiteRepresentation x (ψ (φ f)))
        (finiteEquiv_trans_apply e e' d).symm))
  · exact (congrArg ψ (hφ.2.1 k f)).trans ((hψ.2.1 _ (φ f)).trans
      (congrArg (fun x => U.compactRepresentation x (ψ (φ f)))
        (ArchimedeanCompactTransport.compactEquiv_trans n e e' k).symm))
  · have h : ArchimedeanLieTransport.envelopingEquiv n (e.trans e') a =
        ArchimedeanLieTransport.envelopingEquiv n e'
          (ArchimedeanLieTransport.envelopingEquiv n e a) := by
      rw [ArchimedeanLieTransport.envelopingEquiv_trans]
      rfl
    exact (congrArg ψ (hφ.2.2 a f)).trans ((hψ.2.2 _ (φ f)).trans
      (congrArg (fun x => U.envelopingAction x (ψ (φ f))) h.symm))

/-- The inverse linear equivalence transports back along the inverse field isomorphism. -/
theorem symm {e : K ≃+* L} {S : OperatorRealization K n} {T : OperatorRealization L n}
    {φ : S.Space ≃ₗ[ℂ] T.Space} (hφ : ArithmeticTransportEquations e S T φ) :
    ArithmeticTransportEquations e.symm T S φ.symm := by
  refine ⟨fun d f => ?_, fun k f => ?_, fun a f => ?_⟩
  · apply φ.injective
    have h : T.finiteRepresentation
        (AdelicGLTransport.finiteEquiv n e (AdelicGLTransport.finiteEquiv n e.symm d))
          (φ (φ.symm f)) = T.finiteRepresentation d f :=
      congrArg₂ (fun x y => T.finiteRepresentation x y) (finiteEquiv_apply_symm e d)
        (φ.apply_symm_apply f)
    exact (φ.apply_symm_apply _).trans (h.symm.trans (hφ.1 _ _).symm)
  · apply φ.injective
    have h : T.compactRepresentation
        (ArchimedeanCompactTransport.compactEquiv n e
          (ArchimedeanCompactTransport.compactEquiv n e.symm k))
          (φ (φ.symm f)) = T.compactRepresentation k f :=
      congrArg₂ (fun x y => T.compactRepresentation x y)
        (ArchimedeanCompactTransport.compactEquiv_apply_symm n e k) (φ.apply_symm_apply f)
    exact (φ.apply_symm_apply _).trans (h.symm.trans (hφ.2.1 _ _).symm)
  · apply φ.injective
    have ha : ArchimedeanLieTransport.envelopingEquiv n e
        (ArchimedeanLieTransport.envelopingEquiv n e.symm a) = a := by
      rw [ArchimedeanLieTransport.envelopingEquiv_symm]
      exact AlgEquiv.apply_symm_apply _ a
    have h : T.envelopingAction
        (ArchimedeanLieTransport.envelopingEquiv n e
          (ArchimedeanLieTransport.envelopingEquiv n e.symm a))
          (φ (φ.symm f)) = T.envelopingAction a f :=
      congrArg₂ (fun x y => T.envelopingAction x y) ha (φ.apply_symm_apply f)
    exact (φ.apply_symm_apply _).trans (h.symm.trans (hφ.2.2 _ _).symm)

/-- For the identity field map the equations are exactly the full generator criterion. -/
theorem refl_iff {S T : OperatorRealization K n} (φ : S.Space ≃ₗ[ℂ] T.Space) :
    ArithmeticTransportEquations (RingEquiv.refl K) S T φ ↔
      (∀ d f, φ (S.finiteRepresentation d f) = T.finiteRepresentation d (φ f)) ∧
      (∀ k f, φ (S.compactRepresentation k f) = T.compactRepresentation k (φ f)) ∧
      (∀ a f, φ (S.envelopingAction a f) = T.envelopingAction a (φ f)) := by
  have hd : ∀ d : FiniteAdelicGL K n, AdelicGLTransport.finiteEquiv n (RingEquiv.refl K) d = d :=
    fun d => by rw [AdelicGLTransport.finiteEquiv_refl]; rfl
  have hk := ArchimedeanCompactTransport.compactEquiv_refl (K := K) n
  have ha : ∀ a : ArchimedeanGL.EnvelopingAlgebra K n,
      ArchimedeanLieTransport.envelopingEquiv n (RingEquiv.refl K) a = a :=
    fun a => by rw [ArchimedeanLieTransport.envelopingEquiv_refl]; rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun d f => (h1 d f).trans ?_, fun k f => (h2 k f).trans ?_,
      fun a f => (h3 a f).trans ?_⟩
    · exact congrArg (fun x => T.finiteRepresentation x (φ f)) (hd d)
    · exact congrArg (fun x => T.compactRepresentation x (φ f)) (hk k)
    · exact congrArg (fun x => T.envelopingAction x (φ f)) (ha a)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun d f => (h1 d f).trans ?_, fun k f => (h2 k f).trans ?_,
      fun a f => (h3 a f).trans ?_⟩
    · exact congrArg (fun x => T.finiteRepresentation x (φ f)) (hd d).symm
    · exact congrArg (fun x => T.compactRepresentation x (φ f)) (hk k).symm
    · exact congrArg (fun x => T.envelopingAction x (φ f)) (ha a).symm

end ArithmeticTransportEquations

/-- A relation on supplied actual full realizations over two number fields, asserting no
existence of a transported realization. -/
def IsArithmeticTransport (e : K ≃+* L) (S : OperatorRealization K n)
    (T : OperatorRealization L n) : Prop :=
  ∃ φ : S.Space ≃ₗ[ℂ] T.Space, ArithmeticTransportEquations e S T φ

namespace IsArithmeticTransport

theorem refl (S : OperatorRealization K n) : IsArithmeticTransport (RingEquiv.refl K) S S :=
  ⟨_, ArithmeticTransportEquations.refl S⟩

theorem trans {e : K ≃+* L} {e' : L ≃+* M} {S : OperatorRealization K n}
    {T : OperatorRealization L n} {U : OperatorRealization M n}
    (h : IsArithmeticTransport e S T) (h' : IsArithmeticTransport e' T U) :
    IsArithmeticTransport (e.trans e') S U := by
  rcases h with ⟨φ, hφ⟩
  rcases h' with ⟨ψ, hψ⟩
  exact ⟨φ.trans ψ, hφ.trans hψ⟩

theorem symm {e : K ≃+* L} {S : OperatorRealization K n} {T : OperatorRealization L n}
    (h : IsArithmeticTransport e S T) : IsArithmeticTransport e.symm T S := by
  rcases h with ⟨φ, hφ⟩
  exact ⟨φ.symm, hφ.symm⟩

end IsArithmeticTransport

/-- Transport along the identity field map is exactly full-operator equivalence. -/
theorem isArithmeticTransport_refl_iff {S T : OperatorRealization K n} :
    IsArithmeticTransport (RingEquiv.refl K) S T ↔ Nonempty (S.Equivalence T) := by
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨hd, hk, ha⟩ := (ArithmeticTransportEquations.refl_iff φ).mp hφ
    exact ⟨Equivalence.ofGenerators φ hd hk ha⟩
  · rintro ⟨q⟩
    exact ⟨q.toLinearEquiv, (ArithmeticTransportEquations.refl_iff _).mpr
      ⟨Intertwiner.finite q.toIntertwiningMap, Intertwiner.compact q.toIntertwiningMap,
        Intertwiner.differential q.toIntertwiningMap⟩⟩

/-- Transport in both arguments uses full equivalences, not finite restrictions. -/
theorem isArithmeticTransport_congr {e : K ≃+* L} {S S' : OperatorRealization K n}
    {T T' : OperatorRealization L n}
    (hS : Nonempty (S.Equivalence S')) (hT : Nonempty (T.Equivalence T')) :
    IsArithmeticTransport e S T ↔ IsArithmeticTransport e S' T' := by
  have hS' := isArithmeticTransport_refl_iff.mpr hS
  have hT' := isArithmeticTransport_refl_iff.mpr hT
  have hl : ((RingEquiv.refl K).symm.trans e).trans (RingEquiv.refl L) = e := by
    ext x; rfl
  have hr : ((RingEquiv.refl K).trans e).trans (RingEquiv.refl L).symm = e := by
    ext x; rfl
  constructor
  · intro h
    have h' := (hS'.symm.trans h).trans hT'
    rwa [hl] at h'
  · intro h
    have h' := (hS'.trans h).trans hT'.symm
    rwa [hr] at h'

/-- A fixed field map and source have at most one target class. -/
theorem IsArithmeticTransport.target_equivalent {e : K ≃+* L} {S : OperatorRealization K n}
    {T U : OperatorRealization L n}
    (h : IsArithmeticTransport e S T) (h' : IsArithmeticTransport e S U) :
    Nonempty (T.Equivalence U) := by
  apply isArithmeticTransport_refl_iff.mp
  have h'' := h.symm.trans h'
  rwa [RingEquiv.symm_trans_self] at h''

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
  [CompactSpace (AdeleQuotient M)] {r : ℕ}

/-- The same relation on actual positive-rank irreducible cuspidal objects. -/
abbrev IsArithmeticTransport (e : K ≃+* L) (S : CuspidalOperatorRealization K r)
    (T : CuspidalOperatorRealization L r) : Prop :=
  OperatorRealization.IsArithmeticTransport e S.realization T.realization

theorem isArithmeticTransport_congr {e : K ≃+* L} {S S' : CuspidalOperatorRealization K r}
    {T T' : CuspidalOperatorRealization L r}
    (hS : Nonempty (S.Equivalence S')) (hT : Nonempty (T.Equivalence T')) :
    IsArithmeticTransport e S T ↔ IsArithmeticTransport e S' T' :=
  OperatorRealization.isArithmeticTransport_congr hS hT

namespace IsoClass

/-- Descent to the existing full cuspidal classes, with no chosen representative. -/
def IsArithmeticTransport (e : K ≃+* L) (c : IsoClass K r) (d : IsoClass L r) : Prop :=
  Quotient.liftOn₂ c d
    (fun S T => CuspidalOperatorRealization.IsArithmeticTransport e S T)
    (fun _ _ _ _ hS hT => propext (isArithmeticTransport_congr hS hT))

@[simp]
theorem isArithmeticTransport_isoClass_iff (e : K ≃+* L) (S : CuspidalOperatorRealization K r)
    (T : CuspidalOperatorRealization L r) :
    IsArithmeticTransport e S.isoClass T.isoClass ↔
      CuspidalOperatorRealization.IsArithmeticTransport e S T := Iff.rfl

/-- The complete representative criterion, with all three equations on a supplied actual
linear equivalence. -/
theorem isArithmeticTransport_iff (e : K ≃+* L) (c : IsoClass K r) (d : IsoClass L r) :
    IsArithmeticTransport e c d ↔
      ∀ (S : CuspidalOperatorRealization K r) (T : CuspidalOperatorRealization L r),
        S.isoClass = c → T.isoClass = d →
          ∃ φ : S.realization.Space ≃ₗ[ℂ] T.realization.Space,
            OperatorRealization.ArithmeticTransportEquations e S.realization T.realization φ := by
  refine Quotient.inductionOn₂ c d ?_
  intro S T
  constructor
  · intro h S' T' hS hT
    exact (isArithmeticTransport_congr ((S'.isoClass_eq_iff S).mp hS)
      ((T'.isoClass_eq_iff T).mp hT)).mpr h
  · intro h
    exact h S T rfl rfl

theorem isArithmeticTransport_refl_iff (c d : IsoClass K r) :
    IsArithmeticTransport (RingEquiv.refl K) c d ↔ c = d := by
  refine Quotient.inductionOn₂ c d ?_
  intro S T
  exact OperatorRealization.isArithmeticTransport_refl_iff.trans (S.isoClass_eq_iff T).symm

theorem IsArithmeticTransport.refl (c : IsoClass K r) :
    IsArithmeticTransport (RingEquiv.refl K) c c :=
  (isArithmeticTransport_refl_iff c c).mpr rfl

theorem IsArithmeticTransport.trans {e : K ≃+* L} {e' : L ≃+* M} {c : IsoClass K r}
    {d : IsoClass L r} {c' : IsoClass M r}
    (h : IsArithmeticTransport e c d) (h' : IsArithmeticTransport e' d c') :
    IsArithmeticTransport (e.trans e') c c' := by
  revert h h'
  refine Quotient.inductionOn₃ c d c' ?_
  intro S T U h h'
  exact OperatorRealization.IsArithmeticTransport.trans h h'

theorem IsArithmeticTransport.symm {e : K ≃+* L} {c : IsoClass K r} {d : IsoClass L r}
    (h : IsArithmeticTransport e c d) : IsArithmeticTransport e.symm d c := by
  revert h
  refine Quotient.inductionOn₂ c d ?_
  intro S T h
  exact OperatorRealization.IsArithmeticTransport.symm h

/-- A fixed field map and source class have at most one target class. -/
theorem IsArithmeticTransport.target_unique {e : K ≃+* L} {c : IsoClass K r}
    {d d' : IsoClass L r} (h : IsArithmeticTransport e c d)
    (h' : IsArithmeticTransport e c d') : d = d' := by
  apply (isArithmeticTransport_refl_iff d d').mp
  have h'' := h.symm.trans h'
  rwa [RingEquiv.symm_trans_self] at h''

section Galois

variable {F : Type*} [Field F] [Algebra F K]

/-- `d` is the conjugate of `c` by the Galois automorphism `σ`: it is the arithmetic
transport of `c` along `σ`, so its action of `g` is that of `σ⁻¹ g` on `c`. -/
abbrev IsGaloisConjugate (σ : K ≃ₐ[F] K) (c d : IsoClass K r) : Prop :=
  IsArithmeticTransport σ.toRingEquiv c d

/-- The class is isomorphic to its conjugate by `σ`. -/
abbrev IsGaloisStable (σ : K ≃ₐ[F] K) (c : IsoClass K r) : Prop :=
  IsGaloisConjugate σ c c

theorem isGaloisStable_one (c : IsoClass K r) : IsGaloisStable (1 : K ≃ₐ[F] K) c :=
  IsArithmeticTransport.refl c

theorem IsGaloisStable.inv {σ : K ≃ₐ[F] K} {c : IsoClass K r} (h : IsGaloisStable σ c) :
    IsGaloisStable σ⁻¹ c :=
  IsArithmeticTransport.symm h

theorem IsGaloisStable.mul {σ τ : K ≃ₐ[F] K} {c : IsoClass K r}
    (hσ : IsGaloisStable σ c) (hτ : IsGaloisStable τ c) : IsGaloisStable (σ * τ) c := by
  have h := IsArithmeticTransport.trans hτ hσ
  exact h

end Galois

end IsoClass
end CuspidalOperatorRealization
end Langlands.Automorphic

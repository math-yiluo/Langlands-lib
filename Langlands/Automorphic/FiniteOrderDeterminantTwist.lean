import Langlands.Global.HeckeCharacterFiniteOrder
import Langlands.Automorphic.CuspidalOperatorRealization

/-! # Finite-order determinant twists between supplied full realizations -/

noncomputable section

universe u

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance finiteOrderTwistRationalInvariantAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance finiteOrderTwistContinuousRationalAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance finiteOrderTwistFiniteSmoothRationalAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance finiteOrderTwistAutomorphicFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance finiteOrderTwistStableAutomorphicAddCommGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- The actual determinant character, coerced from complex units to a scalar. -/
def determinantTwistScalar (χ : HeckeCharacter F) (g : AdelicGL F n) : ℂ :=
  χ.onIdeles (AdelicGL.determinant F n g)

@[simp]
theorem determinantTwistScalar_one (g : AdelicGL F n) :
    determinantTwistScalar (1 : HeckeCharacter F) g = 1 := rfl

@[simp]
theorem determinantTwistScalar_mul (χ ψ : HeckeCharacter F) (g : AdelicGL F n) :
    determinantTwistScalar (χ * ψ) g =
      determinantTwistScalar χ g * determinantTwistScalar ψ g := rfl

@[simp]
theorem determinantTwistScalar_inv (χ : HeckeCharacter F) (g : AdelicGL F n) :
    determinantTwistScalar χ⁻¹ g = (determinantTwistScalar χ g)⁻¹ := by
  change (((χ.onIdeles (AdelicGL.determinant F n g))⁻¹ : ℂˣ) : ℂ) =
    ((χ.onIdeles (AdelicGL.determinant F n g) : ℂ))⁻¹
  exact Units.val_inv_eq_inv_val _

theorem determinantTwistScalar_ne_zero (χ : HeckeCharacter F) (g : AdelicGL F n) :
    determinantTwistScalar χ g ≠ 0 :=
  Units.ne_zero _

namespace OperatorRealization

local instance finiteOrderTwistSpaceAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space :=
  Submodule.addCommGroup _

variable {S T U : OperatorRealization F n} {χ ψ : HeckeCharacter F}

/-- All three equations for a supplied linear equivalence. The unchanged
infinitesimal action quantifies over the whole enveloping algebra. -/
def DeterminantTwistEquations (χ : HeckeCharacter F) (S T : OperatorRealization F n)
    (e : S.Space ≃ₗ[ℂ] T.Space) : Prop :=
  (∀ (d : FiniteAdelicGL F n) (f : S.Space),
    T.finiteRepresentation d (e f) =
      determinantTwistScalar χ (AdelicGL.ofFinite F n d) • e (S.finiteRepresentation d f)) ∧
  (∀ (k : standardInfiniteCompact F n) (f : S.Space),
    T.compactRepresentation k (e f) =
      determinantTwistScalar χ (AdelicGL.ofInfinite F n k.val) •
        e (S.compactRepresentation k f)) ∧
  (∀ (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space),
    T.envelopingAction a (e f) = e (S.envelopingAction a f))

namespace DeterminantTwistEquations

theorem refl (S : OperatorRealization F n) :
    DeterminantTwistEquations 1 S S (LinearEquiv.refl ℂ S.Space) := by
  constructor
  · intro d f
    simp
  constructor
  · intro k f
    simp
  · intro a f
    rfl

private theorem compose_equation
    {V W Z : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup Z]
    [Module ℂ V] [Module ℂ W] [Module ℂ Z]
    (e : V ≃ₗ[ℂ] W) (q : W ≃ₗ[ℂ] Z)
    (A : Module.End ℂ V) (B : Module.End ℂ W) (C : Module.End ℂ Z)
    (c d : ℂ) (he : ∀ f, B (e f) = c • e (A f))
    (hq : ∀ g, C (q g) = d • q (B g)) (f : V) :
    C (q (e f)) = (c * d) • q (e (A f)) := by
  rw [hq (e f), he f, q.map_smul, smul_smul, mul_comm d c]

theorem trans {e : S.Space ≃ₗ[ℂ] T.Space} {q : T.Space ≃ₗ[ℂ] U.Space}
    (he : DeterminantTwistEquations χ S T e)
    (hq : DeterminantTwistEquations ψ T U q) :
    DeterminantTwistEquations (χ * ψ) S U (e.trans q) := by
  constructor
  · intro d f
    simpa only [determinantTwistScalar_mul, LinearEquiv.trans_apply] using
      compose_equation e q (S.finiteRepresentation d) (T.finiteRepresentation d)
        (U.finiteRepresentation d) _ _ (he.1 d) (hq.1 d) f
  constructor
  · intro k f
    simpa only [determinantTwistScalar_mul, LinearEquiv.trans_apply] using
      compose_equation e q (S.compactRepresentation k) (T.compactRepresentation k)
        (U.compactRepresentation k) _ _ (he.2.1 k) (hq.2.1 k) f
  · intro a f
    exact (hq.2.2 a (e f)).trans (congrArg q (he.2.2 a f))

private theorem inverse_equation
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (A : Module.End ℂ V) (B : Module.End ℂ W)
    (c : ℂ) (hc : c ≠ 0) (h : ∀ f, B (e f) = c • e (A f)) (g : W) :
    A (e.symm g) = c⁻¹ • e.symm (B g) := by
  apply e.injective
  simp only [map_smul, LinearEquiv.apply_symm_apply]
  have hg := h (e.symm g)
  rw [LinearEquiv.apply_symm_apply] at hg
  rw [hg, smul_smul, inv_mul_cancel₀ hc, one_smul]

set_option maxHeartbeats 800000 in
theorem symm {e : S.Space ≃ₗ[ℂ] T.Space}
    (he : DeterminantTwistEquations χ S T e) :
    DeterminantTwistEquations χ⁻¹ T S e.symm := by
  constructor
  · intro d f
    rw [determinantTwistScalar_inv χ (AdelicGL.ofFinite F n d)]
    exact inverse_equation e _ _ _ (determinantTwistScalar_ne_zero χ _) (he.1 d) f
  constructor
  · intro k f
    rw [determinantTwistScalar_inv χ (AdelicGL.ofInfinite F n k.val)]
    exact inverse_equation e _ _ _ (determinantTwistScalar_ne_zero χ _) (he.2.1 k) f
  · intro a f
    apply e.injective
    simpa only [LinearEquiv.apply_symm_apply] using (he.2.2 a (e.symm f)).symm

/-- The identity character retains precisely the complete generator criterion. -/
theorem one_iff (e : S.Space ≃ₗ[ℂ] T.Space) :
    DeterminantTwistEquations 1 S T e ↔
      (∀ d f, e (S.finiteRepresentation d f) = T.finiteRepresentation d (e f)) ∧
      (∀ k f, e (S.compactRepresentation k f) = T.compactRepresentation k (e f)) ∧
      (∀ a f, e (S.envelopingAction a f) = T.envelopingAction a (e f)) := by
  simp only [DeterminantTwistEquations, determinantTwistScalar_one, one_smul]
  constructor <;> rintro ⟨hd, hk, ha⟩
  · exact ⟨fun d f => (hd d f).symm, fun k f => (hk k f).symm,
      fun a f => (ha a f).symm⟩
  · exact ⟨fun d f => (hd d f).symm, fun k f => (hk k f).symm,
      fun a f => (ha a f).symm⟩

end DeterminantTwistEquations

/-- A relation on supplied actual full realizations, asserting no twist existence. -/
def IsFiniteOrderDeterminantTwist (χ : HeckeCharacter F)
    (S T : OperatorRealization F n) : Prop :=
  χ.HasFiniteOrder ∧ ∃ e : S.Space ≃ₗ[ℂ] T.Space, DeterminantTwistEquations χ S T e

namespace IsFiniteOrderDeterminantTwist

theorem refl (S : OperatorRealization F n) : IsFiniteOrderDeterminantTwist 1 S S :=
  ⟨HeckeCharacter.hasFiniteOrder_one, ⟨_, DeterminantTwistEquations.refl S⟩⟩

theorem trans (h : IsFiniteOrderDeterminantTwist χ S T)
    (h' : IsFiniteOrderDeterminantTwist ψ T U) :
    IsFiniteOrderDeterminantTwist (χ * ψ) S U := by
  rcases h with ⟨hχ, e, he⟩
  rcases h' with ⟨hψ, q, hq⟩
  exact ⟨hχ.mul hψ, ⟨e.trans q, he.trans hq⟩⟩

theorem symm (h : IsFiniteOrderDeterminantTwist χ S T) :
    IsFiniteOrderDeterminantTwist χ⁻¹ T S := by
  rcases h with ⟨hχ, e, he⟩
  exact ⟨hχ.inv, ⟨e.symm, he.symm⟩⟩

end IsFiniteOrderDeterminantTwist

theorem isFiniteOrderDeterminantTwist_one_iff :
    IsFiniteOrderDeterminantTwist 1 S T ↔ Nonempty (S.Equivalence T) := by
  constructor
  · rintro ⟨_, e, he⟩
    obtain ⟨hd, hk, ha⟩ := (DeterminantTwistEquations.one_iff e).mp he
    exact ⟨Equivalence.ofGenerators e hd hk ha⟩
  · rintro ⟨e⟩
    refine ⟨HeckeCharacter.hasFiniteOrder_one, e.toLinearEquiv, ?_⟩
    exact (DeterminantTwistEquations.one_iff _).mpr
      ⟨Intertwiner.finite e.toIntertwiningMap, Intertwiner.compact e.toIntertwiningMap,
        Intertwiner.differential e.toIntertwiningMap⟩

/-- Transport in both arguments uses full equivalences, not finite restrictions. -/
theorem isFiniteOrderDeterminantTwist_congr
    {S' T' : OperatorRealization F n}
    (hS : Nonempty (S.Equivalence S')) (hT : Nonempty (T.Equivalence T')) :
    IsFiniteOrderDeterminantTwist χ S T ↔ IsFiniteOrderDeterminantTwist χ S' T' := by
  have hS' := isFiniteOrderDeterminantTwist_one_iff.mpr hS
  have hT' := isFiniteOrderDeterminantTwist_one_iff.mpr hT
  constructor
  · intro h
    simpa only [inv_one (G := HeckeCharacter F), one_mul χ, mul_one χ] using
      (hS'.symm.trans h).trans hT'
  · intro h
    simpa only [inv_one (G := HeckeCharacter F), one_mul χ, mul_one χ] using
      (hS'.trans h).trans hT'.symm

theorem IsFiniteOrderDeterminantTwist.target_equivalent
    (h : IsFiniteOrderDeterminantTwist χ S T)
    (h' : IsFiniteOrderDeterminantTwist χ S U) : Nonempty (T.Equivalence U) := by
  apply isFiniteOrderDeterminantTwist_one_iff.mp
  simpa only [inv_mul_cancel] using h.symm.trans h'

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}
variable {S T U S' T' : CuspidalOperatorRealization F r} {χ ψ : HeckeCharacter F}

/-- The same relation on actual positive-rank irreducible cuspidal objects. -/
abbrev IsFiniteOrderDeterminantTwist (χ : HeckeCharacter F)
    (S T : CuspidalOperatorRealization F r) : Prop :=
  OperatorRealization.IsFiniteOrderDeterminantTwist χ S.realization T.realization

theorem isFiniteOrderDeterminantTwist_congr
    (hS : Nonempty (S.Equivalence S')) (hT : Nonempty (T.Equivalence T')) :
    IsFiniteOrderDeterminantTwist χ S T ↔ IsFiniteOrderDeterminantTwist χ S' T' :=
  OperatorRealization.isFiniteOrderDeterminantTwist_congr hS hT

/-- Representative independence with exactly the existing full quotient relation. -/
theorem isFiniteOrderDeterminantTwist_iff_of_isoClass_eq
    (hS : S.isoClass = S'.isoClass) (hT : T.isoClass = T'.isoClass) :
    IsFiniteOrderDeterminantTwist χ S T ↔ IsFiniteOrderDeterminantTwist χ S' T' :=
  isFiniteOrderDeterminantTwist_congr ((S.isoClass_eq_iff S').mp hS)
    ((T.isoClass_eq_iff T').mp hT)

namespace IsoClass

/-- Descent to the existing full cuspidal classes, with no chosen representative. -/
def IsFiniteOrderDeterminantTwist (χ : HeckeCharacter F) (c d : IsoClass F r) : Prop :=
  Quotient.liftOn₂ c d
    (fun S T => CuspidalOperatorRealization.IsFiniteOrderDeterminantTwist χ S T)
    (fun _ _ _ _ hS hT => propext (isFiniteOrderDeterminantTwist_congr hS hT))

@[simp]
theorem isFiniteOrderDeterminantTwist_isoClass_iff :
    IsFiniteOrderDeterminantTwist χ S.isoClass T.isoClass ↔
      CuspidalOperatorRealization.IsFiniteOrderDeterminantTwist χ S T := Iff.rfl

/-- The complete representative criterion, including the finite-order hypothesis
and all three equations on a supplied actual linear equivalence. -/
theorem isFiniteOrderDeterminantTwist_iff (c d : IsoClass F r) :
    IsFiniteOrderDeterminantTwist χ c d ↔
      ∀ (S T : CuspidalOperatorRealization F r), S.isoClass = c → T.isoClass = d →
        χ.HasFiniteOrder ∧
          ∃ e : S.realization.Space ≃ₗ[ℂ] T.realization.Space,
            OperatorRealization.DeterminantTwistEquations χ S.realization T.realization e := by
  refine Quotient.inductionOn₂ c d ?_
  intro S T
  constructor
  · intro h S' T' hS hT
    exact (isFiniteOrderDeterminantTwist_iff_of_isoClass_eq hS.symm hT.symm).mp h
  · intro h
    exact h S T rfl rfl

theorem isFiniteOrderDeterminantTwist_one_iff (c d : IsoClass F r) :
    IsFiniteOrderDeterminantTwist 1 c d ↔ c = d := by
  refine Quotient.inductionOn₂ c d ?_
  intro S T
  exact OperatorRealization.isFiniteOrderDeterminantTwist_one_iff.trans
    (S.isoClass_eq_iff T).symm

theorem IsFiniteOrderDeterminantTwist.refl (c : IsoClass F r) :
    IsFiniteOrderDeterminantTwist 1 c c :=
  (isFiniteOrderDeterminantTwist_one_iff c c).mpr rfl

theorem IsFiniteOrderDeterminantTwist.trans {c d e : IsoClass F r}
    (h : IsFiniteOrderDeterminantTwist χ c d)
    (h' : IsFiniteOrderDeterminantTwist ψ d e) :
    IsFiniteOrderDeterminantTwist (χ * ψ) c e := by
  revert h h'
  refine Quotient.inductionOn₃ c d e ?_
  intro S T U h h'
  exact OperatorRealization.IsFiniteOrderDeterminantTwist.trans h h'

theorem IsFiniteOrderDeterminantTwist.symm {c d : IsoClass F r}
    (h : IsFiniteOrderDeterminantTwist χ c d) :
    IsFiniteOrderDeterminantTwist χ⁻¹ d c := by
  revert h
  refine Quotient.inductionOn₂ c d ?_
  intro S T h
  exact OperatorRealization.IsFiniteOrderDeterminantTwist.symm h

/-- A fixed character and source have at most one target; self-twists do not
imply uniqueness of the character. -/
theorem IsFiniteOrderDeterminantTwist.target_unique {c d e : IsoClass F r}
    (h : IsFiniteOrderDeterminantTwist χ c d)
    (h' : IsFiniteOrderDeterminantTwist χ c e) : d = e := by
  apply (isFiniteOrderDeterminantTwist_one_iff d e).mp
  simpa only [inv_mul_cancel] using h.symm.trans h'

end IsoClass
end CuspidalOperatorRealization
end Langlands.Automorphic

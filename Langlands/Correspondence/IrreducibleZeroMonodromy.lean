import Langlands.Correspondence.ArithmeticFactors
import Langlands.Correspondence.ZeroMonodromyExtension
import Langlands.Weil.Local.ContinuityProof
import Langlands.Weil.Local.IrreducibleReductionProof
import Mathlib.FieldTheory.Separable

/-!
# Zero-monodromy parameters of continuous irreducible Weil classes

The open-inertia and Frobenius-semisimplicity conditions are proved from
continuity and irreducibility on the actual local Weil group.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

private theorem finiteImage_action_semisimple
    {G : Type*} [Group G] (B : FiniteRepresentation ℂ G)
    (hB : B.HasFiniteImage) (g : G) :
    Module.End.IsSemisimple (B.representation g) := by
  have hf : (Set.range B.representation.asGroupHom).Finite := by
    apply Set.Finite.of_finite_image (f := Units.val) ?_ Units.val_injective.injOn
    simpa only [FiniteRepresentation.HasFiniteImage, ← Set.range_comp',
      Representation.asGroupHom_apply] using hB
  let : Finite B.representation.asGroupHom.range := hf.to_subtype
  obtain ⟨m, hm, hp⟩ :=
    (isOfFinOrder_of_finite (B.representation.asGroupHom.rangeRestrict g)).exists_pow_eq_one
  have hp' : B.representation g ^ m = 1 := by
    have h := congrArg
      (fun a : B.representation.asGroupHom.range =>
        ((a : (Module.End ℂ B)ˣ) : Module.End ℂ B)) hp
    simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, MonoidHom.coe_rangeRestrict,
      Representation.asGroupHom_apply, OneMemClass.coe_one, Units.val_one] using h
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := Polynomial.X ^ m - Polynomial.C (1 : ℂ))
    ((Polynomial.separable_X_pow_sub_C 1
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)) one_ne_zero).squarefree)
  simp [hp']

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Every action operator of a continuous irreducible actual local Weil
representation is semisimple. -/
theorem irreducibleWeil_action_semisimple
    (A : Weil.Local.LocalWeilRepresentation.{uF, uP} F)
    (hA : A.IsContinuous) (hirr : A.IsIrreducible)
    (g : Weil.Local.localWeilGroup F) :
    Module.End.IsSemisimple (A.representation g) := by
  obtain ⟨⟨z, B, _, _, hB, _, ⟨e⟩⟩, _⟩ :=
    Weil.Local.localWeilIrreducibleReductionFor F A hA hirr
  apply (e.toLinearEquiv.isSemisimple_iff
    (A.representation g)
    ((FiniteRepresentation.twist
      (Weil.Local.localUnramifiedCharacter F z).toMonoidHom B).representation g)
    (e.isIntertwining' g)).mpr
  exact Module.End.IsSemisimple_smul _
    (finiteImage_action_semisimple B hB g)

/-- A continuous irreducible actual Weil representation defines a
Frobenius-semisimple parameter with zero monodromy. -/
theorem irreducibleWeil_zeroMonodromy_isParameter
    (A : Weil.Local.LocalWeilRepresentation.{uF, uP} F)
    (hA : A.IsContinuous) (hirr : A.IsIrreducible) :
    Weil.Local.IsLocalFrobeniusSemisimpleParameter F
      (WeilDeligneRepresentation.zeroMonodromy
        (Weil.Local.localNormCharacter F).toMonoidHom A) := by
  exact ⟨((Weil.Local.localWeilContinuity F A).2.2.1).mp hA,
    fun g _ => irreducibleWeil_action_semisimple F A hA hirr g⟩

/-- Every continuous irreducible Weil class has a zero-monodromy parameter
class in the full domain at the same rank. -/
theorem exists_zeroMonodromyParameter {n : ℕ+}
    (σ : IrreducibleWeilClass.{uF, uP} F n) :
    ∃ D : WeilDeligneClass.{uF, uP} F n, IsZeroMonodromyOf F σ D := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep σ.val
  have hclass : FiniteRepresentation.classOf A.val = weilClassForget F σ :=
    congrArg (FiniteRepresentation.forgetPropertyClass _) hA
  let Z := WeilDeligneRepresentation.zeroMonodromy
    (Weil.Local.localNormCharacter F).toMonoidHom A.val
  have hZ : Weil.Local.IsLocalFrobeniusSemisimpleParameter F Z :=
    irreducibleWeil_zeroMonodromy_isParameter F A.val A.property.1 A.property.2
  let C := Quotient.mk
    (WeilDeligneRepresentation.frobeniusSemisimpleParameterSetoid
      (Weil.Local.localInertia F) (Weil.Local.localDegree F).toMonoidHom) ⟨Z, hZ⟩
  have hdim : WeilDeligneRepresentation.classRank
      (WeilDeligneRepresentation.frobeniusSemisimpleClassForget
        (Weil.Local.localInertia F) (Weil.Local.localDegree F).toMonoidHom C) = n :=
    (congrArg FiniteRepresentation.classRank hclass).trans σ.property
  exact ⟨⟨C, hdim⟩, A.val, hclass, rfl⟩

/-- The unique full parameter class with the given irreducible Weil action and
zero monodromy. -/
def zeroMonodromyParameter {n : ℕ+}
    (σ : IrreducibleWeilClass.{uF, uP} F n) : WeilDeligneClass.{uF, uP} F n :=
  Classical.choose (exists_zeroMonodromyParameter F σ)

/-- The canonical parameter represents the supplied continuous irreducible
Weil class with zero monodromy. -/
theorem zeroMonodromyParameter_spec {n : ℕ+}
    (σ : IrreducibleWeilClass.{uF, uP} F n) :
    IsZeroMonodromyOf F σ (zeroMonodromyParameter F σ) :=
  Classical.choose_spec (exists_zeroMonodromyParameter F σ)

/-- The relational zero-monodromy condition identifies exactly the canonical
parameter. -/
theorem isZeroMonodromyOf_iff_eq {n : ℕ+}
    (σ : IrreducibleWeilClass.{uF, uP} F n)
    (D : WeilDeligneClass.{uF, uP} F n) :
    IsZeroMonodromyOf F σ D ↔ D = zeroMonodromyParameter F σ := by
  constructor
  · intro hD
    exact hD.unique (F := F) (zeroMonodromyParameter_spec F σ)
  · rintro rfl
    exact zeroMonodromyParameter_spec F σ

/-- The canonical parameter and `weilPairClass` have the same underlying pair
class, so arithmetic factors can use either interface. -/
theorem parameterForget_zeroMonodromyParameter {n : ℕ+}
    (σ : IrreducibleWeilClass.{uF, uP} F n) :
    parameterForget F (zeroMonodromyParameter F σ) = weilPairClass F σ := by
  obtain ⟨A, hA, hD⟩ := zeroMonodromyParameter_spec F σ
  change _ = Quotient.map _ _ (weilClassForget F σ)
  rw [← hA]
  exact hD.symm

end Langlands.Correspondence

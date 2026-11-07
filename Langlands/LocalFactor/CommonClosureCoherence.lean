import Langlands.LocalFactor.CommonClosureInductionTwist

/-!
# Self and tower coherence of actual common-closure operations

The tower induction equivalence acts on the existing equivariant-function carriers.
The additive-character identities use the actual finite field traces.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosure

open VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Evaluation of the inner equivariant function at the identity identifies
successive induction with direct induction through the same actual subgroups. -/
def inducedRepresentationTransEquiv (E L M : Extension F)
    (h : E.field ≤ L.field) (h' : L.field ≤ M.field)
    (A : FiniteRepresentation.ContinuousObjects.{uF, max uF uV} (weilSubgroup F M)) :
    FiniteRepresentation.Equiv
      (inducedRepresentation F E L h (inducedRepresentation F L M h' A)).val
      (inducedRepresentation F E M (h.trans h') A).val where
  toLinearEquiv :=
    { toFun := fun f =>
        ⟨fun g => (f.val g).val 1, by
          intro s g
          let l : weilSubgroup F L :=
            ⟨s.val.val, weilSubgroup_antitone F L M h' s.property⟩
          let t : (weilSubgroup F L).subgroupOf (weilSubgroup F E) :=
            ⟨s.val, weilSubgroup_antitone F L M h' s.property⟩
          have hout := congrArg (fun z => z.val 1) (f.property t g)
          change (f.val ((s : weilSubgroup F E) * g)).val 1 =
            (f.val g).val (1 * l) at hout
          have hin := (f.val g).property ⟨l, s.property⟩ 1
          change (f.val g).val (l * 1) =
            A.val.representation (nestedWeilEquiv F E M (h.trans h') s)
              ((f.val g).val 1) at hin
          change (f.val ((s : weilSubgroup F E) * g)).val 1 = _
          exact (hout.trans (congrArg (f.val g).val (one_mul l))).trans
            ((congrArg (f.val g).val (mul_one l)).symm.trans hin)⟩
      invFun := fun f =>
        ⟨fun g =>
          ⟨fun l => f.val (Subgroup.inclusion (weilSubgroup_antitone F E L h) l * g), by
            intro s l
            have hf := f.property
              ⟨Subgroup.inclusion (weilSubgroup_antitone F E L h) s.val, s.property⟩
              (Subgroup.inclusion (weilSubgroup_antitone F E L h) l * g)
            change f.val
                (Subgroup.inclusion (weilSubgroup_antitone F E L h) (s.val * l) * g) =
              A.val.representation (nestedWeilEquiv F L M h' s)
                (f.val (Subgroup.inclusion (weilSubgroup_antitone F E L h) l * g))
            change f.val
                (Subgroup.inclusion (weilSubgroup_antitone F E L h) s.val *
                  (Subgroup.inclusion (weilSubgroup_antitone F E L h) l * g)) =
              A.val.representation (nestedWeilEquiv F L M h' s)
                (f.val (Subgroup.inclusion (weilSubgroup_antitone F E L h) l * g))
              at hf
            simpa only [map_mul, mul_assoc] using hf⟩, by
          intro s g
          apply Subtype.ext
          funext l
          change f.val
              (Subgroup.inclusion (weilSubgroup_antitone F E L h) l *
                ((s : weilSubgroup F E) * g)) =
            f.val (Subgroup.inclusion (weilSubgroup_antitone F E L h)
              (l * nestedWeilEquiv F E L h s) * g)
          simp only [map_mul, mul_assoc]
          rfl⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext g
        apply Subtype.ext
        funext l
        have hf := congrArg (fun z => z.val 1)
          (f.property
            ⟨Subgroup.inclusion (weilSubgroup_antitone F E L h) l, l.property⟩ g)
        change (f.val (Subgroup.inclusion (weilSubgroup_antitone F E L h) l * g)).val 1 =
          (f.val g).val (1 * l) at hf
        simpa only [one_mul] using hf
      right_inv := by
        intro f
        apply Subtype.ext
        funext g
        change f.val (Subgroup.inclusion (weilSubgroup_antitone F E L h) 1 * g) = f.val g
        simp only [map_one, one_mul]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' := by
    intro g
    ext f
    rfl

/-- Induction on the actual continuous exact quotients is transitive. -/
theorem induce_trans (E L M : Extension F)
    (h : E.field ≤ L.field) (h' : L.field ≤ M.field)
    (x : Virtual.{uF, uV} F M) :
    induce F E L h (induce F L M h' x) = induce F E M (h.trans h') x := by
  have heq :
      (induce.{uF, uV} F E L h).comp (induce F L M h') =
        induce F E M (h.trans h') := by
    apply ExactGrothendieckGroup.hom_ext
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      rcases A with ⟨A, hA⟩
      change induce F E L h
          (induce F L M h' (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hA⟩)) =
        induce F E M (h.trans h') (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hA⟩)
      rw [induce_ofRepresentation.{uF, uV} F L M h' ⟨A, hA⟩,
        induce_ofRepresentation.{uF, uV} F E L h (inducedRepresentation F L M h' ⟨A, hA⟩),
        induce_ofRepresentation.{uF, uV} F E M (h.trans h') ⟨A, hA⟩]
      exact ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _
        (inducedRepresentationTransEquiv F E L M h h' ⟨A, hA⟩)
  exact LinearMap.congr_fun heq x

/-- The actual field trace of a self inclusion pulls a character back to itself. -/
@[simp]
theorem traceCharacter_self (E : Extension F) (ψ : AdditiveCharacter F E) :
    traceCharacter F E E le_rfl ψ = ψ := by
  let := (fieldData F E).topology
  apply HarmonicAnalysis.UnitaryAdditiveCharacter.ext
  intro x
  rw [traceCharacter_apply]
  have hi : IntermediateField.inclusion (le_refl E.field) = AlgHom.id F.Carrier E.field := by
    ext y
    rfl
  rw [hi]
  change ψ (Algebra.trace E.field E.field x) = ψ x
  rw [Algebra.trace_self_apply]

/-- Pulling back by trace through a tower agrees with direct trace pullback. -/
theorem traceCharacter_trans (E L M : Extension F)
    (h : E.field ≤ L.field) (h' : L.field ≤ M.field)
    (ψ : AdditiveCharacter F E) :
    traceCharacter F E M (h.trans h') ψ =
      traceCharacter F L M h' (traceCharacter F E L h ψ) := by
  let := (fieldData F M).topology
  let : Algebra E.field L.field := (IntermediateField.inclusion h).toAlgebra
  let : Algebra L.field M.field := (IntermediateField.inclusion h').toAlgebra
  let : Algebra E.field M.field := (IntermediateField.inclusion (h.trans h')).toAlgebra
  let : IsScalarTower E.field L.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier E.field L.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier L.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite E.field L.field := Module.Finite.right F.Carrier E.field L.field
  let : Module.Finite L.field M.field := Module.Finite.right F.Carrier L.field M.field
  apply HarmonicAnalysis.UnitaryAdditiveCharacter.ext
  intro x
  simp only [traceCharacter_apply]
  exact congrArg ψ (Algebra.trace_trace (R := E.field) (S := L.field) x).symm

end Langlands.LocalFactor.CommonClosure

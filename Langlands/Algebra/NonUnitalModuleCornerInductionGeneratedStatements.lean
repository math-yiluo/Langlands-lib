import Langlands.Algebra.NonUnitalModuleCornerInduction
import Langlands.Algebra.NonUnitalModuleIdempotentGenerated

/-!
# Generatedness of actual corner induction and surjective descent

Closed statement targets for Renard (9 July 2026), I.3.2, printed
pp.20–22 / PDF pp.26–28. The arbitrary-ring additive assertions are internal
strengthenings; local units enter only in the nondegenerate-category adapter.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleCornerInductionGeneratedStatements

open CategoryTheory
open NonUnitalModuleCornerInduction
open NonUnitalModuleIdempotentGenerated

universe uA uZ uM uN

/-- Pure-tensor factorization, fixed-vector membership, and generatedness of the
actual quotient with exactly its named group and residual original action. -/
def CornerInductionGeneratedTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    letI : AddCommGroup (Tensor e Z) := tensorAddCommGroup e Z
    letI : NonUnitalModule A (Tensor e Z) := tensorModule e Z
    (∀ (a : A) (z : Z),
      tmul e a z =
        (tensorModule e Z).toDistribSMul.toSMul.smul a (tmul e (e : A) z)) ∧
    (∀ z : Z, tmul e (e : A) z ∈ NonUnitalModuleCorner.fixedPart e (Tensor e Z)) ∧
    IsGeneratedByIdempotent e (Tensor e Z)

/-- A surjective original intertwiner is surjective on the actual generated
submodules and carries generatedness to its target, with independent carriers. -/
def IdempotentGeneratedSurjectiveDescentTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) (N : Type uN) [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A M] [NonUnitalModule A N] (f : NonUnitalModuleHom A M N),
    Function.Surjective f.toAddMonoidHom →
      Function.Surjective
        ((NonUnitalModuleIdempotentGenerated.restrict e f :
          @NonUnitalModuleHom A (aeM e M) (aeM e N) _
            (aeMAddCommGroup e M) (aeMAddCommGroup e N)
            (aeMModule e M) (aeMModule e N)).toAddMonoidHom) ∧
      (IsGeneratedByIdempotent e M → IsGeneratedByIdempotent e N)

/-- The actual additive induction functor factors through the generated full
subcategory. Whole-functor equalities retain every tensor object and full map. -/
def CornerInductionGeneratedFactorizationTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    ∃ G : ModuleCat.{uZ} (Idempotent.Corner e) ⥤
        GeneratedModuleCat.{uA, max uA uZ} e,
      G.Additive ∧
      G ⋙ NonUnitalModuleIdempotentGenerated.inclusion e =
        nondegenerateFunctor hA e ∧
      (G ⋙ NonUnitalModuleIdempotentGenerated.inclusion e) ⋙ nondegenerateInclusion A =
        ambientFunctor e

/-- The closed aggregate of induced generatedness, actual surjective descent,
and actual additive categorical factorization. -/
def CornerInductionGeneratedStatements : Prop :=
  CornerInductionGeneratedTheorem.{uA, uZ} ∧
  IdempotentGeneratedSurjectiveDescentTheorem.{uA, uM, uN} ∧
  CornerInductionGeneratedFactorizationTheorem.{uA, uZ}

end Langlands.Algebra.NonUnitalModuleCornerInductionGeneratedStatements

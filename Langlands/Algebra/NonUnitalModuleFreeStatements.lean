import Langlands.Algebra.NonUnitalModuleFree
import Langlands.Algebra.NondegenerateModuleAbelianProof
import Langlands.CategoryTheory.Renard.HomObjectProperties

/-!
# Renard I.5.3: free quotients and projective direct summands

The free source is the actual finite-support sum of regular modules. The
projectivity hypothesis is the source's exactness of the actual Hom functor.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NonUnitalModuleFreeStatements

universe uA uM

/-- Every nondegenerate original module is a quotient of an actual free sum. -/
def FreeQuotientStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A),
    ∃ (I : Type (max uA uM))
      (q : NonUnitalModuleFree.object.{uA, uM, max uA uM} hA I ⟶ M),
      Epi q ∧ Function.Surjective (NonUnitalModuleHom.toAddMonoidHom q.hom)

/-- An exact-Hom projective is a genuine biproduct summand of a free sum. -/
def ProjectiveFreeSummandStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
    ∀ P : NondegenerateModuleCat.{uA, max uA uM} A,
      Langlands.Renard.HomProjective P →
      ∃ (I : Type (max uA uM)) (Q : NondegenerateModuleCat.{uA, max uA uM} A),
        Nonempty (NonUnitalModuleFree.object.{uA, uM, max uA uM} hA I ≅ P ⊞ Q)

/-- The two positive free-module assertions of Renard I.5.3. -/
def FreeModuleAssertions : Prop :=
  FreeQuotientStatement.{uA, uM} ∧ ProjectiveFreeSummandStatement.{uA, uM}

/-! The closed targets retain independent coefficient and module universes. -/

example : FreeModuleAssertions.{uA, uM} =
    (FreeQuotientStatement.{uA, uM} ∧ ProjectiveFreeSummandStatement.{uA, uM}) := rfl

example : FreeModuleAssertions.{0, 1} =
    (FreeQuotientStatement.{0, 1} ∧ ProjectiveFreeSummandStatement.{0, 1}) := rfl

example : FreeModuleAssertions.{1, 0} =
    (FreeQuotientStatement.{1, 0} ∧ ProjectiveFreeSummandStatement.{1, 0}) := rfl

end Langlands.Algebra.NonUnitalModuleFreeStatements

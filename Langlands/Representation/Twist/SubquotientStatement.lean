import Langlands.Representation.Twist.SubquotientDefinitions
import Mathlib.Order.Atoms

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- Lattice, underlying-map and simplicity laws for character-twisted subquotients. -/
def TwistSubquotientLaws : Prop :=
  ∀ (chi : G →* Rˣ) (rho : Representation R G V),
    (∀ S : Subrepresentation rho,
      (twistSubrepresentation chi S).toSubmodule = S.toSubmodule) ∧
    (twistSubrepresentation chi (⊥ : Subrepresentation rho) = ⊥) ∧
    (twistSubrepresentation chi (⊤ : Subrepresentation rho) = ⊤) ∧
    (∀ S T : Subrepresentation rho,
      twistSubrepresentation chi (S ⊔ T) =
        twistSubrepresentation chi S ⊔ twistSubrepresentation chi T) ∧
    (∀ S T : Subrepresentation rho,
      twistSubrepresentation chi (S ⊓ T) =
        twistSubrepresentation chi S ⊓ twistSubrepresentation chi T) ∧
    (∀ (S : Subrepresentation rho) (v : S.toSubmodule),
      twistSubrepresentationEquiv chi S v = v) ∧
    (∀ (S : Subrepresentation rho) (v : V),
      twistQuotientEquiv chi S (S.toSubmodule.mkQ v) = S.toSubmodule.mkQ v) ∧
    (IsSimpleOrder (Subrepresentation (twist chi rho)) ↔
      IsSimpleOrder (Subrepresentation rho))

end Langlands

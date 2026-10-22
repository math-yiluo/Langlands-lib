import Langlands.Representation.Twist.Definitions

namespace Langlands

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG}
variable {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]

/-- Twisting respects the existing identities, compositions, and equivalences. -/
def TwistIntertwiningCompatibility : Prop :=
  ∀ (chi : G →* Rˣ) (rho : Representation R G V)
    (sigma : Representation R G W) (tau : Representation R G U),
    twistIntertwining chi (Representation.IntertwiningMap.id rho) =
      Representation.IntertwiningMap.id (twist chi rho) ∧
    (∀ (f : rho.IntertwiningMap sigma) (g : sigma.IntertwiningMap tau),
      twistIntertwining chi (g.comp f) =
        (twistIntertwining chi g).comp (twistIntertwining chi f)) ∧
    untwistIntertwining chi (Representation.IntertwiningMap.id (twist chi rho)) =
      Representation.IntertwiningMap.id rho ∧
    (∀ (f : (twist chi rho).IntertwiningMap (twist chi sigma))
      (g : (twist chi sigma).IntertwiningMap (twist chi tau)),
      untwistIntertwining chi (g.comp f) =
        (untwistIntertwining chi g).comp (untwistIntertwining chi f)) ∧
    twistEquiv chi (Representation.Equiv.refl rho) =
      Representation.Equiv.refl (twist chi rho) ∧
    (∀ (e : rho.Equiv sigma), twistEquiv chi e.symm = (twistEquiv chi e).symm) ∧
    (∀ (e : rho.Equiv sigma) (f : sigma.Equiv tau),
      twistEquiv chi (e.trans f) = (twistEquiv chi e).trans (twistEquiv chi f)) ∧
    (∀ (e : rho.Equiv sigma),
      (twistEquiv chi e).toIntertwiningMap = twistIntertwining chi e.toIntertwiningMap)

end Langlands

import Langlands.Representation.Twist.IntertwiningStatement

namespace Langlands

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG}
variable {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]

@[simp]
theorem twistIntertwining_id (chi : G →* Rˣ) (rho : Representation R G V) :
    twistIntertwining chi (Representation.IntertwiningMap.id rho) =
      Representation.IntertwiningMap.id (twist chi rho) := by
  ext v
  rfl

@[simp]
theorem twistIntertwining_comp (chi : G →* Rˣ)
    {rho : Representation R G V} {sigma : Representation R G W}
    {tau : Representation R G U}
    (g : sigma.IntertwiningMap tau) (f : rho.IntertwiningMap sigma) :
    twistIntertwining chi (g.comp f) =
      (twistIntertwining chi g).comp (twistIntertwining chi f) := by
  ext v
  rfl

@[simp]
theorem untwistIntertwining_id (chi : G →* Rˣ) (rho : Representation R G V) :
    untwistIntertwining chi (Representation.IntertwiningMap.id (twist chi rho)) =
      Representation.IntertwiningMap.id rho := by
  ext v
  rfl

@[simp]
theorem untwistIntertwining_comp (chi : G →* Rˣ)
    {rho : Representation R G V} {sigma : Representation R G W}
    {tau : Representation R G U}
    (g : (twist chi sigma).IntertwiningMap (twist chi tau))
    (f : (twist chi rho).IntertwiningMap (twist chi sigma)) :
    untwistIntertwining chi (g.comp f) =
      (untwistIntertwining chi g).comp (untwistIntertwining chi f) := by
  ext v
  rfl

@[simp]
theorem twistEquiv_refl (chi : G →* Rˣ) (rho : Representation R G V) :
    twistEquiv chi (Representation.Equiv.refl rho) =
      Representation.Equiv.refl (twist chi rho) := by
  ext v
  rfl

@[simp]
theorem twistEquiv_symm (chi : G →* Rˣ)
    {rho : Representation R G V} {sigma : Representation R G W}
    (e : rho.Equiv sigma) :
    twistEquiv chi e.symm = (twistEquiv chi e).symm := by
  ext v
  rfl

@[simp]
theorem twistEquiv_trans (chi : G →* Rˣ)
    {rho : Representation R G V} {sigma : Representation R G W}
    {tau : Representation R G U} (e : rho.Equiv sigma) (f : sigma.Equiv tau) :
    twistEquiv chi (e.trans f) = (twistEquiv chi e).trans (twistEquiv chi f) := by
  ext v
  rfl

@[simp]
theorem twistEquiv_toIntertwiningMap (chi : G →* Rˣ)
    {rho : Representation R G V} {sigma : Representation R G W}
    (e : rho.Equiv sigma) :
    (twistEquiv chi e).toIntertwiningMap = twistIntertwining chi e.toIntertwiningMap := by
  ext v
  rfl

/-- The whole target, with no hypotheses beyond those in the statement. -/
theorem twistIntertwiningCompatibility :
    TwistIntertwiningCompatibility (R := R) (G := G) (V := V) (W := W) (U := U) := by
  intro chi rho sigma tau
  exact ⟨twistIntertwining_id chi rho,
    fun f g => twistIntertwining_comp chi g f,
    untwistIntertwining_id chi rho,
    fun f g => untwistIntertwining_comp chi g f,
    twistEquiv_refl chi rho,
    fun e => twistEquiv_symm chi e,
    fun e f => twistEquiv_trans chi e f,
    fun e => twistEquiv_toIntertwiningMap chi e⟩

end Langlands

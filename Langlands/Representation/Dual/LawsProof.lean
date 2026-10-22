import Langlands.Representation.Dual.LawsStatement

/-! # Laws of algebraic dual maps -/

namespace Langlands

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]
variable {ρ : Representation R G V} {σ : Representation R G W}

theorem dualIntertwining_apply (f : ρ.IntertwiningMap σ) (ℓ : Module.Dual R W) (v : V) :
    dualIntertwining f ℓ v = ℓ (f v) := rfl

theorem dualIntertwining_id :
    dualIntertwining (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id ρ.dual := by
  ext ℓ v
  rfl

theorem dualIntertwining_comp {τ : Representation R G U}
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    dualIntertwining (g.comp f) = (dualIntertwining f).comp (dualIntertwining g) := by
  ext ℓ v
  rfl

theorem dualEquiv_apply (e : ρ.Equiv σ) (ℓ : Module.Dual R W) (v : V) :
    dualEquiv e ℓ v = ℓ (e v) := rfl

theorem bidualIntertwining_apply (v : V) (ℓ : Module.Dual R V) :
    bidualIntertwining ρ v ℓ = ℓ v := rfl

theorem bidualIntertwining_natural (f : ρ.IntertwiningMap σ) :
    (dualIntertwining (dualIntertwining f)).comp (bidualIntertwining ρ) =
      (bidualIntertwining σ).comp f := by
  ext v ℓ
  rfl

theorem algebraicDualLaws :
    AlgebraicDualLawsStatement (R := R) (G := G) (V := V) (W := W) (U := U) := by
  exact ⟨fun _ _ f ℓ v => dualIntertwining_apply f ℓ v,
    fun _ => dualIntertwining_id, fun _ _ _ f g => dualIntertwining_comp f g,
    fun _ _ e ℓ v => dualEquiv_apply e ℓ v, fun _ v ℓ => bidualIntertwining_apply v ℓ,
    fun _ _ f => bidualIntertwining_natural f⟩

end Langlands

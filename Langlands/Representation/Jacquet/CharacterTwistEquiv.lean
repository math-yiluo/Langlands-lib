import Langlands.Representation.Jacquet.Coinvariants
import Langlands.Representation.Twist.Definitions

/-!
# Jacquet quotients under a character twist trivial on the radical

A character of the ambient group trivial on `N` does not change the restricted
action of `N`. The actual quotient maps of the twisted and untwisted
representations therefore descend to mutually inverse linear maps between the
two quotients. The acting subgroup only normalizes `N`; normality of `N` in the
ambient group is not assumed.
-/

namespace Langlands.Jacquet

universe uR uG uV uW

variable {R : Type uR} {G : Type uG}
variable [CommRing R] [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- A character trivial on `N` does not change the action of an element of `N`. -/
theorem twist_apply_of_le_ker (χ : G →* Rˣ) (ρ : Representation R G V)
    {N : Subgroup G} (hN : N ≤ χ.ker) (n : N) (v : V) :
    twist χ ρ n v = ρ n v := by
  change ((χ n : R) • ρ n) v = ρ n v
  rw [MonoidHom.mem_ker.mp (hN n.property), Units.val_one, one_smul]

/-- A character trivial on `N` does not change the restricted action of `N`. -/
theorem twist_comp_subtype (χ : G →* Rˣ) (ρ : Representation R G V) {N : Subgroup G}
    (hN : N ≤ χ.ker) : (twist χ ρ).comp N.subtype = ρ.comp N.subtype := by
  ext x v
  have hx : χ x = 1 := hN x.property
  change ((χ x : R) • ρ x) v = ρ x v
  rw [hx, Units.val_one, one_smul]

/-- The relation submodules before and after the twist agree. -/
theorem relations_twist_of_le_ker (χ : G →* Rˣ) (ρ : Representation R G V)
    {N : Subgroup G} (hN : N ≤ χ.ker) :
    relations (twist χ ρ) N = relations ρ N :=
  congrArg Representation.Coinvariants.ker (twist_comp_subtype χ ρ hN)

/-- The untwisted quotient map descends to the twisted quotient. -/
noncomputable def twistCoinvariantsToCoinvariants (χ : G →* Rˣ)
    (ρ : Representation R G V) (N : Subgroup G) (hN : N ≤ χ.ker) :
    Coinvariants (twist χ ρ) N →ₗ[R] Coinvariants ρ N :=
  lift (twist χ ρ) N (mk ρ N) fun n => LinearMap.ext fun v => by
    change mk ρ N (twist χ ρ n v) = mk ρ N v
    rw [twist_apply_of_le_ker χ ρ hN n v]
    exact mk_apply_subgroup ρ N n v

/-- The twisted quotient map descends to the untwisted quotient. -/
noncomputable def coinvariantsToTwistCoinvariants (χ : G →* Rˣ)
    (ρ : Representation R G V) (N : Subgroup G) (hN : N ≤ χ.ker) :
    Coinvariants ρ N →ₗ[R] Coinvariants (twist χ ρ) N :=
  lift ρ N (mk (twist χ ρ) N) fun n => LinearMap.ext fun v => by
    change mk (twist χ ρ) N (ρ n v) = mk (twist χ ρ) N v
    rw [← twist_apply_of_le_ker χ ρ hN n v]
    exact mk_apply_subgroup (twist χ ρ) N n v

/-- The linear equivalence of actual quotients induced by the two quotient maps. -/
noncomputable def twistCoinvariantsLinearEquiv (χ : G →* Rˣ)
    (ρ : Representation R G V) (N : Subgroup G) (hN : N ≤ χ.ker) :
    Coinvariants (twist χ ρ) N ≃ₗ[R] Coinvariants ρ N :=
  LinearEquiv.ofLinearMap (twistCoinvariantsToCoinvariants χ ρ N hN)
    (coinvariantsToTwistCoinvariants χ ρ N hN)
    (Representation.Coinvariants.hom_ext (LinearMap.ext fun _ => rfl))
    (Representation.Coinvariants.hom_ext (LinearMap.ext fun _ => rfl))

@[simp]
theorem twistCoinvariantsLinearEquiv_mk (χ : G →* Rˣ)
    (ρ : Representation R G V) (N : Subgroup G) (hN : N ≤ χ.ker) (v : V) :
    twistCoinvariantsLinearEquiv χ ρ N hN (mk (twist χ ρ) N v) = mk ρ N v := rfl

@[simp]
theorem twistCoinvariantsLinearEquiv_symm_mk (χ : G →* Rˣ)
    (ρ : Representation R G V) (N : Subgroup G) (hN : N ≤ χ.ker) (v : V) :
    (twistCoinvariantsLinearEquiv χ ρ N hN).symm (mk ρ N v) = mk (twist χ ρ) N v := rfl

/-- The Jacquet quotient of a twist by a character trivial on `N` is the twist of
the Jacquet quotient by the restricted character. -/
noncomputable def actionTwistEquiv (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker) :
    (action (twist χ ρ) N M hMN).Equiv
      (twist (χ.comp M.subtype) (action ρ N M hMN)) :=
  Representation.Equiv.mk (twistCoinvariantsLinearEquiv χ ρ N hN) fun m => by
    apply Representation.Coinvariants.hom_ext
    refine LinearMap.ext fun v => ?_
    change mk ρ N ((χ m : R) • ρ m v) = (χ m : R) • mk ρ N (ρ m v)
    exact map_smul (mk ρ N) _ _

@[simp]
theorem actionTwistEquiv_mk (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker) (v : V) :
    actionTwistEquiv ρ N M hMN χ hN (mk (twist χ ρ) N v) = mk ρ N v := rfl

@[simp]
theorem actionTwistEquiv_symm_mk (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker) (v : V) :
    (actionTwistEquiv ρ N M hMN χ hN).symm (mk ρ N v) = mk (twist χ ρ) N v := rfl

/-- The same identification after a common additional character of `M`. -/
noncomputable def twistActionTwistEquiv (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker) (ψ : M →* Rˣ) :
    (twist ψ (action (twist χ ρ) N M hMN)).Equiv
      (twist (χ.comp M.subtype) (twist ψ (action ρ N M hMN))) :=
  Representation.Equiv.mk (twistCoinvariantsLinearEquiv χ ρ N hN) fun m => by
    apply Representation.Coinvariants.hom_ext
    refine LinearMap.ext fun v => ?_
    change mk ρ N ((ψ m : R) • (χ m : R) • ρ m v) =
      (χ m : R) • (ψ m : R) • mk ρ N (ρ m v)
    rw [map_smul, map_smul, smul_comm]

@[simp]
theorem twistActionTwistEquiv_mk (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker) (ψ : M →* Rˣ)
    (v : V) :
    twistActionTwistEquiv ρ N M hMN χ hN ψ (mk (twist χ ρ) N v) = mk ρ N v := rfl

@[simp]
theorem twistActionTwistEquiv_symm_mk (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker) (ψ : M →* Rˣ)
    (v : V) :
    (twistActionTwistEquiv ρ N M hMN χ hN ψ).symm (mk ρ N v) = mk (twist χ ρ) N v := rfl

section Naturality

variable {ρ : Representation R G V} {σ : Representation R G W}

/-- The identification commutes with the maps induced by an ambient intertwiner. -/
theorem actionTwistEquiv_naturality (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker)
    (f : ρ.IntertwiningMap σ) :
    (twistIntertwining (χ.comp M.subtype) (map N M hMN f)).comp
        (actionTwistEquiv ρ N M hMN χ hN).toIntertwiningMap =
      (actionTwistEquiv σ N M hMN χ hN).toIntertwiningMap.comp
        (map N M hMN (twistIntertwining χ f)) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  rfl

theorem actionTwistEquiv_map_apply (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker)
    (f : ρ.IntertwiningMap σ) (q : Coinvariants (twist χ ρ) N) :
    actionTwistEquiv σ N M hMN χ hN (map N M hMN (twistIntertwining χ f) q) =
      map N M hMN f (actionTwistEquiv ρ N M hMN χ hN q) :=
  Representation.Coinvariants.induction_on q fun _ => rfl

/-- The inverse identification commutes with the induced maps as well. -/
theorem actionTwistEquiv_symm_naturality (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker)
    (f : ρ.IntertwiningMap σ) :
    (map N M hMN (twistIntertwining χ f)).comp
        (actionTwistEquiv ρ N M hMN χ hN).symm.toIntertwiningMap =
      (actionTwistEquiv σ N M hMN χ hN).symm.toIntertwiningMap.comp
        (twistIntertwining (χ.comp M.subtype) (map N M hMN f)) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  rfl

/-- Naturality after a common additional character of `M`. -/
theorem twistActionTwistEquiv_naturality (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker) (ψ : M →* Rˣ)
    (f : ρ.IntertwiningMap σ) :
    (twistIntertwining (χ.comp M.subtype) (twistIntertwining ψ (map N M hMN f))).comp
        (twistActionTwistEquiv ρ N M hMN χ hN ψ).toIntertwiningMap =
      (twistActionTwistEquiv σ N M hMN χ hN ψ).toIntertwiningMap.comp
        (twistIntertwining ψ (map N M hMN (twistIntertwining χ f))) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  rfl

theorem twistActionTwistEquiv_map_apply (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker) (ψ : M →* Rˣ)
    (f : ρ.IntertwiningMap σ) (q : Coinvariants (twist χ ρ) N) :
    twistActionTwistEquiv σ N M hMN χ hN ψ (map N M hMN (twistIntertwining χ f) q) =
      map N M hMN f (twistActionTwistEquiv ρ N M hMN χ hN ψ q) :=
  Representation.Coinvariants.induction_on q fun _ => rfl

theorem twistActionTwistEquiv_symm_naturality (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (χ : G →* Rˣ) (hN : N ≤ χ.ker) (ψ : M →* Rˣ)
    (f : ρ.IntertwiningMap σ) :
    (twistIntertwining ψ (map N M hMN (twistIntertwining χ f))).comp
        (twistActionTwistEquiv ρ N M hMN χ hN ψ).symm.toIntertwiningMap =
      (twistActionTwistEquiv σ N M hMN χ hN ψ).symm.toIntertwiningMap.comp
        (twistIntertwining (χ.comp M.subtype) (twistIntertwining ψ (map N M hMN f))) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  rfl

end Naturality

end Langlands.Jacquet

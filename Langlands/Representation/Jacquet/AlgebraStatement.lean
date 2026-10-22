import Langlands.Representation.Twist.Definitions
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.Basic.Complex.Basic

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Algebraic transitivity on the actual quotient by normal-subgroup relations. -/
def CoinvariantTowerStatement : Prop :=
  ∀ (rho : Representation ℂ G V) (N P : Subgroup G) [N.Normal] [P.Normal], N ≤ P →
      ∃ e : ((rho.toCoinvariants N).toCoinvariants P).Equiv
        (rho.toCoinvariants P),
        ∀ v : V,
          e (Representation.Coinvariants.mk ((rho.toCoinvariants N).comp P.subtype)
            (Representation.Coinvariants.mk (rho.comp N.subtype) v)) =
              Representation.Coinvariants.mk (rho.comp P.subtype) v

/-- Coinvariants commute with a scalar twist that is trivial on the subgroup. -/
def CoinvariantTwistStatement : Prop :=
  ∀ (rho : Representation ℂ G V) (N : Subgroup G) [N.Normal] (chi : G →* ℂˣ),
      (∀ n : N, chi (n : G) = 1) →
      ∃ e : ((twist chi rho).toCoinvariants N).Equiv
        (twist chi (rho.toCoinvariants N)),
        ∀ v : V,
          e (Representation.Coinvariants.mk ((twist chi rho).comp N.subtype) v) =
            Representation.Coinvariants.mk (rho.comp N.subtype) v

/-- A prescribed central scalar action descends to normal-subgroup coinvariants. -/
def CoinvariantCentralActionStatement : Prop :=
  ∀ (rho : Representation ℂ G V) (N : Subgroup G) [N.Normal]
      (omega : Subgroup.center G →* ℂˣ),
      (∀ (z : Subgroup.center G) (v : V), rho (z : G) v = (omega z : ℂ) • v) →
      ∀ (z : Subgroup.center G) (q : Representation.Coinvariants (rho.comp N.subtype)),
        rho.toCoinvariants N (z : G) q = (omega z : ℂ) • q

/-- The three concrete algebraic coinvariant laws, all with unnormalized actions. -/
def CoinvariantAlgebraStatement : Prop :=
  CoinvariantTowerStatement (G := G) (V := V) ∧
    CoinvariantTwistStatement (G := G) (V := V) ∧
    CoinvariantCentralActionStatement (G := G) (V := V)

end Langlands.Jacquet

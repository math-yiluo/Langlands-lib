import Langlands.Geometry.FormalGroup.PDivisibleGroupSchemeTower
import Langlands.GroupScheme.Cartier.FiniteCartierDualExactnessStatement
import Langlands.GroupScheme.Cartier.FiniteDualAdditivity

/-! # The actual Cartier dual tower of a p-divisible group -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.PDivisibleGroup

open GroupScheme.Cartier GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p)

local instance pDivisibleLevelFinite (n : ℕ) : IsFinite (G.inclusions.obj n).X.hom :=
  (G.finiteLocallyFree n).1
local instance pDivisibleLevelFlat (n : ℕ) : Flat (G.inclusions.obj n).X.hom :=
  (G.finiteLocallyFree n).2.1
local instance pDivisibleLevelFinitePresentation (n : ℕ) :
    LocallyOfFinitePresentation (G.inclusions.obj n).X.hom :=
  (G.finiteLocallyFree n).2.2

/-- Cartier duals of transfer maps give the inclusion diagram of the dual groups. -/
def dualInclusions : ℕ ⥤ CommGroupScheme (Spec R) where
  obj n := schemeDual (G.inclusions.obj n)
  map i := schemeDualMap (G.transfer i)
  map_id n := by
    change schemeDualMap (G.transfer (𝟙 n)) = 𝟙 _
    rw [G.transfer_id, schemeDualMap_id]
  map_comp i j := by
    change schemeDualMap (G.transfer (i ≫ j)) = schemeDualMap (G.transfer i) ≫ schemeDualMap (G.transfer j)
    rw [G.transfer_comp, schemeDualMap_comp]

/-- When the dual arrows are reversed, the two exponents in the short exact
sequence exchange roles. The middle level can be written with either sum. -/
theorem shortExact_of_sum (m n k : ℕ) (h : k = m + n) (i : n ⟶ k) (j : m ⟶ k) :
    CommGroupScheme.AffineFppfShortExact (G.inclusions.map i) (G.transfer j) := by
  subst k
  have hi : i = homOfLE (Nat.le_add_left n m) := Subsingleton.elim _ _
  have hj : j = homOfLE (Nat.le_add_right m n) := Subsingleton.elim _ _
  rw [hi, hj]
  exact G.shortExact m n

/-- Exactness of Cartier duality promotes the actual dual spectrum diagram to
a p-divisible group. Its backward maps are duals of the original inclusions. -/
def dual (hExact : FiniteCartierDualExactnessStatement.{u}) : PDivisibleGroup R p where
  inclusions := G.dualInclusions
  transfer i := schemeDualMap (G.inclusions.map i)
  transfer_id n := by
    change schemeDualMap (G.inclusions.map (𝟙 n)) = 𝟙 _
    rw [G.inclusions.map_id, schemeDualMap_id]
  transfer_comp i j := by
    change schemeDualMap (G.inclusions.map (i ≫ j)) =
      schemeDualMap (G.inclusions.map j) ≫ schemeDualMap (G.inclusions.map i)
    rw [Functor.map_comp, schemeDualMap_comp]
  finiteLocallyFree n := schemeDual_finiteLocallyFree (G.inclusions.obj n)
  multiplication {m n} i := by
    change schemeDualMap (G.inclusions.map i) ≫ schemeDualMap (G.transfer i) =
      p ^ (n - m) • (𝟙 (schemeDual (G.inclusions.obj n)))
    rw [← schemeDualMap_comp, G.multiplication, schemeDualMap_nsmul_id]
  shortExact m n := by
    let i : n ⟶ m + n := homOfLE (Nat.le_add_left n m)
    let j : m ⟶ m + n := homOfLE (Nat.le_add_right m n)
    change CommGroupScheme.AffineFppfShortExact (schemeDualMap (G.transfer i))
      (schemeDualMap (G.inclusions.map j))
    exact hExact R (G.inclusions.obj m) (G.inclusions.obj (m + n)) (G.inclusions.obj n)
      (G.inclusions.map j) (G.transfer i) (G.shortExact_of_sum n m (m + n) (Nat.add_comm m n) j i)

end Langlands.PDivisibleGroup

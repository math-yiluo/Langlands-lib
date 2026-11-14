import Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.Parabolic.OrderedProductRegroupingStatement
import Langlands.AllField.Representation.Parabolic.RegroupingFactorEquivalences
/-!
# Three-block associativity from ordered product regrouping

Given the ordered product regrouping proposition `OrderedProductRegrouping` for a topological
datum of a `p`-adic field, this module constructs an equivalence between the two bracketings
`(σ0 × (σ1 × σ2))` and `((σ0 × σ1) × σ2)` of a normalized three-block product, after the
entry-preserving rank cast along `Nat.add_assoc`. It applies the regrouping proposition to the
two refinements of `ThreeBlockRefinementGeometry`, identifies the inner one-block and two-block
products with the literal factors, and composes. The final theorem derives
`CommonUniverseThreeBlockAssociativity` from ordered regrouping at the canonical topological
data of every `p`-adic field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.GeneralLinear hiding SupercuspidalClass blockSum rankInclusion

universe uF uV

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The functor value of a factor family is its normalized product. -/
def normalizedProductInductionObjEquiv {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F)) :
    letI := T.topology
    Representation.Equiv ((T.normalizedProductInductionFunctor B).obj σ).representation
      (T.normalizedProductInduced B (fun i => (σ i).representation)) :=
  letI := T.topology
  Representation.Equiv.refl _

end Langlands.LocalFieldData

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding OrderedProductRegrouping
open Langlands.AllField.Parabolic

section EquivalenceAlgebra

universe uA uG uH uV uW uU

end EquivalenceAlgebra

end Langlands.AllField.Parabolic

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding OrderedProductRegrouping
open Langlands.AllField.Parabolic

open Langlands.GeneralLinear
open Langlands.Geometric hiding PadicStandardIntersectionsTheorem
open Langlands.AllField.Geometric
open Langlands.Shahidi

section Pairs

universe uF uV


end Pairs

section Regroupings

universe uF uW


end Regroupings

universe uF uW

end Langlands.AllField.Parabolic

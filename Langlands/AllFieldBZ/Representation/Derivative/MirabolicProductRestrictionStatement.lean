import Langlands.AllFieldBZ.Representation.Derivative.Homogeneity
import Langlands.AllFieldBZ.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Derivative.MirabolicProductRestrictionStatement

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductRestrictionStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductRestrictionStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous MirabolicProductRestrictionStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
universe uF uV

namespace MirabolicProductRestriction
open Langlands.Derivative.MirabolicProductRestriction hiding restrictedProduct restrictionQuotient restrictionSubobject
variable {F : LocalFieldPackage.{uF}}

/-- `(A × B)|P_(a+b)` for `A` on `GL_(m+1)` and `B` on `GL_(n+1)`: the binary
normalized product, the actual rank cast `(m+1)+(n+1) = (m+n+1)+1`, and
restriction to `P_(m+n+2)`. -/
def restrictedProduct (T : F.TopologicalData) (m n : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier) :=
  letI := T.topology
  T.binaryNormalizedProductFunctor (m + 1) (n + 1) ⋙
    generalLinearRankCast T (show (m + 1) + (n + 1) = (m + n + 1) + 1 by omega) ⋙
      generalLinearRestriction T (m + n + 1)

/-- `(A|P_a) × B`, the first term: restriction of the first input to
`P_(m+1)`, the right mixed product of case (III) with ranks `n+1, m`, and the
actual rank cast `(n+1)+m = m+n+1`. -/
def restrictionSubobject (T : F.TopologicalData) (m n : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier) :=
  letI := T.topology
  (generalLinearRestriction T m).prod
      (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier))) ⋙
    T.rightMixedProductFunctor (n + 1) m ⋙
      mirabolicRankCast T (show (n + 1) + m = m + n + 1 by omega)

/-- `A × (B|P_b)`, the last term: restriction of the second input to
`P_(n+1)`, the left mixed product of case (II) with ranks `m+1, n`, and the
actual rank cast `(m+1)+n = m+n+1`. -/
def restrictionQuotient (T : F.TopologicalData) (m n : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier) :=
  letI := T.topology
  (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
      (generalLinearRestriction T n) ⋙
    T.leftMixedProductFunctor (m + 1) n ⋙
      mirabolicRankCast T (show (m + 1) + n = m + n + 1 by omega)

end MirabolicProductRestriction
open MirabolicProductRestriction in
/-- BZ77 Proposition 4.13(a) for all positive ranks `a = m+1`, `b = n+1`:
natural transformations `i` and `q` whose actual component intertwiners form a
short exact sequence `0 → (A|P_a) × B → (A × B)|P_(a+b) → A × (B|P_b) → 0` at
every pair `(A, B)`. This is a proposition definition, with no theorem-valued
premise and no assertion of its proof. -/
def MirabolicProductRestrictionStatement (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ m n : ℕ,
    ∃ (i : Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictionSubobject.{uF, uV} T m n ⟶ Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictedProduct T m n)
      (q : Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictedProduct.{uF, uV} T m n ⟶ Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictionQuotient T m n),
      ∀ X,
        Function.Injective (SmoothRep.hom (i.app X)) ∧
        LinearMap.range (SmoothRep.hom (i.app X)).toLinearMap =
          LinearMap.ker (SmoothRep.hom (q.app X)).toLinearMap ∧
        Function.Surjective (SmoothRep.hom (q.app X))

end Langlands.AllFieldBZ.Derivative

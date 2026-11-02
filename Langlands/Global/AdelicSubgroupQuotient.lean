import Langlands.GroupScheme.SubgroupFunctor
import Langlands.Global.AdelicGroupPointTopology
import Langlands.Global.LeftCosetSpace

/-! # Actual rational quotients of adelic subgroup functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (U : GroupScheme.SubgroupFunctor G)

/-- The subgroup functor evaluated on the actual rational coefficient scheme. -/
def rationalPoints : Subgroup (RationalGroupPoints F G) :=
  U.carrier ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)))

/-- The subgroup functor evaluated on the actual full adele coefficient scheme. -/
def adelicPoints : Subgroup (AdelicGroupPoints F G) :=
  U.carrier ((algSpec (CommRingCat.of F)).obj
    (op (CommAlgCat.of F (AdeleRing (𝓞 F) F))))

/-- The actual principal map restricted using the subgroup functor's restriction law. -/
def rational : rationalPoints F G U →* adelicPoints F G U where
  toFun q := ⟨AdelicGroupPoints.rational F G q.val,
    U.comp_mem ((algSpec (CommRingCat.of F)).map
      (CommAlgCat.ofHom (Algebra.ofId F (AdeleRing (𝓞 F) F))).op) q.property⟩
  map_one' := Subtype.ext (map_one (AdelicGroupPoints.rational F G))
  map_mul' q r := Subtype.ext (map_mul (AdelicGroupPoints.rational F G) q.val r.val)

@[simp]
theorem rational_coe (q : rationalPoints F G U) :
    ((rational F G U q : adelicPoints F G U) : AdelicGroupPoints F G) =
      AdelicGroupPoints.rational F G q.val := rfl

/-- The actual principal image inside the actual adelic subgroup. -/
def rationalSubgroup : Subgroup (adelicPoints F G U) :=
  (rational F G U).range

/-- The actual left quotient `U(F) \ U(A_F)`, using the principal image. -/
abbrev RationalQuotient :=
  LeftCosetSpace (rationalSubgroup F G U)

/-- Subgroup inclusion followed by projection to the ambient rational quotient respects
the subgroup's actual rational equivalence relation. No injectivity is asserted. -/
def quotientInclusion :
    RationalQuotient F G U → LeftCosetSpace (AdelicGroupPoints.rationalSubgroup F G) :=
  Quotient.map' (fun n : adelicPoints F G U => (n : AdelicGroupPoints F G))
    fun x y h => by
      apply QuotientGroup.rightRel_apply.mpr
      rcases QuotientGroup.rightRel_apply.mp h with ⟨q, hq⟩
      exact ⟨q.val, congrArg (fun n : adelicPoints F G U =>
        (n : AdelicGroupPoints F G)) hq⟩

@[simp]
theorem quotientInclusion_mk (n : adelicPoints F G U) :
    quotientInclusion F G U (LeftCosetSpace.mk (rationalSubgroup F G U) n) =
      LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F G)
        (n : AdelicGroupPoints F G) := rfl

theorem continuous_quotientInclusion : Continuous (quotientInclusion F G U) := by
  apply (LeftCosetSpace.continuous_iff (rationalSubgroup F G U)).mpr
  exact (LeftCosetSpace.continuous_mk (AdelicGroupPoints.rationalSubgroup F G)).comp
    continuous_subtype_val

theorem quotientInclusion_rightTranslate (n : adelicPoints F G U)
    (q : RationalQuotient F G U) :
    quotientInclusion F G U
      (LeftCosetSpace.rightTranslate (rationalSubgroup F G U) n q) =
        LeftCosetSpace.rightTranslate (AdelicGroupPoints.rationalSubgroup F G)
          (n : AdelicGroupPoints F G) (quotientInclusion F G U q) := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

end Langlands.Global.AdelicSubgroupPoints

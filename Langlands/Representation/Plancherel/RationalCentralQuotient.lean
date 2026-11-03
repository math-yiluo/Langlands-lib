import Langlands.Representation.Plancherel.RenardRepresentativeData
import Langlands.GroupScheme.Rational.CenterSplitComponent
import Mathlib.GroupTheory.Index

/-! # Actual central quotients and the rational-character valuation image -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe uG uL u

section GroupQuotient

variable {G : Type uG} [Group G] {L : Type uL} [CommGroup L]
variable (f : G →* L) (hf : Function.Surjective f) (A : Subgroup G) [A.Normal]

/-- Quotienting by the kernel and a normal subgroup is quotienting the target
by the image of that subgroup. -/
def quotientKerSupEquivQuotientMap :
    (G ⧸ (f.ker ⊔ A)) ≃* (L ⧸ A.map f) := by
  let q := (QuotientGroup.mk' (A.map f)).comp f
  have hker : q.ker = f.ker ⊔ A := by
    change ((QuotientGroup.mk' (A.map f)).comp f).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_map_eq, sup_comm]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q
      ((QuotientGroup.mk'_surjective (A.map f)).comp hf))

@[simp]
theorem quotientKerSupEquivQuotientMap_mk (g : G) :
    quotientKerSupEquivQuotientMap f hf A (QuotientGroup.mk g) =
      QuotientGroup.mk (f g) := rfl

end GroupQuotient

section RationalPoints

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The quotient by the actual common norm kernel and a normal point subgroup
is the actual valuation image modulo that subgroup's valuation image. -/
def rationalSubgroupQuotientEquiv (A : Subgroup (GroupScheme.rationalPoints G)) [A.Normal] :
    (GroupScheme.rationalPoints G ⧸ (rationalCommonNormKernel G ⊔ A)) ≃*
      (rationalCharacterValuationImage G ⧸ A.map (rationalCharacterValuation G).rangeRestrict) :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [MonoidHom.ker_rangeRestrict, rationalCharacterValuation_ker])).trans
      (quotientKerSupEquivQuotientMap (rationalCharacterValuation G).rangeRestrict
        (rationalCharacterValuation G).rangeRestrict_surjective A)

@[simp]
theorem rationalSubgroupQuotientEquiv_mk
    (A : Subgroup (GroupScheme.rationalPoints G)) [A.Normal]
    (g : GroupScheme.rationalPoints G) :
    rationalSubgroupQuotientEquiv G A (QuotientGroup.mk g) =
      QuotientGroup.mk ((rationalCharacterValuation G).rangeRestrict g) := rfl

variable {G}
variable {H : GroupScheme (Spec (CommRingCat.of F))}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Mapping the existing scheme-center image back into the ambient point group
gives exactly the range of the actual point map. -/
theorem centralRationalPointImage_map_eq_range (i : H ⟶ G) (hi : GroupScheme.IsCentral i) :
    (GroupScheme.centralRationalPointImage i hi).map
        (GroupScheme.schemeCenterPoints G).subtype =
      (GroupScheme.rationalPoints.map i).range := by
  change (GroupScheme.centralRationalPointsMap i hi).range.map _ = _
  rw [MonoidHom.map_range]
  rfl

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- For an actual central torus map, the quotient is the quotient by the already
defined split-torus valuation image. The construction itself needs only centrality. -/
def rationalCentralQuotientEquiv (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    (GroupScheme.rationalPoints G ⧸
        (rationalCommonNormKernel G ⊔ (GroupScheme.rationalPoints.map s).range)) ≃*
      (rationalCharacterValuationImage G ⧸ RenardCartan.splitValuationImage s) := by
  letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  let v : GroupScheme.rationalPoints G →* rationalCharacterValuationImage G :=
    (rationalCharacterValuation G).rangeRestrict
  have himage : (GroupScheme.rationalPoints.map s).range.map v =
      RenardCartan.splitValuationImage s := MonoidHom.map_range _ _
  exact (rationalSubgroupQuotientEquiv G (GroupScheme.rationalPoints.map s).range).trans
    (QuotientGroup.quotientMulEquivOfEq
      (M := (GroupScheme.rationalPoints.map s).range.map v)
      (N := RenardCartan.splitValuationImage s) himage)

@[simp]
theorem rationalCentralQuotientEquiv_mk (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s) (g : GroupScheme.rationalPoints G) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    rationalCentralQuotientEquiv s hs (QuotientGroup.mk g) =
      QuotientGroup.mk ((rationalCharacterValuation G).rangeRestrict g) := rfl

/-- Finite index of the actual central valuation image implies finiteness of
the actual rational-point quotient. Finite index is an explicit premise. -/
theorem finite_rationalCentralQuotient (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s) (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    Finite (GroupScheme.rationalPoints G ⧸
      (rationalCommonNormKernel G ⊔ (GroupScheme.rationalPoints.map s).range)) := by
  let := hindex
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  exact Finite.of_injective _ (rationalCentralQuotientEquiv s hs).injective

end RationalPoints

end Langlands.Plancherel

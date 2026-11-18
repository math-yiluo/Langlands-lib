import Langlands.Representation.Jacquet.StandardCasselmanConstantTerm
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer
import Langlands.Representation.Exponents.NormalizedIwahoriEigenCoefficient
import Langlands.Geometry.Building.SpecialCompactLevi

/-! # The specified component and ordinary quotient of the canonical standard Levi -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
  (q : A.toGrp ⟶ S.toGrp)

/-- The specified component map through the maximal split torus, with codomain
the canonical representative of the actual standard Levi. -/
def standardComponentSchemeHom : A.toGrp ⟶ Standard.leviScheme i ν J :=
  q ≫ Standard.leviTorusHom i ν J

@[simp] theorem standardComponentSchemeHom_comp :
    standardComponentSchemeHom (i := i) (ν := ν) (J := J) q ≫ Standard.leviHom i ν J = q ≫ i := by
  rw [standardComponentSchemeHom, Category.assoc, Standard.leviTorusHom_comp]

variable {q} (hA : IsCompatibleStandardSplitComponent i ν J A q)

include hA in
/-- Compatibility makes the specified map an actual split component of the
canonical standard Levi scheme, independently of the representative in its witness. -/
theorem isSplitComponent_standardComponentSchemeHom :
    IsSplitComponent (standardComponentSchemeHom (i := i) (ν := ν) (J := J) q) := by
  obtain ⟨_, M, j, a, hj, _, _, ha, hcompat⟩ := hA
  let hj' := Standard.isRepresentedBy_leviHom i ν J
  let e : M ≅ Standard.leviScheme i ν J := hj.isoOfIsRepresentedBy hj'
  have he : e.hom ≫ Standard.leviHom i ν J = j := hj.isoOfIsRepresentedBy_hom_comp hj'
  have hfactor : a ≫ e.hom = standardComponentSchemeHom q := by
    apply hj'.hom_ext
    rw [Category.assoc, he, standardComponentSchemeHom_comp]
    exact hcompat
  rw [← hfactor]
  exact ha.comp_iso e

/-- On actual points, the canonical component map is the target's specified
`standardComponentHom` under the canonical standard-Levi representation equivalence. -/
@[simp] theorem leviPointsEquiv_map_standardComponentSchemeHom (x : rationalPoints A.toGrp) :
    Standard.leviPointsEquiv i ν J
        (rationalPoints.map (standardComponentSchemeHom (i := i) (ν := ν) (J := J) q) x) =
      standardComponentHom hA x := by
  apply Subtype.ext
  rw [Standard.leviPointsEquiv_val, coe_standardComponentHom]
  have h := congrArg (fun f : A.toGrp ⟶ G => rationalPoints.map f x)
    (standardComponentSchemeHom_comp (i := i) (ν := ν) (J := J) q)
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using h

section OrdinaryJacquet

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup standardConstantTermT2Field standardConstantTermLocallyCompact
  standardConstantTermNonarchimedean

/-- The canonical actual normalized Jacquet functor has the same normalized
action on ordinary coinvariants used by the target's Casselman constant term. -/
def standardNormalizedJacquetOrdinaryEquiv
    (ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) :
    ((Aubert.General.normalizedJacquetFunctor (standardUnipotentPoints i ν J)
      (standardLeviPoints i ν J) (isClosed_standardUnipotentPoints i ν J)
      (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)).obj ρ).representation.Equiv
      (Jacquet.normalizedActionOfModulus ρ.representation (standardUnipotentPoints i ν J)
        (standardLeviPoints i ν J) (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
          (standardRadicalModulus i ν J)) :=
  Aubert.General.normalizedJacquetOrdinaryEquiv (standardUnipotentPoints i ν J)
    (standardLeviPoints i ν J) (isClosed_standardUnipotentPoints i ν J)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) ρ

/-- Restriction to the exact specified component preserves all actual
normalized Jacquet generalized eigencharacters under this equivalence. -/
theorem isGeneralizedEigencharacter_standardNormalizedJacquet_iff
    (ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsGeneralizedEigencharacter
        ((((Aubert.General.normalizedJacquetFunctor (standardUnipotentPoints i ν J)
          (standardLeviPoints i ν J) (isClosed_standardUnipotentPoints i ν J)
          (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)).obj ρ).representation).comp
            (standardComponentHom hA)) χ ↔
      IsGeneralizedEigencharacter
        ((Jacquet.normalizedActionOfModulus ρ.representation (standardUnipotentPoints i ν J)
          (standardLeviPoints i ν J) (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
            (standardRadicalModulus i ν J)).comp (standardComponentHom hA)) χ :=
  isGeneralizedEigencharacter_iff_of_equiv
    (Cohomology.HyperextAbutment.equivComp
      (standardNormalizedJacquetOrdinaryEquiv (i := i) (ν := ν) (J := J) ρ)
        (standardComponentHom hA)) χ

end OrdinaryJacquet

end Langlands.BruhatTits.SpecialCompact

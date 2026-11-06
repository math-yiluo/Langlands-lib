import Langlands.GroupScheme.Rational.RootGeneratedCentralizerAssembly
import Langlands.GroupScheme.Rational.RootGeneratedCoxeterRelations
import Langlands.GroupScheme.Rational.RootGeneratedWeylRepresentatives
import Langlands.GroupScheme.Rational.DynamicRootProductRayReduction
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterReduction
import Langlands.Group.RootPairingCoxeterProof

/-! # The root-generated centralizer bound from two structural statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General.RationalPointFamily

namespace Langlands.GroupScheme

/-- The two outstanding geometric statements sufficient for the target. -/
def RootGeneratedCentralizerStructuralPremises : Prop :=
  RelativeRootSystemStatement.{u} ∧ RootRankOneFactorizationStatement.{u}

section Lifts

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  [Smooth G.X.hom] (ν : cocharacterLattice T)

/-- Opposite pairs give actual opposite-root simple lifts; the proved
relation adapter supplies all their Coxeter relations modulo `H0`. -/
theorem hasRootGeneratedSimpleReflectionLifts_of_oppositeFactorPairs
    (hT : IsSplitTorus T.toGrp) (hroot : HasRelativeRootSystem i)
    (hν : IsGenericCocharacter i ν)
    (hE : RelativeRoot.HasOppositeFactorPairs i)
    {C : CoxeterMatrix (SimpleRoot i ν)}
    (cs : CoxeterSystem C (relativeWeylGroup i))
    (hSimple : ∀ a : SimpleRoot i ν, IsRelativeReflection i a.val (cs.simple a)) :
    HasRootGeneratedSimpleReflectionLifts i ν cs := by
  classical
  have hex : ∀ a : SimpleRoot i ν, ∃ n : normalizerPoints i,
      (QuotientGroup.mk n : relativeWeylGroup i) = cs.simple a ∧
        n.val ∈ RelativeRoot.oppositeGeneratedPoints i a.val := by
    intro a
    obtain ⟨x, hx, hx1⟩ := RelativeRoot.exists_rootPoint_actual hT i a.property.1.1
    obtain ⟨p, hp⟩ := hE a.val a.property.1.1 x hx hx1
    let n : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
    refine ⟨n, hroot.eq_of_isRelativeReflection
      (hp.isRelativeReflection i hT a.property.1.1 hx hx1) (hSimple a), ?_⟩
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr hp.1))
        (Subgroup.subset_closure (Or.inl hx)))
      (Subgroup.subset_closure (Or.inr hp.2.1))
  choose m hm hmL using hex
  exact ⟨m, hm, hmL,
    RelativeRoot.oppositeRootSimpleLifts_isLiftable cs hroot hT hν hSimple m hm hmL⟩

end Lifts

/-- Full rank-one factorization supplies the full-kernel reflection
existence statement through the already constructed opposite-root representatives. -/
theorem relativeRootReflectionExistence_of_rootRankOneFactorization
    (hRank : RootRankOneFactorizationStatement.{u}) :
    RelativeRootReflectionExistenceStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hG.smooth
  let := hi.isSplitSubtorus.mono
  have hE : RelativeRoot.HasOppositeFactorPairs i :=
    fun a ha x hx hx1 => (hRank k G hG T i hi a ha x hx hx1).1.exists
  refine ⟨RelativeRootReflectionData.ofOppositeFactorPairs i hi.isSplitSubtorus.1 hE,
    fun a => ?_⟩
  exact (RelativeRoot.rootGeneratedRepresentative_spec i hi.isSplitSubtorus.1 hE a).2.2

/-- The public abstract Coxeter proof discharges the abstract input;
opposite pairs supply the remaining integral reflection data. -/
theorem RootGeneratedCentralizerStructuralPremises.relativeWeylCoxeter
    (h : RootGeneratedCentralizerStructuralPremises.{u}) :
    RelativeWeylCoxeterStatement.{u} :=
  relativeWeylCoxeterStatement_of_rootPairingWeylCoxeterStatement h.1
    (relativeRootReflectionExistence_of_rootRankOneFactorization h.2)
    Langlands.Group.rootPairingWeylCoxeterStatement_proof

/-- Actual root rays and the public arbitrary-field unipotent product
theorem discharge the ordered-product input under the root-system statement. -/
theorem RootGeneratedCentralizerStructuralPremises.dynamicRootOrderedProduct
    (h : RootGeneratedCentralizerStructuralPremises.{u}) :
    RelativeRoot.DynamicRootOrderedProductStatement.{u} :=
  RelativeRoot.dynamicRootOrderedProduct_of_rayDecomposition
    (RelativeRoot.relativeRootRayDecompositionStatement_of_relativeRootSystemStatement h.1)

/-- The exact target follows from the two stated geometric inputs. This
conditional theorem does not prove either input. -/
theorem rootGeneratedCentralizerRankOne_of_structuralPremises
    (h : RootGeneratedCentralizerStructuralPremises.{u}) :
    RootGeneratedCentralizerRankOneStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hG.smooth
  let := hi.isSplitSubtorus.mono
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  have hroot := h.1 k G hG T i hi
  have hE : RelativeRoot.HasOppositeFactorPairs i :=
    fun a ha x hx hx1 => (h.2 k G hG T i hi a ha x hx hx1).1.exists
  obtain ⟨_, _, C, cs, hcs⟩ := h.relativeWeylCoxeter k G hG T i hi ν hν
  have hSimple : ∀ a : SimpleRoot i ν, IsRelativeReflection i a.val (cs.simple a) :=
    hcs.isRelativeReflection_simple
  have hprod := hasOrderedRootPointFactorization_of_statement
    h.dynamicRootOrderedProduct k G hG T i hi ν
  have hLifts := hasRootGeneratedSimpleReflectionLifts_of_oppositeFactorPairs
    i ν hi.isSplitSubtorus.1 hroot hν hE cs hSimple
  exact centralizer_inf_generatedPoints_le_of_orderedRootPoints
    i ν hG hi hν hroot hprod hE cs hSimple hLifts

end Langlands.GroupScheme

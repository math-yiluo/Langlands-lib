import Langlands.Representation.Geometric.SurvivingCoefficientAdmissibility
import Langlands.Representation.Geometric.CoefficientStabilizerQuotient
import Langlands.Representation.Smooth.Admissibility.CoefficientQuotient
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-! Native quotient admissibility of the actual universal orbit coefficient. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u uR uV

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance stabilizerQuotientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}
  {B : Type uR} [CommRing B]
  {V : Type uV} [AddCommGroup V] [Module B V]

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "T" =>
  pointImage (lQ ≫ q) ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z⁻¹))
    (pointImage p)
local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "NQH" => Subgroup.comap (Subgroup.subtype H)
  (MonoidHom.ker (IsSemidirectDecomposition.projection dQ))

/-- The original stabilizer's target-kernel quotient, acted on through the
original target-intersection section on the same native quotient carrier. -/
def targetStabilizerCoinvariantRepresentation
    (ρ : Representation B H V) :
    Representation B ↥(T) (Jacquet.Coinvariants ρ NQH) :=
  (ρ.toCoinvariants NQH).comp D.targetParabolicPointsToStabilizer

/-- The original quotient map, as an intertwiner for the actual section. -/
def targetStabilizerCoinvariantMap (ρ : Representation B H V) :
    Representation.IntertwiningMap (ρ.comp D.targetParabolicPointsToStabilizer)
      (D.targetStabilizerCoinvariantRepresentation ρ) where
  toLinearMap := Jacquet.mk ρ NQH
  isIntertwining' _ := rfl

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
@[simp]
theorem targetStabilizerCoinvariantMap_apply (ρ : Representation B H V) (v : V) :
    D.targetStabilizerCoinvariantMap ρ v = Jacquet.mk ρ NQH v := rfl

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
theorem targetStabilizerCoinvariantMap_surjective (ρ : Representation B H V) :
    Function.Surjective (D.targetStabilizerCoinvariantMap ρ) :=
  Jacquet.mk_surjective ρ NQH

include D

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The literal target intersection is closed in the original ambient group. -/
theorem isClosed_targetIntersectionPoints : IsClosed (T : Set (rationalPoints G)) := by
  have hc := isClosed_pointImage (D.q' ≫ lQ ≫ q)
    (D.hq'.isClosedSubgroup.comp (hlQ.isClosedSubgroup.comp hq.isClosedSubgroup))
  have heq := congrArg (fun J₀ : Subgroup (rationalPoints G) => (J₀ : Set (rationalPoints G)))
    D.targetParabolicPoints_eq
  exact (congrArg IsClosed heq).mp hc

/-- Actual closedness gives the compact-open cofinality needed for native
coefficient quotient admissibility; it is not an additional hypothesis. -/
theorem targetIntersection_compactOpenCofinal (K : OpenSubgroup ↥(T)) :
    ∃ J : OpenSubgroup ↥(T), IsCompact (J : Set ↥(T)) ∧ J ≤ K := by
  let : LocallyCompactSpace ↥(T) := (D.isClosed_targetIntersectionPoints).locallyCompactSpace
  obtain ⟨J, hJ, hJK⟩ := compactOpenSubgroupBasis ↥(T) (K : Set ↥(T)) K.mem_nhds_one
  exact ⟨J, hJ, hJK⟩

/-- Apply native complex-algebra quotient transport to the original section
coefficient and the actual kernel quotient. -/
theorem targetStabilizerCoinvariantRepresentation_isAdmissible
    [Algebra ℂ B] [IsNoetherianRing B]
    (ρ : Representation B H V)
    (hρ : IsAdmissible (ρ.comp D.targetParabolicPointsToStabilizer)) :
    IsAdmissible (D.targetStabilizerCoinvariantRepresentation ρ) :=
  isAdmissible_of_surjective_coefficients D.targetIntersection_compactOpenCofinal
    (D.targetStabilizerCoinvariantMap ρ)
    (D.targetStabilizerCoinvariantMap_surjective ρ) hρ

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.Plancherel.RationalNormalized

open GroupScheme Aubert.General.RepresentedParabolic
open Langlands.AlgebraicGeometry.PointTopology

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P N : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance universalStabilizerQuotientAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance universalStabilizerQuotientPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance universalStabilizerQuotientFieldT2 : T2Space F :=
  BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : N ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (hmul : IsIso (subgroupMultiplication l n))
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  {Q L U : GroupScheme (Spec (CommRingCat.of F))}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {nQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hnQ : LeviSubgroup.IsGeometricUnipotentRadical nQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ nQ)}
  {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l n r.isCompatible.parabolic hn
    r.isCompatible.levi hmul q lQ nQ hq hnQ hlQ hmulQ z)
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

local instance universalStabilizerQuotientTensorAddCommGroup :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup

/-- The actual universal stabilizer-kernel quotient, with its original
target-intersection section action, is admissible for a surviving piece. -/
theorem universalTargetStabilizerCoinvariant_isAdmissible_of_full
    (hfull : SubgroupFunctor.range D.p' = ⊤)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsAdmissible σ) :
    IsAdmissible (D.targetStabilizerCoinvariantRepresentation
      ((inducingRepresentation r h hU σ).comp
        (Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹))) := by
  let := regularAlgebra_isNoetherianRing r
  exact D.targetStabilizerCoinvariantRepresentation_isAdmissible _
    (universalTargetIntersectionCoefficient_isAdmissible r hn hmul h hU D hfull σ hσ)

/-- Proper pieces vanish; surviving original section coefficients descend
admissibly. Thus every supplied actual geometric intersection gives an
admissible native stabilizer-kernel coefficient quotient over the original B. -/
theorem universalTargetStabilizerCoinvariant_isAdmissible
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (hσ : IsAdmissible σ) (hcusp : IsSupercuspidal r σ) :
    IsAdmissible (D.targetStabilizerCoinvariantRepresentation
      ((inducingRepresentation r h hU σ).comp
        (Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹))) := by
  by_cases hfull : SubgroupFunctor.range D.p' = ⊤
  · exact universalTargetStabilizerCoinvariant_isAdmissible_of_full
      r hn hmul h hU D hfull σ hσ
  · let := universalStabilizerCoinvariants_subsingleton r hn hmul h hU D σ hcusp hfull
    constructor
    · intro v
      refine ⟨⊤, ?_⟩
      intro g
      exact Subsingleton.elim _ _
    · intro K
      infer_instance

end Langlands.Plancherel.RationalNormalized

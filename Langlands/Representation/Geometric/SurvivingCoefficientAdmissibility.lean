import Langlands.Representation.Geometric.SurvivingIntersectionGeometry
import Langlands.Representation.Exponents.MaximalLeviUnitaryCentralTwistReduction
import Langlands.Representation.Plancherel.UnramifiedRationalConjugateAdmissibility

/-! Admissibility of the original coefficient on a surviving target intersection. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u uR uV

private theorem continuous_projection_congr {G₀ : Type*} [Group G₀] [TopologicalSpace G₀]
    {P₀ M₀ U₀ P₁ M₁ U₁ : Subgroup G₀}
    (d₀ : IsSemidirectDecomposition P₀ M₀ U₀)
    (d₁ : IsSemidirectDecomposition P₁ M₁ U₁)
    (hP : P₀ = P₁) (hM : M₀ = M₁) (hU : U₀ = U₁)
    (hd : Continuous d₀.projection) : Continuous d₁.projection := by
  subst P₁ M₁ U₁
  exact hd

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance survivingCoefficientPointTopology : TopologicalSpace (rationalPoints G) :=
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

local notation "T" =>
  pointImage (lQ ≫ q) ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z⁻¹))
    (pointImage p)
local notation "C" =>
  pointImage (lQ ≫ q) ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z⁻¹))
    (pointImage (l ≫ p))
local notation "dP" => isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul

/-- The original full source covariance, restricted through the actual
target-intersection section and inverse orbit conjugation. -/
def targetIntersectionCoefficientRepresentation
    (δ : Induction.SmoothCharacter B (pointImage p))
    (σ : Representation B (pointImage (l ≫ p)) V) : Representation B ↥(T) V :=
  (Langlands.twist δ.toMonoidHom (σ.comp (dP).projection)).comp
    D.targetParabolicPointsToSource

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The actual intersection Levi projection is continuous, through its
represented multiplication isomorphism in the original ambient point topology. -/
theorem continuous_targetIntersectionProjection :
    Continuous D.targetPoints_isSemidirectDecomposition.projection := by
  have hc : IsClosedSubgroup (D.q' ≫ lQ ≫ q) :=
    D.hq'.isClosedSubgroup.comp (hlQ.isClosedSubgroup.comp hq.isClosedSubgroup)
  have hd := continuous_pointImage_projection (D.q' ≫ lQ ≫ q)
    D.lQ' D.rQ' hc D.hrQ' D.hmulQ'
  exact continuous_projection_congr _ D.targetPoints_isSemidirectDecomposition
    D.targetParabolicPoints_eq
    (by simpa only [Category.assoc] using D.targetLeviPoints_eq)
    (by simpa only [Category.assoc] using D.targetRadicalPoints_eq) hd

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)] in
/-- The original target-section coefficient is admissible for a full source
intersection. Full-source conjugation is derived from the geometric datum. -/
theorem targetIntersectionCoefficientRepresentation_isAdmissible
    [IsNoetherianRing B]
    (hfull : SubgroupFunctor.range D.p' = ⊤)
    (δ : Induction.SmoothCharacter B (pointImage p))
    (σ : Representation B (pointImage (l ≫ p)) V) (hσ : IsAdmissible σ) :
    IsAdmissible (D.targetIntersectionCoefficientRepresentation δ σ) := by
  let d := D.targetPoints_isSemidirectDecomposition
  let e := D.survivingIntersectionConjugationEquiv hfull
  have hd : Continuous d.projection := D.continuous_targetIntersectionProjection
  have hinfl : IsAdmissible ((σ.comp e.toMonoidHom).comp d.projection) :=
    (isAdmissible_comp_iff_of_open_surjective _ d.projection hd
      (d.isOpenMap_projection hd)
      (fun m => ⟨Subgroup.inclusion d.levi_le m, d.projection_levi m⟩)).mpr
        (isAdmissible_comp_continuousMulEquiv σ e hσ)
  have hf :
      σ.comp D.targetParabolicPointsToSourceLevi =
        (σ.comp e.toMonoidHom).comp d.projection := by
    apply MonoidHom.ext
    intro x
    apply LinearMap.ext
    intro v
    exact congrArg (fun m => σ m v)
      ((D.targetParabolicPointsToSourceLevi_eq x).trans
        (D.targetLeviPointsToSourceLevi_eq_survivingConjugation hfull (d.projection x)))
  have hδ : IsOpen
      ((δ.toMonoidHom.comp D.targetParabolicPointsToSource).ker : Set ↥(T)) :=
    δ.isOpen_ker.preimage D.continuous_targetParabolicPointsToSource
  change IsAdmissible
    (Langlands.twist (δ.toMonoidHom.comp D.targetParabolicPointsToSource)
      (σ.comp D.targetParabolicPointsToSourceLevi))
  apply (isAdmissible_twist_iff _ _ hδ).mpr
  exact hf.symm ▸ hinfl

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

local instance survivingUniversalAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance survivingUniversalPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance survivingUniversalFieldT2 : T2Space F := BruhatTits.localField_t2Space F

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

local instance survivingUniversalTensorAddCommGroup :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup

/-- The original normalized universal coefficient, pulled back along the
actual target-intersection section, is admissible over its original algebra
for a surviving full source intersection. -/
theorem universalTargetIntersectionCoefficient_isAdmissible
    (hfull : SubgroupFunctor.range D.p' = ⊤)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsAdmissible σ) :
    IsAdmissible ((inducingRepresentation r h hU σ).comp
      D.targetParabolicPointsToSource) := by
  let := regularAlgebra_isNoetherianRing r
  exact D.targetIntersectionCoefficientRepresentation_isAdmissible hfull
    (UnramifiedNormalized.inductionCharacter (parabolicLeviRationalNormCharacters r)
      _ _ hU h.le_normalizer)
    (universalRepresentation r σ) (universalRepresentation_isAdmissible r σ hσ)

end Langlands.Plancherel.RationalNormalized

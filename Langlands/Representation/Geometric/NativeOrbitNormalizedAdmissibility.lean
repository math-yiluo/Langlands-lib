import Langlands.Representation.Geometric.NativeOrbitJacquetComparison
import Langlands.Representation.Geometric.RepresentedParabolicKernelCoinvariants
import Langlands.Representation.Jacquet.CoefficientRestrictedFiltration
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetFinitenessStatement

/-! The actual normalized native orbit quotient and its universal admissibility. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 80000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Induction

universe u uR uV

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance nativeNormalizedPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {Q L U : GroupScheme (Spec (CommRingCat.of k))}
  (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  {B : Type uR} [CommRing B]
  {V : Type uV} [AddCommGroup V] [Module B V]

local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "π" => IsSemidirectDecomposition.projection dQ
local notation "s" => Subgroup.inclusion (IsSemidirectDecomposition.levi_le dQ)
local notation "NQ" => pointImage (rQ ≫ q)
local notation "MQ" => pointImage (lQ ≫ q)
local notation "hMN" => pointImage_le_normalizer q lQ rQ hrQ
local notation "hNQ" => pointImage_comp_le q rQ
local notation "hMQ" => pointImage_comp_le q lQ
local notation "FQ" => Jacquet.Localization.Coefficient.subgroupFunctor
  (R := B) NQ MQ hMN (pointImage q) hNQ hMQ

/-- The original subgroup-localization used by actual support grades is the
ordinary native projection-kernel quotient, on the same representatives. -/
def nativeParabolicProjectionKernelEquiv (ρ : Representation B (pointImage q) V) :
    Representation.Equiv ((FQ).obj (Rep.of ρ)).ρ
      ((ρ.toCoinvariants (π).ker).comp s) := by
  let eK := MulEquiv.subgroupCongr
    (parabolicRadicalPoints_eq_projectionKernel q lQ rQ hq hrQ hmulQ)
  let eT := Jacquet.Localization.transportEquiv ρ ρ
    (parabolicRadicalPoints q rQ) (π).ker 1 1 eK
    (LinearEquiv.refl B V) (fun _ _ => rfl) (fun _ => rfl)
  let hn : (⊤ : Subgroup (pointImage q)) ≤ Subgroup.normalizer (π).ker := by
    simp only [Subgroup.normalizer_eq_top, le_refl]
  let eO := Jacquet.Localization.trivialEquiv ρ (π).ker ⊤ hn
  exact {
    toLinearEquiv := eT.trans eO.toLinearEquiv
    isIntertwining' := by
      intro m
      apply LinearMap.ext
      intro x
      obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective ρ
        (parabolicRadicalPoints q rQ) 1 x
      rfl }

omit [TopologicalSpace k] [T2Space k] [IsAffineHom G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
@[simp]
theorem nativeParabolicProjectionKernelEquiv_mk
    (ρ : Representation B (pointImage q) V) (v : V) :
    nativeParabolicProjectionKernelEquiv q lQ rQ hq hrQ hmulQ ρ
      (Jacquet.Localization.mk ρ (parabolicRadicalPoints q rQ) 1 v) =
      Jacquet.mk ρ (π).ker v := rfl

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.Plancherel.RationalNormalized

set_option backward.isDefEq.respectTransparency.types true

open GroupScheme Aubert.General.RepresentedParabolic Induction
open Langlands.AlgebraicGeometry.PointTopology

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P N : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance universalNativeOrbitAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance universalNativeOrbitPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance universalNativeOrbitFieldT2 : T2Space F :=
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

local instance universalNativeOrbitRegularCommRing : CommRing (RegularAlgebra r) :=
  Subalgebra.toCommRing _
local instance universalNativeOrbitRegularAlgebra : Algebra ℂ (RegularAlgebra r) :=
  Subalgebra.algebra _
local instance universalNativeOrbitTensorAddCommGroup :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup
local instance universalNativeOrbitTensorModule :
    Module (RegularAlgebra r) (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.leftModule

local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ nQ hq.isClosedSubgroup hnQ hmulQ
local notation "s" => Subgroup.inclusion (Aubert.General.IsSemidirectDecomposition.levi_le dQ)
local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "K" => Subgroup.comap s D.compactComparisonSaturation
local notation "NQ" => pointImage (nQ ≫ q)
local notation "MQ" => pointImage (lQ ≫ q)
local notation "hMN" => pointImage_le_normalizer q lQ nQ hnQ
local notation "hNQ" => pointImage_comp_le q nQ
local notation "hMQ" => pointImage_comp_le q lQ
local notation "FQ" => Jacquet.Localization.Coefficient.subgroupFunctor
  (R := RegularAlgebra r) NQ MQ hMN (pointImage q) hNQ hMQ

/-- The canonical inverse output half-modulus on the original output Levi,
as a constant character in the complete source rational-norm algebra. -/
def universalNativeOrbitOutputCharacter : SmoothCharacter (RegularAlgebra r) MQ :=
  UnramifiedNormalized.jacquetCharacter (parabolicLeviRationalNormCharacters r) NQ MQ
    (isClosed_pointImage_comp q nQ hq.isClosedSubgroup hnQ.1.isClosedSubgroup) hMN

/-- The literal native subgroup quotient of the actual compact orbit piece,
with the original inverse output half normalization. -/
def universalNativeOrbitJacquetRepresentation
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :=
  Langlands.twist
    (universalNativeOrbitOutputCharacter (r := r) (q := q) (lQ := lQ)
      (nQ := nQ) (hq := hq) (hnQ := hnQ)).toMonoidHom
    (((FQ).obj (Rep.of (compactInduced (R := RegularAlgebra r) H
      (universalNativeEndpointStabilizerCoefficient r h hU σ)))).ρ)

/-- The actual universal stabilizer coefficient is smooth when the supplied
original inducing projection is continuous. -/
theorem isSmooth_universalNativeEndpointStabilizerCoefficient
    (hproj : Continuous h.projection)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsSmooth σ) :
    IsSmooth (universalNativeEndpointStabilizerCoefficient r h hU
      (q := q) (z := z) σ) := by
  apply isSmooth_comp _ _ (isSmooth_inducingRepresentation r h hU hproj σ hσ)
  exact ((continuous_const.mul
    (continuous_subtype_val.comp continuous_subtype_val)).mul
      continuous_const).subtype_mk _

/-- The original normalized native orbit quotient of the actual universal
supercuspidal family is admissible, retaining only geometric orbit data and
compactness of the original output quotient as additional premises. -/
theorem universalNativeOrbitJacquet_isAdmissible
    [CompactSpace (LeftQuotient K)] (R : D.DynamicRealization)
    (hproj : Continuous h.projection)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (hσ : IsAdmissible σ) (hcusp : IsSupercuspidal r σ) :
    IsAdmissible (R := RegularAlgebra r)
      (universalNativeOrbitJacquetRepresentation r h hU
        (q := q) (lQ := lQ) (nQ := nQ) (hq := hq) (hnQ := hnQ) (z := z) σ) := by
  let := regularAlgebra_isNoetherianRing r
  let ρ := universalNativeEndpointStabilizerCoefficient r h hU (q := q) (z := z) σ
  let : Module (RegularAlgebra r) (CompactFunctions H ρ) := Submodule.module _
  apply (isAdmissible_twist_iff _ _
    (universalNativeOrbitOutputCharacter (r := r) (q := q) (lQ := lQ)
      (nQ := nQ) (hq := hq) (hnQ := hnQ)).isOpen_ker).mpr
  apply isAdmissible_of_equiv
    (nativeParabolicProjectionKernelEquiv
      (B := RegularAlgebra r) (V := CompactFunctions H ρ)
      q lQ nQ hq hnQ hmulQ (compactInduced H ρ)).symm
  exact D.compactComparisonNativeJacquet_isAdmissible
    (B := RegularAlgebra r) (V := RegularAlgebra r ⊗[ℂ] E) R _
    (isSmooth_universalNativeEndpointStabilizerCoefficient r h hU hproj σ hσ.1)
    (universalTargetStabilizerCoinvariant_isAdmissible r hn hmul h hU D σ hσ hcusp)

end Langlands.Plancherel.RationalNormalized

import Langlands.Representation.Geometric.NativeOrbitNormalizedAdmissibility
import Langlands.Representation.Geometric.CoefficientSupportJacquet
import Langlands.Representation.Filtration.SingleSurvivingGrade
import Langlands.Representation.Smooth.Admissibility.Extension

/-! Actual universal native support images and conditional admissibility. -/

noncomputable section
set_option maxHeartbeats 160000
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Geometric.OrderedDoubleCosets

universe uR uG uW

variable {B : Type uR} [CommRing B] [Algebra ℂ B]
  {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [NonarchimedeanGroup Γ]
  [LocallyCompactSpace Γ] [T2Space Γ] [SigmaCompactSpace Γ]
  {P Q : Subgroup Γ} [CompactSpace (Induction.LeftQuotient P)]
  (U M : Subgroup Γ) (hMU : M ≤ Subgroup.normalizer U) (hMQ : M ≤ Q)
  (hUQ : U ≤ Q) (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)

/-- Objectwise evaluation of the native support-grade comparison. -/
def nativeSmoothJacquetSupportGradedOrbitIsoAt
    (hP : IsClosed (P : Set Γ)) (hQ : IsClosed (Q : Set Γ))
    {m : ℕ} (t : OrderedDoubleCosets P Q m)
    (χ : Induction.SmoothCharacter B M) (i : Fin m)
    (X : SmoothRep.{uR, uG, uW} B P) :
    ((t.nativeSmoothJacquetSupportFiltration U M hMU hMQ χ).atObject X).gradedRepresentation i ≅
      (orbitPiece (R := B) P Q (t.representative i) ⋙
        Jacquet.Localization.Coefficient.subgroupFunctor U M hMU Q hUQ hMQ ⋙
          χ.twistFunctor).obj X :=
  (t.nativeSmoothJacquetSupportGradedOrbitIso U M hMU hMQ hUQ hU hP hQ χ i).app X

omit [Algebra ℂ B] [LocallyCompactSpace Γ] [T2Space Γ] [SigmaCompactSpace Γ]
  [CompactSpace (Induction.LeftQuotient P)] in
/-- Finite native support images give admissibility of the original normalized
full smooth induced action when their actual grades are admissible. -/
theorem nativeSmoothJacquetSupport_isAdmissibleAt [IsNoetherianRing B]
    {m : ℕ} (t : OrderedDoubleCosets P Q m)
    (χ : Induction.SmoothCharacter B M) (X : SmoothRep.{uR, uG, uW} B P)
    (hgr : ∀ i : Fin m, IsAdmissible
      (((t.nativeSmoothJacquetSupportFiltration U M hMU hMQ χ).atObject X).gradedRepresentation
        i).ρ) :
    IsAdmissible (twist χ.toMonoidHom
      (Jacquet.Localization.action (Induction.smoothInduced P X.representation)
        U 1 M hMU (Jacquet.Localization.isInvariant_one U M hMU))) := by
  apply isAdmissible_of_objectRepFiltration
    ((t.nativeSmoothJacquetSupportFiltration U M hMU hMQ χ).atObject X)
  · exact (isSmooth_twist_iff _ _ χ.isOpen_ker).mpr
      (Jacquet.Localization.isSmooth_action _ U 1 M hMU
        (Jacquet.Localization.isInvariant_one U M hMU)
        (Induction.smoothInduced_smooth _ _))
  · exact hgr

end Langlands.Geometric.OrderedDoubleCosets

namespace Langlands.Plancherel.RationalNormalized

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

local instance nativeSupportAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance nativeSupportPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance nativeSupportFieldT2 : T2Space F :=
  BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : N ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  {Q L U : GroupScheme (Spec (CommRingCat.of F))}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {nQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hnQ : LeviSubgroup.IsGeometricUnipotentRadical nQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ nQ)}
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

local instance nativeSupportRegularCommRing : CommRing (RegularAlgebra r) :=
  Subalgebra.toCommRing _
local instance nativeSupportRegularAlgebra : Algebra ℂ (RegularAlgebra r) :=
  Subalgebra.algebra _
local instance nativeSupportTensorAddCommGroup :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup
local instance nativeSupportTensorModule :
    Module (RegularAlgebra r) (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.leftModule

local notation "NQ" => pointImage (nQ ≫ q)
local notation "MQ" => pointImage (lQ ≫ q)
local notation "hMN" => pointImage_le_normalizer q lQ nQ hnQ
local notation "hNQ" => pointImage_comp_le q nQ
local notation "hMQ" => pointImage_comp_le q lQ
local notation "ηQ" =>
  universalNativeOrbitOutputCharacter (r := r) (q := q) (lQ := lQ)
    (nQ := nQ) (hq := hq) (hnQ := hnQ)

/-- The original universal inducing action, bundled only with its proved
smoothness; the positive source normalization is unchanged. -/
def universalNativeJacquetInducingInput
    (hproj : Continuous h.projection)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsSmooth σ) :=
  SmoothRep.of (inducingRepresentation r h hU σ)
    (isSmooth_inducingRepresentation r h hU hproj σ hσ)

/-- The actual finite support-image filtration on the original full universal
induction's native quotient, with the inverse output half normalization. -/
def universalNativeJacquetSupportFiltration
    (hproj : Continuous h.projection)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsSmooth σ)
    {m : ℕ} (t : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m) :=
  (t.nativeSmoothJacquetSupportFiltration NQ MQ hMN hMQ ηQ).atObject
    (universalNativeJacquetInducingInput r h hU hproj σ hσ)

/-- Evaluation of the original compact orbit functor retains its covariance
representation and canonical module structure. -/
theorem universalNativeJacquetOrbitPiece_eq
    (hproj : Continuous h.projection)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsSmooth σ)
    (z : rationalPoints G) :
    (Geometric.orbitPiece (R := RegularAlgebra r) (pointImage p) (pointImage q) z⁻¹).obj
      (universalNativeJacquetInducingInput r h hU hproj σ hσ) =
      Rep.of (compactInduced (R := RegularAlgebra r)
        (Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹)
        (universalNativeEndpointStabilizerCoefficient r h hU (q := q) (z := z) σ)) := by
  rfl

/-- The evaluated native orbit functor is the same normalized orbit action. -/
def universalNativeJacquetOrbitFunctorIso
    (hproj : Continuous h.projection)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsSmooth σ)
    (z : rationalPoints G) :
    (Geometric.orbitPiece (R := RegularAlgebra r) (pointImage p) (pointImage q) z⁻¹ ⋙
      Jacquet.Localization.Coefficient.subgroupFunctor NQ MQ hMN (pointImage q) hNQ hMQ ⋙
        (ηQ).twistFunctor).obj
          (universalNativeJacquetInducingInput r h hU hproj σ hσ) ≅
      Rep.of (universalNativeOrbitJacquetRepresentation r h hU
        (q := q) (lQ := lQ) (nQ := nQ) (hq := hq) (hnQ := hnQ) (z := z) σ) := by
  apply eqToIso
  rfl

variable [T2Space (rationalPoints G)] [SigmaCompactSpace (rationalPoints G)]
  [CompactSpace (LeftQuotient (pointImage p))]

set_option maxHeartbeats 800000 in
/-- Each actual native support grade is the original normalized orbit quotient.
The orbit convention uses the inverse of the ordered representative as `z`. -/
def universalNativeJacquetSupportGradedOrbitIso
    (hproj : Continuous h.projection)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsSmooth σ)
    {m : ℕ} (t : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m)
    (i : Fin m) :
  (universalNativeJacquetSupportFiltration r h hU (q := q) (lQ := lQ)
      (nQ := nQ) (hq := hq) (hnQ := hnQ) hproj σ hσ t).gradedRepresentation i ≅
      Rep.of (universalNativeOrbitJacquetRepresentation r h hU
        (q := q) (lQ := lQ) (nQ := nQ) (hq := hq) (hnQ := hnQ)
        (z := (t.representative i)⁻¹) σ) := by
  let T := fun w : rationalPoints G =>
    (Geometric.orbitPiece (R := RegularAlgebra r) (pointImage p) (pointImage q) w ⋙
      Jacquet.Localization.Coefficient.subgroupFunctor NQ MQ hMN (pointImage q) hNQ hMQ ⋙
        (ηQ).twistFunctor).obj
          (universalNativeJacquetInducingInput r h hU hproj σ hσ)
  let e := t.nativeSmoothJacquetSupportGradedOrbitIsoAt
      (B := RegularAlgebra r) NQ MQ hMN hMQ hNQ
      (isLimitOfCompactSubgroups_pointImage_radical q nQ hq.isClosedSubgroup hnQ.1)
      (isClosed_pointImage p r.isCompatible.parabolic.isClosedSubgroup)
      (isClosed_pointImage q hq.isClosedSubgroup) ηQ i
      (universalNativeJacquetInducingInput r h hU hproj σ hσ)
  have hi : ((t.representative i)⁻¹)⁻¹ = t.representative i := inv_inv _
  have ht : T (t.representative i) = T ((t.representative i)⁻¹)⁻¹ :=
    congrArg T hi.symm
  let e₁ : T (t.representative i) ≅ T ((t.representative i)⁻¹)⁻¹ :=
    eqToIso ht
  let e₂ : T (t.representative i) ≅
      Rep.of (universalNativeOrbitJacquetRepresentation r h hU
        (q := q) (lQ := lQ) (nQ := nQ) (hq := hq) (hnQ := hnQ)
        (z := (t.representative i)⁻¹) σ) :=
    e₁ ≪≫ universalNativeJacquetOrbitFunctorIso r h hU hproj σ hσ (t.representative i)⁻¹
  have ha :
      (universalNativeJacquetSupportFiltration r h hU (q := q) (lQ := lQ)
        (nQ := nQ) (hq := hq) (hnQ := hnQ) hproj σ hσ t).gradedRepresentation i =
      ((t.nativeSmoothJacquetSupportFiltration NQ MQ hMN hMQ ηQ).atObject
        (universalNativeJacquetInducingInput r h hU hproj σ hσ)).gradedRepresentation i := rfl
  with_reducible exact eqToIso ha ≪≫ (e ≪≫ e₂)

set_option maxHeartbeats 800000 in
/-- Admissibility of the actual full universal native Jacquet family follows
from finite ordered orbit geometry, actual dynamically realized intersection
data, and compactness of the original output quotient for each orbit. -/
theorem universalNativeJacquet_isAdmissible
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication l n))
    (hproj : Continuous h.projection)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (hσ : IsAdmissible σ) (hcusp : IsSupercuspidal r σ)
    {m : ℕ} (t : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m)
    (D : ∀ i : Fin m, GeometricLemmaIntersectionDatum p l n
      r.isCompatible.parabolic hn r.isCompatible.levi hmul
      q lQ nQ hq hnQ hlQ hmulQ (t.representative i)⁻¹)
    (R : ∀ i : Fin m, (D i).DynamicRealization)
    (hcompact : ∀ i : Fin m, CompactSpace (LeftQuotient
      (Subgroup.comap
        (Subgroup.inclusion (Aubert.General.IsSemidirectDecomposition.levi_le
          (isSemidirectDecomposition_pointImage q lQ nQ hq.isClosedSubgroup hnQ hmulQ)))
        (D i).compactComparisonSaturation))) :
    IsAdmissible (R := RegularAlgebra r)
      (UnramifiedNormalized.jacquetRepresentation (parabolicLeviRationalNormCharacters r)
        (inducedRepresentation r h hU σ) NQ MQ
        (isClosed_pointImage_comp q nQ hq.isClosedSubgroup hnQ.1.isClosedSubgroup) hMN) := by
  let := regularAlgebra_isNoetherianRing r
  apply Geometric.OrderedDoubleCosets.nativeSmoothJacquetSupport_isAdmissibleAt
    NQ MQ hMN hMQ t ηQ (universalNativeJacquetInducingInput r h hU hproj σ hσ.1)
  intro i
  let := hcompact i
  let e := universalNativeJacquetSupportGradedOrbitIso r h hU
    (q := q) (lQ := lQ) (nQ := nQ) (hq := hq) (hnQ := hnQ) hproj σ hσ.1 t i
  have horbit := universalNativeOrbitJacquet_isAdmissible r hn hmul h hU
    (D i) (R i) hproj σ hσ hcusp
  exact isAdmissible_of_equiv (Representation.equivOfIso e).symm horbit

end Langlands.Plancherel.RationalNormalized

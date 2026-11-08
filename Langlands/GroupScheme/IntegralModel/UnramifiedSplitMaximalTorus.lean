import Langlands.GroupScheme.IntegralModel.UnramifiedModelClassification
import Langlands.GroupScheme.Torus.StrictHenselianMaximal
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # A split maximal torus of the generic fibre of the unramified model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

/-- The generic fibre of an integral homomorphism from a commutative group scheme
into the model, followed by the supplied generic identification of the model. -/
def genericTorusMap (T : CommGroupScheme (Spec (CommRingCat.of R)))
    (i : T.toGrp ⟶ M.group) :
    ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T).toGrp ⟶ G :=
  (GroupScheme.baseChange (Spec.algebraMap R K)).map i ≫ M.genericIso.hom

/-- If a torus map into a smooth affine model is maximal on every residue-field
fibre, its generic fibre, read through the supplied generic identification, is a
maximal torus of the generic group. -/
theorem isMaximalTorus_genericTorusMap [Smooth M.group.X.hom]
    [IsAffineHom M.group.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of R))) (i : T.toGrp ⟶ M.group)
    (hi : IsFibrewiseMaximalTorus i) :
    IsMaximalTorus (M.genericTorusMap T i) :=
  (hi.fieldPoint (Spec.algebraMap R K)).comp_iso M.genericIso

/-- Over a strictly Henselian local domain, a reductive model contains an actual
closed split torus whose generic fibre, read through the supplied generic
identification, is a maximal torus and a maximal split torus of the generic group. -/
theorem exists_isSplitTorus_isMaximalSplitTorus_genericTorusMap
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (hM : IsReductive M.group) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of R))) (i : T.toGrp ⟶ M.group),
      IsSplitTorus T.toGrp ∧ IsClosedSubgroup i ∧
        IsMaximalTorus (M.genericTorusMap T i) ∧
          IsMaximalSplitTorus (M.genericTorusMap T i) := by
  obtain ⟨T, i, hT, hic, hmax⟩ := strictHenselianSplitMaximalTorus R M.group hM
  let := hM.smooth
  let := hM.isAffineHom
  have hgen : IsMaximalTorus (M.genericTorusMap T i) :=
    M.isMaximalTorus_genericTorusMap T i hmax
  exact ⟨T, i, hT, hic, hgen,
    hgen.isMaximalSplitTorus (hT.baseChange (Spec.algebraMap R K))⟩

end Langlands.GroupScheme.IntegralModel

namespace Langlands.GroupScheme.IntegralModel

open Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

local instance unramifiedSplitMaximalTorusAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedSplitMaximalTorusIsScalarTower : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- The supplied good local model, base changed to the actual maximal-unramified
integers, contains a closed split torus whose generic fibre is a maximal torus
and a maximal split torus of the base-changed generic group. -/
theorem exists_isMaximalSplitTorus_baseChangeUnramified
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group)) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F))))
      (i : T.toGrp ⟶ M.baseChangeUnramified.group),
      IsSplitTorus T.toGrp ∧ IsClosedSubgroup i ∧
        IsMaximalTorus (M.baseChangeUnramified.genericTorusMap T i) ∧
          IsMaximalSplitTorus (M.baseChangeUnramified.genericTorusMap T i) := by
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let := (residueToFixedField F).toAlgebra
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    IsAlgClosure.isAlgClosed 𝓀[F]
  exact M.baseChangeUnramified.exists_isSplitTorus_isMaximalSplitTorus_genericTorusMap
    (M.isReductive_baseChangeUnramified hG hSpecial)

end Langlands.GroupScheme.IntegralModel

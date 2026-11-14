import Langlands.GroupScheme.IntegralModel.CommonSpecialFibreTorus
import Langlands.GroupScheme.Torus.GeometricHomMaximal
import Langlands.BruhatTits.IntegralModels.UnramifiedComponentModelComparison
import Langlands.GroupScheme.Descent.SquareSemilinear
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Maximal residue tori through actual coefficient extensions of models -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

section ResidueSquare

variable {R A : Type u} [CommRing R] [CommRing A]
  [IsLocalRing R] [IsLocalRing A] [Algebra R A]
  [IsLocalHom (algebraMap R A)]

/-- The actual coefficient map and its induced residue map give a commuting
square of affine schemes. -/
theorem residue_coefficient_square :
    Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A) ≫
        residueBaseMap R =
      residueBaseMap A ≫ Spec.algebraMap R A := by
  rw [residueBaseMap, residueBaseMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

end ResidueSquare

section Coefficients

variable {R K A L : Type u}
  [CommRing R] [IsDomain R] [IsLocalRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  [CommRing A] [IsDomain A] [IsLocalRing A] [Field L]
  [Algebra R A] [IsLocalHom (algebraMap R A)]
  [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M N : IntegralModel R K G)

/-- The canonical comparison of the residue fibre after coefficient extension
with the coefficient extension of the original residue fibre. -/
def specialFibreCoefficientIso :
    (GroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).obj
        M.specialFibre ≅ (M.baseChange A L).specialFibre :=
  Descent.squareComparison (residueBaseMap R)
    (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))
    (Spec.algebraMap R A) (residueBaseMap A) residue_coefficient_square M.group

/-- The canonical residue comparisons carry the actual pulled-back model map
to the actual residue map of the coefficient-extended model map. -/
theorem specialFibreCoefficientIso_naturality (φ : M.Hom N (𝟙 G)) :
    (GroupScheme.baseChange
        (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).map
          φ.specialFibreMap ≫ (N.specialFibreCoefficientIso (A := A) (L := L)).hom =
      (M.specialFibreCoefficientIso (A := A) (L := L)).hom ≫
        (φ.baseChangeIdentity A L).specialFibreMap := by
  exact Descent.squareComparison_naturality (residueBaseMap R)
    (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))
    (Spec.algebraMap R A) (residueBaseMap A) residue_coefficient_square φ.hom

end Coefficients

section Bounded

variable {R K A L : Type u}
  [CommRing R] [IsDomain R] [IsLocalRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  [CommRing A] [IsDomain A] [Field L]
  [IsNoetherianRing A] [ValuationRing A] [HenselianLocalRing A]
  [Algebra R A] [IsLocalHom (algebraMap R A)]
  [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [IsAlgClosed (IsLocalRing.ResidueField A)]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {M N : IntegralModel R K G}
  [Smooth M.group.X.hom] [Smooth N.group.X.hom]
  [ConnectedSpace M.specialFibre.X.left]

/-- A bounded generic maximal split torus after coefficient extension proves
preservation of every original-residue maximal torus by the model map. -/
theorem Hom.isMaximalTorus_specialFibreMap_of_coefficient_bounded
    (φ : M.Hom N (𝟙 G))
    (hG : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G))
    {Γ₀ : Type u} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation L Γ₀) (hv : ∀ a : Aˣ, v (algebraMap A L (a : A)) = 1)
    {T : CommGroupScheme (Spec (CommRingCat.of L))}
    {iT : T.toGrp ⟶ (GroupScheme.baseChange (Spec.algebraMap K L)).obj G}
    (hiT : IsMaximalSplitTorus iT)
    (hb : (Langlands.Geometry.Building.characterValuationKernel v T.toGrp).map
      (rationalPoints.map iT) ≤ (M.baseChange A L).integralPoints)
    {S : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    {s : S.toGrp ⟶ M.specialFibre} (hs : IsMaximalTorus s) :
    IsMaximalTorus (s ≫ φ.specialFibreMap) := by
  let : Smooth (M.baseChange A L).group.X.hom :=
    M.isSmooth_baseChange A L (inferInstance : Smooth M.group.X.hom)
  let : Smooth (N.baseChange A L).group.X.hom :=
    N.isSmooth_baseChange A L (inferInstance : Smooth N.group.X.hom)
  let : Smooth M.specialFibre.X.hom := by
    change Smooth (pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  let : IsAffineHom M.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  let : IsAffineHom N.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd N.group.X.hom (residueBaseMap R))
    infer_instance
  obtain ⟨U, iU, hU, hUφ⟩ :=
    (φ.baseChangeIdentity A L).exists_common_maximalTorus_specialFibre_of_bounded
      hG v hv hiT hb
  let eM := M.specialFibreCoefficientIso (A := A) (L := L)
  let eN := N.specialFibreCoefficientIso (A := A) (L := L)
  apply hs.comp_of_common_geometric_maximalTorus
    (K := IsLocalRing.ResidueField A) φ.specialFibreMap
  refine ⟨U, iU ≫ eM.inv, hU.comp_iso eM.symm, ?_⟩
  have hφ :
      eM.inv ≫ (GroupScheme.baseChange
          (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).map
            φ.specialFibreMap =
        (φ.baseChangeIdentity A L).specialFibreMap ≫ eN.inv := by
    apply (cancel_mono eN.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [specialFibreCoefficientIso_naturality, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, hφ, Iso.symm_hom] using hUφ.comp_iso eN.symm

/-- The common torus constructed after coefficient extension also guarantees
existence of a maximal torus over the original residue field with maximal
composite, without descending that particular geometric torus. -/
theorem Hom.exists_maximalTorus_specialFibreMap_of_coefficient_bounded
    (φ : M.Hom N (𝟙 G))
    (hG : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G))
    {Γ₀ : Type u} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation L Γ₀) (hv : ∀ a : Aˣ, v (algebraMap A L (a : A)) = 1)
    {T : CommGroupScheme (Spec (CommRingCat.of L))}
    {iT : T.toGrp ⟶ (GroupScheme.baseChange (Spec.algebraMap K L)).obj G}
    (hiT : IsMaximalSplitTorus iT)
    (hb : (Langlands.Geometry.Building.characterValuationKernel v T.toGrp).map
      (rationalPoints.map iT) ≤ (M.baseChange A L).integralPoints) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
      (s : S.toGrp ⟶ M.specialFibre),
      IsMaximalTorus s ∧ IsMaximalTorus (s ≫ φ.specialFibreMap) := by
  let : Smooth M.specialFibre.X.hom := by
    change Smooth (pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  let : IsAffineHom M.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  obtain ⟨S, s, hs⟩ :=
    maximalTorusExistence (IsLocalRing.ResidueField R) M.specialFibre
  exact ⟨S, s, hs, φ.isMaximalTorus_specialFibreMap_of_coefficient_bounded hG v hv hiT hb hs⟩

end Bounded

/-- Boundedness of a maximal split generic torus after an actual local
coefficient extension forces maximal-torus preservation on original special
fibres, and gives an original-field common maximal torus. -/
def CoefficientBoundedTorusSpecialFibreStatement : Prop :=
  ∀ (R K A L : Type u)
    [CommRing R] [IsDomain R] [IsLocalRing R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [CommRing A] [IsDomain A] [Field L]
    [IsNoetherianRing A] [ValuationRing A] [HenselianLocalRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)]
    [Algebra A L] [IsFractionRing A L]
    [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (G : GroupScheme (Spec (CommRingCat.of K)))
    (_hG : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G))
    (M N : IntegralModel R K G)
    [Smooth M.group.X.hom] [Smooth N.group.X.hom]
    [ConnectedSpace M.specialFibre.X.left] (φ : M.Hom N (𝟙 G))
    (Γ₀ : Type u) [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation L Γ₀) (_hv : ∀ a : Aˣ, v (algebraMap A L (a : A)) = 1)
    (T : CommGroupScheme (Spec (CommRingCat.of L)))
    (iT : T.toGrp ⟶ (GroupScheme.baseChange (Spec.algebraMap K L)).obj G),
    IsMaximalSplitTorus iT →
    (Langlands.Geometry.Building.characterValuationKernel v T.toGrp).map
      (rationalPoints.map iT) ≤ (M.baseChange A L).integralPoints →
    (∀ (S : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
      (s : S.toGrp ⟶ M.specialFibre),
      IsMaximalTorus s → IsMaximalTorus (s ≫ φ.specialFibreMap)) ∧
    (∃ (S : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
      (s : S.toGrp ⟶ M.specialFibre),
      IsMaximalTorus s ∧ IsMaximalTorus (s ≫ φ.specialFibreMap))

/-- Construct a common torus upstairs, compare actual residue pullbacks,
and use geometric conjugacy and original-field torus existence. -/
theorem coefficientBoundedTorusSpecialFibre :
    CoefficientBoundedTorusSpecialFibreStatement.{u} := by
  intro R K A L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G hG M N _ _ _ φ
    Γ₀ _ v hv T iT hiT hb
  exact ⟨fun S s hs =>
    φ.isMaximalTorus_specialFibreMap_of_coefficient_bounded hG v hv hiT hb hs,
    φ.exists_maximalTorus_specialFibreMap_of_coefficient_bounded hG v hv hiT hb⟩

end Langlands.GroupScheme.IntegralModel

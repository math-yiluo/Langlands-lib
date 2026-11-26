import Langlands.Geometry.Building.KPZeroDatumConstruction
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.SimplyConnected.FieldExtensionProof
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.IntegralModel.UnramifiedBuildingSemilinearAction
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescent
import Langlands.GroupScheme.IntegralModel.SmoothHomExtension
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement
import Langlands.BruhatTits.IntegralModels.RelativeComponentModelLemmas
import Langlands.BruhatTits.IntegralModels.RelativeComponentFunctoriality
import Langlands.Geometry.Building.UnramifiedZeroDescentStatement

/-! # Integral models over `𝒪[F]` from parahoric models over the maximal unramified integers -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A simply connected derived cover stays one after any extension of the ground field. -/
theorem IsSimplyConnectedDerivedCover.baseChange_field {k K : Type u} [Field k] [Field K]
    [Algebra k K] {G D C : GroupScheme (Spec (CommRingCat.of k))} {d : D ⟶ G} {π : C ⟶ D}
    (h : IsSimplyConnectedDerivedCover d π) :
    IsSimplyConnectedDerivedCover
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map d)
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map π) := by
  let : IsAffineHom G.X.hom := h.isConnectedReductive.isAffineHom
  let : Smooth G.X.hom := h.isConnectedReductive.smooth
  exact ⟨connectedReductiveFieldExtensionStatement k K G h.isConnectedReductive,
    (derivedSubgroupFieldBaseChange k K G D d h.isDerivedSubgroup).1,
    isSimplyConnectedCover_fieldExtension k K C D π h.isSimplyConnectedCover⟩

end Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building LocalGalois.Separable GaloisPointComparison IntegralModel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Zero-subgroup data over the maximal unramified extension, from the base change of the
simply connected derived cover stored in a parahoric building datum. -/
def unramifiedZeroDatumOfParahoric {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G) :
    UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G) :=
  UnramifiedZeroDatum.ofDerivedCover _ _
    P.zeroDatum.isSimplyConnectedDerivedCover.baseChange_field

private instance unramifiedModelFamilyAffineHom {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

local instance unramifiedModelFamilyAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedModelFamilyScalarTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- Elements of `G(K)` fixing a set pointwise keep doing so after Galois conjugation, when the
set is fixed pointwise by the semilinear action. -/
theorem rationalConjugate_mem_pointwiseFixer {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom]
    {C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
    (Dσ : MaximalUnramified.SemilinearApartmentData C) {Y : Set C.ReducedBuilding}
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (hY : ∀ y ∈ Y, Dσ.action σ y = y)
    {x : rationalPoints (baseChanged F (inertiaFixedField F) G)}
    (hx : x ∈ C.pointwiseFixer Y) :
    rationalConjugate F (inertiaFixedField F) G σ x ∈ C.pointwiseFixer Y := by
  rw [IntegerValuationBuildingData.pointwiseFixer, KPApartmentData.mem_pointwiseFixer] at hx ⊢
  intro y hy
  have h := Dσ.action_smul σ x y
  rw [hx y hy, hY y hy] at h
  exact h.symm

set_option maxHeartbeats 2000000 in
/-- **One model over `𝒪[F]`.** Let `Y` be a translate `g · Ya` of a nonempty bounded subset of
the apartment of supplied building data `C` over the maximal unramified extension, fixed
pointwise by the supplied semilinear Galois action. Assume the parahoric model theorems over
`K` (KP 8.3.2 and 8.3.13), smooth model descent (KP Fact 2.10.16) and Galois stability of
`G(K)^1` (the first clause of `UnramifiedZeroDescentStatement`). Then there is a
relative-component datum over `𝒪[F]` whose base changes to the maximal unramified integers
have integral points `G(K)^1 ∩ Fix(Y)` and `G(K)^0 ∩ Fix(Y)`. -/
theorem exists_relativeComponentModelData_of_unramified
    (hpar : UnramifiedParahoricModelStatement.{u})
    (hdesc : UnramifiedSmoothModelDescentStatement.{u})
    (hzero : UnramifiedZeroDescentStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
    (Dσ : MaximalUnramified.SemilinearApartmentData C)
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (Y : Set C.ReducedBuilding)
    (hY : ∃ (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
      (Ya : Set C.Apartment), Ya.Nonempty ∧ (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ya)) ∧
        Y = (fun x => g • C.apartmentMap x) '' Ya)
    (hfix : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F), ∀ y ∈ Y,
      Dσ.action σ y = y) :
    ∃ D : RelativeComponentModelData ↥𝒪[F] F G,
      D.full.baseChangeUnramified.integralPoints =
          characterValuationKernel (MaximalUnramified.valuation F)
              (baseChanged F (inertiaFixedField F) G) ⊓ C.pointwiseFixer Y ∧
        D.neutral.baseChangeUnramified.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer Y := by
  obtain ⟨g, Ya, hne, hb, rfl⟩ := hY
  obtain ⟨DK, hfull, hneut⟩ := hpar F G C E g Ya hne hb
  have hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ∀ x ∈ DK.full.integralPoints,
        rationalConjugate F (inertiaFixedField F) G σ x ∈ DK.full.integralPoints := by
    have h1 := (hzero F G hG).1
    intro σ x hx
    rw [hfull] at hx ⊢
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hc1 := h1 σ x hx1
    have hc2 := rationalConjugate_mem_pointwiseFixer Dσ σ (hfix σ) hx2
    exact Subgroup.mem_inf.mpr ⟨hc1, hc2⟩
  obtain ⟨M, hMs, ⟨iso⟩⟩ := hdesc F G DK.full DK.full_smooth hstable
  let : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨D, hD⟩ := RelativeComponentModelData.exists_full_eq M hMs
  subst hD
  refine ⟨D, iso.integralPoints_eq.trans hfull, ?_⟩
  exact (D.baseChange_neutral_integralPoints_eq (fixedFieldIntegers F) (inertiaFixedField F)
    DK iso).trans hneut

end Langlands.BruhatTits.IntegralModels

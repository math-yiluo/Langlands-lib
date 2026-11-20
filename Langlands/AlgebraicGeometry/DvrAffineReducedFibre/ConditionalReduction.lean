import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.AffineSpecialFibre
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.CompleteBaseReduction
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.FiniteDvrExtension
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.FiniteNormalization
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.SchemeNormalizationAffine
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.SmoothFibreStalk
import Langlands.CommutativeAlgebra.CompleteLocalNormalizationFiniteness

/-! # The affine reduced fibre theorem from the two named premises -/

open AlgebraicGeometry CategoryTheory IsLocalRing Limits TensorProduct Topology
open Langlands.CommutativeAlgebra

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

private theorem isReduced_fibre_stalk_of_smooth_neighbourhoods
    {X Y B : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B} [LocallyOfFinitePresentation f]
    (e : X ≅ Y) (he : e.hom ≫ g = f) (b : B)
    (hsmooth : ∀ y : f.fiber b, y ∈ genericPoints (f.fiber b) →
      ∃ U : X.Opens, f.fiberι b y ∈ U ∧ Smooth (f.resLE ⊤ U le_top))
    (x : g.fiber b) (hx : x ∈ genericPoints (g.fiber b)) :
    _root_.IsReduced ((g.fiber b).presheaf.stalk x) := by
  let r := B.fromSpecResidueField b
  have hrs : g ≫ 𝟙 B = e.inv ≫ f := by rw [Category.comp_id, ← he, Iso.inv_hom_id_assoc]
  have hrr : r ≫ 𝟙 B = 𝟙 (Spec (B.residueField b)) ≫ r := by simp
  let ef : pullback g r ≅ pullback f r := asIso (pullback.map g r f r e.inv (𝟙 _) (𝟙 _) hrs hrr)
  have hy : ef.hom x ∈ genericPoints (f.fiber b) :=
    mem_genericPoints_of_homeomorph (Scheme.homeoOfIso ef) hx
  obtain ⟨U, hyU, hSmoothU⟩ := hsmooth (ef.hom x) hy
  have : Smooth (U.ι ≫ f) := by
    rw [← f.resLE_comp_ι (show U ≤ f ⁻¹ᵁ (⊤ : B.Opens) from le_top)]
    infer_instance
  have hySmooth : f.fiberι b (ef.hom x) ∈ f.smoothLocus := by
    change (⟨f.fiberι b (ef.hom x), hyU⟩ : U) ∈ U.ι ⁻¹ᵁ f.smoothLocus
    rw [Scheme.Hom.preimage_smoothLocus_eq, (U.ι ≫ f).smoothLocus_eq_top]
    trivial
  have : _root_.IsReduced ((pullback f r).presheaf.stalk (ef.hom x)) :=
    isReduced_fibre_stalk_of_mem_smoothLocus f b (ef.hom x) hySmooth
  have : IsIso (ef.hom.stalkMap x) := ((isIso_iff_isIso_stalkMap ef.hom).mp ef.isIso_hom).2 x
  let estalk := (asIso (ef.hom.stalkMap x)).commRingCatIsoToRingEquiv.symm
  exact isReduced_of_injective estalk.toRingHom estalk.injective

section Affine

variable (S D : Type u) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [IsAdicComplete (maximalIdeal S) S] [PerfectField (ResidueField S)]
    [CommRing D] [Algebra S D] [Module.Flat S D] [Algebra.FiniteType S D]
    [Algebra.Smooth (FractionRing S) (FractionRing S ⊗[S] D)]

local notation "G" => D ⊗[S] FractionRing S
local notation "N" => integralClosure D (D ⊗[S] FractionRing S)

private theorem affineNormalization_finite_and_reduced_of_smooth_neighbourhoods
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (e : X ≅ Spec (CommRingCat.of D)) (he : e.hom ≫ Spec.algebraMap S D = f)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hSmoothAt : let h := schemeNormalizationHom X hX ≫ f
      ∀ y : h.fiber (closedPoint S), y ∈ genericPoints (h.fiber (closedPoint S)) →
        ∃ U : (schemeNormalization X hX).Opens, h.fiberι (closedPoint S) y ∈ U ∧
          Smooth (h.resLE ⊤ U le_top)) :
    Module.Finite D N ∧
      ∀ (F : Type u) [Field F] [Algebra S F], IsReduced (F ⊗[S] N) := by
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing S D
  have : IsReduced (FractionRing S ⊗[S] D) :=
    SmoothReducedProof.isReduced_of_smooth_of_domain (FractionRing S) (FractionRing S ⊗[S] D)
  have : IsReduced G := isReduced_of_injective (Algebra.TensorProduct.comm S D _).toRingHom
    (Algebra.TensorProduct.comm S D _).injective
  have hDG : Function.Injective (algebraMap D G) := by
    intro a b hab
    let j : G →ₐ[D] FractionRing D := genericFibreTotalFractionsMap S D
    exact IsFractionRing.injective D (FractionRing D)
      ((j.commutes a).symm.trans ((congrArg j hab).trans (j.commutes b)))
  have : IsReduced D := isReduced_of_injective (algebraMap D G) hDG
  have : IsIntegrallyClosed G := isIntegrallyClosed_genericFibre S D
  have hFiniteN : Module.Finite D N := finite_integralClosure_genericFibre_of_completeDvr S D
  have : IsNoetherianRing N := IsNoetherianRing.of_finite D N
  let n := schemeNormalizationHom X hX ≫ f
  let a := Spec.algebraMap S N
  let eN := schemeNormalizationGenericFibreIso S D e hX
  have hComp : Spec.algebraMap D N ≫ Spec.algebraMap S D = a := by
    simp only [a, Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq S D N]
  have heN : eN.hom ≫ a = n := by
    rw [← hComp, ← Category.assoc, schemeNormalizationGenericFibreIso_hom_comp,
      Category.assoc, he]
  have : Algebra.FiniteType S N := Algebra.FiniteType.trans (S := D) inferInstance inferInstance
  have : LocallyOfFinitePresentation a := by
    dsimp only [a, Spec.algebraMap]
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : LocallyOfFinitePresentation n := by rw [← heN]; infer_instance
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hRegular : algebraMap S N π ∈ nonZeroDivisors N := by
    have hUnit : IsUnit (algebraMap S G π) := by
      let : Algebra (FractionRing S) G := Algebra.TensorProduct.rightAlgebra
      have : IsScalarTower S (FractionRing S) G := Algebra.TensorProduct.right_isScalarTower
      rw [IsScalarTower.algebraMap_apply S (FractionRing S) G]
      have hπK : algebraMap S (FractionRing S) π ≠ 0 := by
        rw [← map_zero (algebraMap S (FractionRing S))]
        exact (IsFractionRing.injective S (FractionRing S)).ne hπ.ne_zero
      exact (isUnit_iff_ne_zero.mpr hπK).map (algebraMap (FractionRing S) G)
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    apply Subtype.ext
    have hx' := congrArg (fun z : N => z.val) hx
    change algebraMap S G π * x.val = 0 at hx'
    exact hUnit.mul_right_eq_zero.mp hx'
  have hReduced : IsReduced (ResidueField S ⊗[S] N) :=
    isReduced_residueTensor_of_isReduced_at_genericPoints S N hπ.maximalIdeal_eq hRegular
      (fun p _ => normal_localizations_genericNormalization S D p)
      (isReduced_fibre_stalk_of_smooth_neighbourhoods eN heN (closedPoint S) hSmoothAt)
  refine ⟨hFiniteN, ?_⟩
  apply isReduced_tensor_integralClosure_of_residue_test S D (E := ResidueField S)
  let eκ := Algebra.TensorProduct.lid (ResidueField S) (ResidueField S ⊗[S] N)
  exact isReduced_of_injective eκ.toRingHom eκ.injective

end Affine

/-- The named scheme theorem gives the complete-base affine assertion using
universal Japanese finiteness to supply the scheme theorem's Nagata hypothesis. -/
theorem completeBase_of_normalizationFiniteness_and_scheme
    (hFiniteness : CompleteLocalNormalizationFinitenessStatement.{u})
    (hScheme : SchemeReducedFibreStatement.{u, u}) :
    DvrAffineReducedFibreCompleteBaseStatement.{u} := by
  intro R _ _ _ _ _ A _ _ hFlat hFiniteType hSmooth
  let f := Spec.algebraMap R A
  have : Flat f := HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr hFlat)
  have : LocallyOfFiniteType f :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr hFiniteType)
  have : QuasiCompact f := inferInstance
  obtain ⟨L, _, _, _, _, _, hW, hSmoothAt⟩ := hScheme R (FractionRing R)
    ⟨inferInstance, by
      intro p _ L _ _ _ _ _
      exact hFiniteness R (R ⧸ p) L⟩ f
  let S := integralClosure R L
  obtain ⟨hDvrS, hCompleteS⟩ := isDiscreteValuationRing_and_isAdicComplete_of_finiteExtension R L
  have : IsAlgClosed (ResidueField S) :=
    IsAlgClosed.of_ringEquiv (ResidueField R) (ResidueField S) (residueEquiv_of_finiteExtension R L)
  have hFF : Module.FaithfullyFlat R S := DvrFiniteSeparableExtension.faithfullyFlat R L
  let D := S ⊗[R] A
  have : Algebra.Smooth (FractionRing S) (FractionRing S ⊗[S] D) :=
    smooth_genericFibre_baseChange (A := A) (FaithfulSMul.algebraMap_injective R S)
  have h := affineNormalization_finite_and_reduced_of_smooth_neighbourhoods S D
    (pullback.snd f (Spec.algebraMap R S)) (affineBaseChangeIso R S A)
    (affineBaseChangeIso_hom_comp R S A) hW (hSmoothAt (closedPoint S))
  exact ⟨S, inferInstance, inferInstance, hDvrS, inferInstance, hFF, h.1, h.2⟩

/-- The two named premises imply the unchanged affine reduced fibre proposition. -/
def DvrAffineReducedFibreConditionalStatement : Prop :=
  CompleteLocalNormalizationFinitenessStatement.{u} → SchemeReducedFibreStatement.{u, u} →
    DvrAffineReducedFibreStatement.{u}

/-- Compose the complete-base result with the arbitrary-DVR reduction. -/
theorem dvrAffineReducedFibreConditional : DvrAffineReducedFibreConditionalStatement.{u} := by
  intro hFiniteness hScheme
  exact dvrAffineReducedFibre_of_completeBase
    (completeBase_of_normalizationFiniteness_and_scheme hFiniteness hScheme)

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre

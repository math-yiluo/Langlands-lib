import Langlands.Representation.Plancherel.DynamicCommonLeviGalleryNormalization
import Langlands.Representation.Plancherel.DynamicRepresentedGalleryProduct

/-! # The scalar of the compact continued composite from the gallery -/

noncomputable section

universe u uV

set_option quotPrecheck false
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction Aubert.General.RepresentedParabolic
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicCommonLeviComposition DynamicCommonLeviContinuation
open DynamicCommonLeviCompact DynamicCommonLeviStructuralComparison
open ActualCommonLeviTensor UnramifiedOperatorFamily StandardIntertwining

private theorem comp_eq_smul_of_equiv
    {X Y V W : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (E : X ≃ₗ[ℂ] V) (F : Y ≃ₗ[ℂ] W)
    (J : X →ₗ[ℂ] Y) (L : Y →ₗ[ℂ] X) (J' : V →ₗ[ℂ] W) (L' : W →ₗ[ℂ] V)
    (a b c : ℂ) (hJ : ∀ x, F (J x) = a • J' (E x)) (hL : ∀ y, E (L y) = b • L' (F y))
    (hcomp : ∀ v, L' (J' v) = c • v) :
    L.comp J = ((b * a) * c) • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply E.injective
  change E (L (J x)) = E (((b * a) * c) • x)
  rw [hL, hJ, map_smul, hcomp, smul_smul, smul_smul, map_smul, mul_assoc]

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

local notation "d" => galleryVertexData hG ha
local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "B" => twistObject χ
local notation "σ" => fun z : X => SmoothRep.pullback (parameterHomeomorph χ) (B z A)
local notation "I" => fun x z => representedInduction hG (d x) (σ z)
local notation "C" => fun (x : GalleryVertex χ) => CompactInductionPicture
  (commonDecomposition χ x.val x.property) K A

set_option backward.isDefEq.respectTransparency.types false in
/-- Compare the actual compact picture with the represented induction at the same parameter. -/
def compactRepresentedGalleryEquiv (x : GalleryVertex χ)
    (hxK : ∀ g : rationalPoints G, ∃ q : parabolic x.val, ∃ k : K, g = (q : rationalPoints G) * k)
    (z : X) : C x ≃ₗ[ℂ] I x z :=
  (compactEquiv χ hG K hK x.val x.property hxK z A).symm.trans
    (representedDynamicInductionEquiv hG (d x) x.property (B z A)).symm.toLinearEquiv

variable (x y : GalleryVertex χ)
  (hxK : ∀ g : rationalPoints G, ∃ q : parabolic x.val, ∃ k : K, g = (q : rationalPoints G) * k)
  (hyK : ∀ g : rationalPoints G, ∃ q : parabolic y.val, ∃ k : K, g = (q : rationalPoints G) * k)
  (p : ContinuedPair χ hG K hK x.val x.property hxK y.val y.property hyK A)

local notation "E₀" => compactRepresentedGalleryEquiv hG ha K hK A x hxK
local notation "E₁" => compactRepresentedGalleryEquiv hG ha K hK A y hyK

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two transports commute with the original continued compact operator. -/
theorem representedContinuedPairOperator_compact_apply (z : p.regularRegion) (v : C x) :
    representedContinuedPairOperator hG ha K hK x y hxK hyK A p z (E₀ z.val v) =
      E₁ z.val (p.presentation.continuedOperator z v) := by
  let e₀ := representedDynamicInductionEquiv hG (d x) x.property (B z.val A)
  let e₁ := representedDynamicInductionEquiv hG (d y) y.property (B z.val A)
  let k₀ := compactEquiv χ hG K hK x.val x.property hxK z.val A
  let k₁ := compactEquiv χ hG K hK y.val y.property hyK z.val A
  let J := ContinuedPair.operator χ hG K hK x.val x.property hxK y.val y.property hyK A p z
  have hk := LinearMap.congr_fun
    (ContinuedPair.operator_compact χ hG K hK x.val x.property hxK y.val y.property hyK A p z) v
  change k₁ (J (k₀.symm v)) = p.presentation.continuedOperator z v at hk
  change e₁.symm (J (e₀ (e₀.symm (k₀.symm v)))) =
    e₁.symm (k₁.symm (p.presentation.continuedOperator z v))
  rw [e₀.apply_symm_apply, ← hk, LinearEquiv.symm_apply_apply]

variable (q : ContinuedPair χ hG K hK y.val y.property hyK x.val x.property hxK A)

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar of the original compact composite is the gallery scalar
times the product of the two positive Haar scales. -/
def continuedCompositeGalleryScale :
    {s : ℝ≥0 // 0 < s ∧ ∀ (z : ↥(p.regularRegion ∩ q.regularRegion)),
      representedIsPQRegular hG (d x) (d y) (σ z.val) →
      representedIsPQRegular hG (d y) (d x) (σ z.val) →
      ∀ c : ℂ, IsGalleryCompositeScalar hG ha K hK (σ z.val) x y c →
        p.presentation.continuedComposite q.presentation z = ((s : ℂ) * c) • LinearMap.id} := by
  let sF := continuedPairGalleryScale hG ha K hK x y hxK hyK A p
  let sR := continuedPairGalleryScale hG ha K hK y x hyK hxK A q
  refine ⟨sR.val * sF.val, mul_pos sR.property.1 sF.property.1, fun z hF hR c hz => ?_⟩
  let zF : p.regularRegion := ⟨z.val, z.property.1⟩
  let zR : q.regularRegion := ⟨z.val, z.property.2⟩
  let JF := galleryIntegralOperator hG ha K hK (σ z.val) x y
  let JR := galleryIntegralOperator hG ha K hK (σ z.val) y x
  have hForward (v : C x) : E₁ z.val (p.presentation.continuedOperator zF v) =
      (sF.val : ℂ) • JF (E₀ z.val v) :=
    (representedContinuedPairOperator_compact_apply hG ha K hK A x y hxK hyK p zF v).symm.trans
      (DFunLike.congr_fun (sF.property.2 zF hF) (E₀ z.val v))
  have hReverse (v : C y) : E₀ z.val (q.presentation.continuedOperator zR v) =
      (sR.val : ℂ) • JR (E₁ z.val v) :=
    (representedContinuedPairOperator_compact_apply hG ha K hK A y x hyK hxK q zR v).symm.trans
      (DFunLike.congr_fun (sR.property.2 zR hR) (E₁ z.val v))
  have he := comp_eq_smul_of_equiv (E₀ z.val) (E₁ z.val) (p.presentation.continuedOperator zF)
    (q.presentation.continuedOperator zR) JF.toLinearMap JR.toLinearMap (sF.val : ℂ) (sR.val : ℂ) c
    hForward hReverse (fun v => DFunLike.congr_fun hz v)
  simpa only [RationalOperatorContinuationData.continuedComposite, zF, zR,
    NNReal.coe_mul, Complex.ofReal_mul] using he

end Langlands.Plancherel.DynamicCommonLeviPresentations

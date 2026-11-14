import Langlands.BruhatTits.IntegralModels.IncidentRootReductiveQuotient
import Langlands.BruhatTits.IntegralModels.UnramifiedRootPositiveReductionStatement
import Langlands.GroupScheme.VectorScalarKernel
import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-! # Vanishing of negative root composites from positive reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- A root fixer at a point with negative displacement from `x` has strictly
positive depth at `x`. No facet incidence assumption is needed. -/
theorem rootFixer_le_filtrationPlus_of_displacement_neg
    {Ω : Set D.Apartment} {x y : D.Apartment} (hy : y ∈ Ω)
    (a : relativeRoots i) (ha : rootForm i a (y -ᵥ x) < 0) :
    D.rootFixer a Ω ≤ D.filtrationPlus x a 0 := by
  intro g hg
  have hgy := (D.mem_rootFixer.mp hg).2 y hy
  have hshift : D.filtration y a 0 =
      D.filtration x a (0 - rootForm i a (y -ᵥ x)) := by
    simpa only [vsub_vadd] using D.filtration_vadd x (y -ᵥ x) a 0
  rw [hshift] at hgy
  exact D.filtration_le_filtrationPlus x a (by linarith) hgy

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R]
  [IsAlgClosed (IsLocalRing.ResidueField R)]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  {Q : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
  [IsAffineHom Q.X.hom]

/-- For a smooth model over a Henselian ring with algebraically closed
residue field, a residue homomorphism killing reductions of every integral
section is the zero morphism on all schemes, including infinitesimal tests. -/
theorem specialFibreHom_eq_zero_of_reduction
    (hM : M.IsSmooth) (j : M.specialFibre ⟶ Q)
    (h : ∀ s : M.integralSections, rationalPoints.map j (M.reduction s) = 1) :
    j = 0 := by
  let : Smooth M.group.X.hom := hM
  let : Smooth M.specialFibre.X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  let : IsReduced M.specialFibre.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      (IsLocalRing.ResidueField R) _ M.specialFibre.X.hom
  apply Grp.hom_ext
  apply hom_ext_rationalPoints
  intro z
  change z ≫ j.hom.hom = z ≫ (1 : M.specialFibre.X ⟶ Q.X)
  rw [MonObj.comp_one]
  obtain ⟨s, hs⟩ := M.reduction_surjective hM z
  simpa only [hs, rationalPoints.map_apply] using h s

end Langlands.GroupScheme.IntegralModel

namespace Langlands.GroupScheme

/-- Equality transport of the Library's full zero-kernel isomorphism. -/
def kernelIsoOfEqZero {S : Scheme.{u}} {A B : GroupScheme S}
    (q : A ⟶ B) (hq : q = 0) : kernel q ≅ A := by
  subst q
  exact zeroKernelIso A B

/-- A zero homomorphism with smooth source has smooth full kernel. -/
theorem smooth_kernel_of_eq_zero {S : Scheme.{u}} {A B : GroupScheme S}
    [Smooth A.X.hom] (q : A ⟶ B) (hq : q = 0) :
    Smooth (kernel q).X.hom := by
  let e := (Grp.forget (Over S)).mapIso (kernelIsoOfEqZero q hq)
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  let : Smooth ((Grp.forget (Over S)).obj A).hom := ‹Smooth A.X.hom›
  change Smooth ((Grp.forget (Over S)).obj (kernel q)).hom
  rw [← e.hom.w]
  infer_instance

/-- A zero homomorphism has zero differential on every test algebra. -/
theorem Lie.targetMapLinear_eq_zero_of_eq_zero
    {R : CommRingCat.{u}} {A B : GroupScheme (Spec R)}
    [IsAffineHom A.X.hom] [IsAffineHom B.X.hom]
    (q : A ⟶ B) (hq : q = 0)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    Lie.targetMapLinear q R' = 0 := by
  subst q
  apply DFunLike.ext
  intro X
  apply Additive.toMul.injective
  apply Subtype.ext
  exact MonObj.comp_one _

end Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    {source target :
      RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G}
    (φ : RelativeComponentModelHom source target)
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (T : IntegralTorusData source C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData target) (hQ : Q.IsReductiveQuotient)
    (Ω Ω' : Set C.Apartment)
    (hsource : source.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (htarget : target.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (hP : UnramifiedRootPositiveReductionStatement.{u})

private instance sourceNeutral_smooth : Smooth source.neutral.group.X.hom :=
  source.neutral_smooth

private instance targetNeutral_smooth : Smooth target.neutral.group.X.hom :=
  target.neutral_smooth

private instance negativeRootSpecialFibre_affine (a : relativeRoots C.i) :
    IsAffineHom ((T.toIntegralSplitTorusData hT).rootModel a a.2.1).specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd
    ((T.toIntegralSplitTorusData hT).rootModel a a.2.1).group.X.hom
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  infer_instance

private instance negativeRootSpecialFibre_smooth (a : relativeRoots C.i) :
    Smooth ((T.toIntegralSplitTorusData hT).rootModel a a.2.1).specialFibre.X.hom := by
  let A := T.toIntegralSplitTorusData hT
  let : Smooth (A.rootModel a a.2.1).group.X.hom :=
    IntegralModel.SplitRoot.model_isSmooth source.neutral A.isSplit A.inclusion
      (A.integralCharacter a) (A.integralCharacter_ne_zero a.2.1)
  change Smooth (CategoryTheory.Limits.pullback.snd
    (A.rootModel a a.2.1).group.X.hom (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  infer_instance

private instance negativeRootSpecialFibre_connected (a : relativeRoots C.i) :
    ConnectedSpace
      ((T.toIntegralSplitTorusData hT).rootModel a a.2.1).specialFibre.X.left := by
  let A := T.toIntegralSplitTorusData hT
  exact (A.rootModel a a.2.1).hasConnectedSpecialFibre_of_geometricallyConnected
    ((A.rootModel a a.2.1).hasGeometricallyConnectedSpecialFibre_of_geometricallyConnected
      (IntegralModel.SplitRoot.model_hasGeometricallyConnectedFibres
        source.neutral A.isSplit A.inclusion
        (A.integralCharacter a) (A.integralCharacter_ne_zero a.2.1)))

include hQ hsource htarget hb hP

/-- Positive reduction implies that every strictly negative source-root
composite into the target reductive quotient is the zero scheme morphism. -/
theorem rootTargetReductiveQuotientMap_eq_zero_of_eval_neg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : RealTorusSpace.eval C.S a v < 0) :
    φ.rootTargetReductiveQuotientMap T hT Q a a.2.1 = 0 := by
  let A := T.toIntegralSplitTorusData hT
  let B := (φ.mapIntegralTorus T).toIntegralSplitTorusData hT
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (residueToFixedField F).toAlgebra
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  have hroot : (A.rootModel a a.2.1).integralPoints.map
      (rationalPoints.map (A.rootInclusion a a.2.1)) =
        C.apartment.rootFixer a Ω' := by
    rw [A.rootModel_integralPoints_eq, inf_comm, hsource,
      rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer C E Ω' a]
  have hpos : C.apartment.rootFixer a Ω' ≤ C.apartment.filtrationPlus x a 0 :=
    C.apartment.rootFixer_le_filtrationPlus_of_displacement_neg hv a
      (by simpa only [vadd_vsub, rootForm_mk] using ha)
  apply (A.rootModel a a.2.1).specialFibreHom_eq_zero_of_reduction
    (IntegralModel.SplitRoot.model_isSmooth source.neutral A.isSplit A.inclusion
      (A.integralCharacter a) (A.integralCharacter_ne_zero a.2.1))
  intro u
  let u' := rationalPoints.map (φ.integralRootMap T hT a a.2.1) u
  have hsection :
      rationalPoints.map (B.rootModelMap a a.2.1).hom u' =
        rationalPoints.map φ.neutral.hom
          (rationalPoints.map (A.rootModelMap a a.2.1).hom u) := by
    change u ≫ (φ.integralRootMap T hT a a.2.1).hom.hom ≫
        (B.rootModelMap a a.2.1).hom.hom.hom =
      u ≫ (A.rootModelMap a a.2.1).hom.hom.hom ≫ φ.neutral.hom.hom.hom
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f => u ≫ f.hom.hom) (φ.integralRootMap_comp T hT a a.2.1)
  have hgeneric :
      rationalPoints.map (B.rootInclusion a a.2.1)
          ((B.rootModel a a.2.1).integralPointMap u') =
        rationalPoints.map (A.rootInclusion a a.2.1)
          ((A.rootModel a a.2.1).integralPointMap u) := by
    calc
      _ = target.neutral.integralPointMap
          (rationalPoints.map (B.rootModelMap a a.2.1).hom u') :=
        ((B.rootModelMap a a.2.1).integralPointMap_naturality u').symm
      _ = target.neutral.integralPointMap
          (rationalPoints.map φ.neutral.hom
            (rationalPoints.map (A.rootModelMap a a.2.1).hom u)) :=
        congrArg target.neutral.integralPointMap hsection
      _ = source.neutral.integralPointMap
          (rationalPoints.map (A.rootModelMap a a.2.1).hom u) :=
        φ.neutral_integralPointMap _
      _ = _ := (A.rootModelMap a a.2.1).integralPointMap_naturality u
  have hrad : target.neutral.reduction
      (rationalPoints.map (B.rootModelMap a a.2.1).hom u') ∈ Q.radicalPoints := by
    apply (hP F G C E Ω ⟨x, hx⟩ hb target htarget B Q hQ a u').mpr
    refine ⟨x, hx, ?_⟩
    rw [hgeneric]
    exact hpos (hroot.le (Subgroup.mem_map.mpr
      ⟨(A.rootModel a a.2.1).integralPointMap u, ⟨u, rfl⟩, rfl⟩))
  have hkill : rationalPoints.map Q.projection
      (target.neutral.reduction
        (rationalPoints.map (B.rootModelMap a a.2.1).hom u')) = 1 := by
    apply (mem_range_kernelι_iff Q.projection _).mp
    exact (SubgroupFunctor.le_def.mp hQ.2.1.2.2.2.ge) _ hrad
  rw [hsection, φ.neutral.reduction_naturality,
    (A.rootModelMap a a.2.1).reduction_naturality] at hkill
  simpa only [rootTargetReductiveQuotientMap, rationalPoints.map_apply,
    Grp.comp_hom_hom, Category.assoc] using hkill

/-- The full negative root-composite kernel is the original smooth root
special fibre, conditional only on the positive-reduction theorem above. -/
def rootTargetReductiveQuotientKernelIsoOfEvalNeg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : RealTorusSpace.eval C.S a v < 0) :
    kernel (φ.rootTargetReductiveQuotientMap T hT Q a a.2.1) ≅
      ((T.toIntegralSplitTorusData hT).rootModel a a.2.1).specialFibre :=
  kernelIsoOfEqZero (φ.rootTargetReductiveQuotientMap T hT Q a a.2.1)
    (φ.rootTargetReductiveQuotientMap_eq_zero_of_eval_neg C E T hT Q hQ
      Ω Ω' hsource htarget hb hP x hx v hv a ha)

/-- The full kernel in the negative branch is smooth. -/
theorem rootTargetReductiveQuotientMap_smooth_kernel_of_eval_neg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : RealTorusSpace.eval C.S a v < 0) :
    Smooth (kernel (φ.rootTargetReductiveQuotientMap T hT Q a a.2.1)).X.hom :=
  smooth_kernel_of_eq_zero _
    (φ.rootTargetReductiveQuotientMap_eq_zero_of_eval_neg C E T hT Q hQ
      Ω Ω' hsource htarget hb hP x hx v hv a ha)

/-- The negative root differential has zero range. -/
theorem rootTargetReductiveQuotientMap_lie_range_of_eval_neg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : RealTorusSpace.eval C.S a v < 0) :
    LinearMap.range (Lie.targetMapLinear
      (φ.rootTargetReductiveQuotientMap T hT Q a a.2.1)
      (IsLocalRing.ResidueField (fixedFieldIntegers F))) = ⊥ := by
  exact (congrArg LinearMap.range
    (Lie.targetMapLinear_eq_zero_of_eq_zero _
      (φ.rootTargetReductiveQuotientMap_eq_zero_of_eval_neg C E T hT Q hQ
        Ω Ω' hsource htarget hb hP x hx v hv a ha)
      (IsLocalRing.ResidueField (fixedFieldIntegers F)))).trans LinearMap.range_zero

/-- The inclusion of the actual negative-root schematic image has zero Lie range. -/
theorem rootTargetReductiveQuotientImage_lie_range_of_eval_neg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : RealTorusSpace.eval C.S a v < 0) :
    LinearMap.range (Lie.targetMapLinear
      (SchematicImage.inclusion (φ.rootTargetReductiveQuotientMap T hT Q a a.2.1))
      (IsLocalRing.ResidueField (fixedFieldIntegers F))) = ⊥ := by
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  exact (Lie.range_schematicImage_inclusion_of_smooth_kernel _
    (φ.rootTargetReductiveQuotientMap_smooth_kernel_of_eval_neg C E T hT Q hQ
      Ω Ω' hsource htarget hb hP x hx v hv a ha)
    (IsLocalRing.ResidueField (fixedFieldIntegers F))).trans
      (φ.rootTargetReductiveQuotientMap_lie_range_of_eval_neg C E T hT Q hQ
        Ω Ω' hsource htarget hb hP x hx v hv a ha)

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

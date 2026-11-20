import Langlands.Representation.Plancherel.DynamicRankOneWallGeometry
import Langlands.Representation.Plancherel.DynamicRepresentedGalleryProduct
import Langlands.Representation.Intertwining.LeviExtensionIntertwining
import Langlands.Representation.Intertwining.PQIntegralIntertwiningTwist

/-! # Ambient character invariance of the rank-one gallery scalar -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviComposition

open Aubert.General.RepresentedParabolic DynamicCommonLeviPresentations
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicCommonLeviStructuralComparison

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
  equalitySubgroupMeasurable equalitySubgroupBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

local notation "d" => galleryVertexData hG ha

/-- The represented opposite at a gallery vertex with its original complement. -/
def galleryOppositeModel (x : GalleryVertex χ) :
    OppositeLeviParabolicData (d x).p (d x).l where
  parabolic := (d x.opposite).P
  radical := (d x.opposite).U
  inclusion := (d x.opposite).p
  levi := (d x.opposite).l
  unipotent := (d x.opposite).n
  isParabolic := (d x.opposite).r.isCompatible.parabolic
  isLevi := (d x.opposite).r.isCompatible.levi
  isRadical := (d x.opposite).radical
  multiplication := multiplication_isIso hG (d x.opposite)
  levi_comp := (d x.opposite).levi_comp.trans (d x).levi_comp.symm
  intersection := pointImage_inter_dynamicOpposite (d x) (d x.opposite) x.property

namespace DynamicRankOneWall

variable {x y : GalleryVertex χ} (W : DynamicRankOneWall χ x.val y.val)

local instance intermediateAffine : IsAffineHom W.wall.M.X.hom :=
  W.wall.levi.isConnectedReductive.isAffineHom

local instance intermediateTopology : TopologicalSpace (rationalPoints W.wall.M) :=
  leviPointTopology W.wall.m W.wall.levi

local instance intermediateLocallyCompact : LocallyCompactSpace (rationalPoints W.wall.M) :=
  leviPoints_locallyCompactSpace W.wall.p W.wall.m W.wall.parabolic W.wall.levi

local instance intermediateNonarchimedean : NonarchimedeanGroup (rationalPoints W.wall.M) :=
  leviPoints_nonarchimedeanGroup W.wall.p W.wall.m W.wall.parabolic W.wall.levi

local notation "outer" => W.outerRadical
local notation "rad₁" => W.innerRadical
local notation "rad₂" => W.innerRadical'
set_option quotPrecheck false in
local notation "lower₁" => leviInductionFunctor W.wall.q W.wall.l (rad₁).inclusion
  W.wall.innerParabolic (rad₁).isRadical W.wall.innerLevi (rad₁).multiplication
set_option quotPrecheck false in
local notation "lower₂" => leviInductionFunctor W.wall.q' W.wall.l' (rad₂).inclusion
  W.wall.innerParabolic' (rad₂).isRadical W.wall.innerLevi' (rad₂).multiplication
set_option quotPrecheck false in
local notation "V₁" => (pointImage ((rad₁).inclusion ≫ W.wall.q) ⊓ pointImage ((rad₁).inclusion ≫ W.wall.q) :
  Subgroup (rationalPoints W.wall.M))
set_option quotPrecheck false in
local notation "V₂" => (pointImage ((rad₂).inclusion ≫ W.wall.q') ⊓ pointImage ((rad₂).inclusion ≫ W.wall.q') :
  Subgroup (rationalPoints W.wall.M))
local notation "PQ" => fun x y σ => representedIsPQRegular hG (d x) (d y) σ
local notation "Jupper" => galleryIntegralOperator hG ha K hK
local notation "HaarUpper" => galleryPairHaar hG ha K hK
local notation "ScalarUpper" => IsGalleryCompositeScalar hG ha K hK

private theorem scalar_iff_of_restriction {H X Y Z : Type*} [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ H X) (T : X →ₗ[ℂ] Y) (hT : Function.Surjective T)
    (evalG : X → Z) (evalL : Y → Z) (hEval : ∀ f, evalL (T f) = evalG f)
    (hSep : ∀ f g, (∀ x, evalG (ρ x f) = evalG (ρ x g)) → f = g)
    (J : ρ.IntertwiningMap ρ) (J' : Y →ₗ[ℂ] Y) (h : ∀ f, T (J f) = J' (T f)) (c : ℂ) :
    (∀ f, J f = c • f) ↔ (∀ f, J' f = c • f) := by
  constructor
  · intro hf g
    obtain ⟨f, rfl⟩ := hT g
    exact (h f).symm.trans ((congrArg T (hf f)).trans (map_smul T c f))
  · intro hg f
    apply hSep
    intro x
    have horbit : T (J (ρ x f)) = T (c • ρ x f) :=
      (h _).trans ((hg _).trans (map_smul T c (ρ x f)).symm)
    have h₁ := Representation.IntertwiningMap.isIntertwining _ _ J x f
    have h₂ := map_smul (ρ x) c f
    exact (congrArg evalG h₁).symm.trans ((hEval _).symm.trans
      ((congrArg evalL horbit).trans ((hEval _).trans (congrArg evalG h₂.symm))))

private theorem scalar_conjugation {X Y X' Y' : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
    (E : X ≃ₗ[ℂ] X') (E' : Y ≃ₗ[ℂ] Y') (J : X →ₗ[ℂ] Y) (J' : Y →ₗ[ℂ] X)
    (c : ℂ) (h : ∀ x, J' (J x) = c • x) (x : X') :
    E (J' (E'.symm (E' (J (E.symm x))))) = c • x := by
  rw [E'.symm_apply_apply, h, map_smul, E.apply_symm_apply]

include ha in
set_option maxHeartbeats 7000000 in
private theorem integralComposite_scalar_iff
    (d₁ : ParabolicData χ x.val T a) (d₂ : ParabolicData χ y.val T a)
    (b₁ : ParabolicData χ (Dynamic.inverseCocharacter x.val) T a)
    (b₂ : ParabolicData χ (Dynamic.inverseCocharacter y.val) T a)
    (τ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
    (hF : representedIsPQRegular hG d₁ d₂ τ) (hR : representedIsPQRegular hG d₂ d₁ τ)
    (eF : (V₂ : Type u) ≃ₜ* representedComplement b₁ d₂)
    (eR : (V₁ : Type u) ≃ₜ* representedComplement b₂ d₁)
    (heF : ∀ x, (eF x : rationalPoints G) = rationalPoints.map (W.wall.m ≫ W.wall.p) x.val)
    (heR : ∀ x, (eR x : rationalPoints G) = rationalPoints.map (W.wall.m ≫ W.wall.p) x.val)
    (measureF : Measure (V₂)) (measureR : Measure (V₁))
    (upperF : Measure (representedComplement b₁ d₂)) (upperR : Measure (representedComplement b₂ d₁))
    (heqF : upperF = measureF.map eF) (heqR : upperR = measureR.map eR)
    (J₁ : (representedInduction hG d₁ τ).representation.IntertwiningMap
      (representedInduction hG d₂ τ).representation)
    (J₂ : (representedInduction hG d₂ τ).representation.IntertwiningMap
      (representedInduction hG d₁ τ).representation)
    (L₁ : ((lower₁).obj τ).representation.IntertwiningMap ((lower₂).obj τ).representation)
    (L₂ : ((lower₂).obj τ).representation.IntertwiningMap ((lower₁).obj τ).representation)
    (hJ₁ : representedIsIntegralIntertwiner hG d₁ d₂ b₁ upperF τ J₁)
    (hJ₂ : representedIsIntegralIntertwiner hG d₂ d₁ b₂ upperR τ J₂)
    (hL₁ : IsIntegralIntertwiner W.wall.q W.wall.l (rad₁).inclusion
      W.wall.innerParabolic (rad₁).isRadical W.wall.innerLevi (rad₁).multiplication
      W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic' (rad₂).isRadical W.wall.innerLevi'
      (rad₂).multiplication (V₂) measureF τ L₁)
    (hL₂ : IsIntegralIntertwiner W.wall.q' W.wall.l' (rad₂).inclusion
      W.wall.innerParabolic' (rad₂).isRadical W.wall.innerLevi' (rad₂).multiplication
      W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic (rad₁).isRadical W.wall.innerLevi
      (rad₁).multiplication (V₁) measureR τ L₂) (c : ℂ) :
    (∀ f, J₂ (J₁ f) = c • f) ↔ (∀ f, L₂ (L₁ f) = c • f) := by
  let D₁ := W.extension hG d₁
  let D₂ := W.extension' hG d₂
  have hP₁ : pointImage d₁.p ≤ pointImage W.wall.p := D₁.pointImage_le
  have hP₂ : pointImage d₂.p ≤ pointImage W.wall.p := D₂.pointImage_le
  have hM₁ : W.wall.l ≫ W.wall.q ≫ W.wall.m ≫ W.wall.p = d₁.l ≫ d₁.p := D₁.levi_comp.symm
  have hM₂ : W.wall.l' ≫ W.wall.q' ≫ W.wall.m ≫ W.wall.p = d₂.l ≫ d₂.p := D₂.levi_comp.symm
  have hI₁ : pointImage (W.wall.q ≫ W.wall.m ≫ W.wall.p) =
      pointImage d₁.p ⊓ pointImage (W.wall.m ≫ W.wall.p) :=
    D₁.pointImage_inf.trans (inf_comm _ _)
  have hI₂ : pointImage (W.wall.q' ≫ W.wall.m ≫ W.wall.p) =
      pointImage d₂.p ⊓ pointImage (W.wall.m ≫ W.wall.p) :=
    D₂.pointImage_inf.trans (inf_comm _ _)
  let restrict₁ := innerStageRestriction hG d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi
    d₁.radical (multiplication_isIso hG d₁)
    W.wall.p W.wall.m (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication hP₁
    W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic
    W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication hM₁ hI₁ τ
  let stage₁ := leviInductionStagesIso d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi
    d₁.radical (multiplication_isIso hG d₁)
    W.wall.p W.wall.m (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication
    W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic
    W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication hP₁ hM₁ (hI₁.trans (inf_comm _ _)) hG
  let restrict₂ := innerStageRestriction hG d₂.p d₂.l d₂.n d₂.r.isCompatible.parabolic d₂.r.isCompatible.levi
    d₂.radical (multiplication_isIso hG d₂)
    W.wall.p W.wall.m (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication hP₂
    W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic'
    W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication hM₂ hI₂ τ
  let stage₂ := leviInductionStagesIso d₂.p d₂.l d₂.n d₂.r.isCompatible.parabolic d₂.r.isCompatible.levi
    d₂.radical (multiplication_isIso hG d₂)
    W.wall.p W.wall.m (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication
    W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic'
    W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication hP₂ hM₂ (hI₂.trans (inf_comm _ _)) hG
  have commuteF (f : representedInduction hG d₁ τ) :
      restrict₂ (J₁ f) = L₁ (restrict₁ f) := by
    have hStage := leviInductionStagesIso_eval' d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi
      d₁.radical (multiplication_isIso hG d₁)
      W.wall.p W.wall.m (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication
      W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic
      W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication hP₁ hM₁ (hI₁.trans (inf_comm _ _)) hG τ f
    apply Subtype.ext
    apply Subtype.ext
    funext z
    have h := innerLevi_integralIntertwiner_formula hG
      d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi
      d₁.radical (multiplication_isIso hG d₁) d₂.p d₂.l d₂.n d₂.r.isCompatible.parabolic d₂.r.isCompatible.levi
      d₂.radical (multiplication_isIso hG d₂)
      W.wall.p W.wall.m (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication hP₁ hP₂
      W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic
      W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic'
      W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication
      hM₁ hM₂ hI₁ hI₂ a ha (representedComplement b₁ d₂) (V₂) inf_le_right eF heF
      measureF upperF heqF τ hF J₁ L₁ hJ₁ hL₁ f (SmoothRep.hom (stage₁.hom.app τ) f) hStage 1 z
    let c := innerLeviHalfModulus W.wall.p W.wall.m (outer).inclusion W.wall.parabolic
      W.wall.levi (outer).isRadical (outer).multiplication
    have hTarget := innerStageRestriction_eval hG d₂.p d₂.l d₂.n d₂.r.isCompatible.parabolic d₂.r.isCompatible.levi
      d₂.radical (multiplication_isIso hG d₂)
      W.wall.p W.wall.m (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication hP₂
      W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic'
      W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication hM₂ hI₂ τ (J₁ f) z
    have hmul := congrArg (fun t : rationalPoints G => ((c z : ℂˣ) : ℂ)⁻¹ •
      Induction.eval _ _ (J₁ f) t) (mul_one (rationalPoints.map (W.wall.m ≫ W.wall.p) z))
    exact hTarget.trans (h.trans hmul).symm
  have commuteR (f : representedInduction hG d₂ τ) :
      restrict₁ (J₂ f) = L₂ (restrict₂ f) := by
    have hStage := leviInductionStagesIso_eval' d₂.p d₂.l d₂.n d₂.r.isCompatible.parabolic d₂.r.isCompatible.levi
      d₂.radical (multiplication_isIso hG d₂)
      W.wall.p W.wall.m (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication
      W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic'
      W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication hP₂ hM₂ (hI₂.trans (inf_comm _ _)) hG τ f
    apply Subtype.ext
    apply Subtype.ext
    funext z
    have h := innerLevi_integralIntertwiner_formula hG
      d₂.p d₂.l d₂.n d₂.r.isCompatible.parabolic d₂.r.isCompatible.levi
      d₂.radical (multiplication_isIso hG d₂) d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi
      d₁.radical (multiplication_isIso hG d₁)
      W.wall.p W.wall.m (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication hP₂ hP₁
      W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic'
      W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic
      W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication
      hM₂ hM₁ hI₂ hI₁ a ha (representedComplement b₂ d₁) (V₁) inf_le_right eR heR
      measureR upperR heqR τ hR J₂ L₂ hJ₂ hL₂ f (SmoothRep.hom (stage₂.hom.app τ) f) hStage 1 z
    let c := innerLeviHalfModulus W.wall.p W.wall.m (outer).inclusion W.wall.parabolic
      W.wall.levi (outer).isRadical (outer).multiplication
    have hTarget := innerStageRestriction_eval hG d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi
      d₁.radical (multiplication_isIso hG d₁)
      W.wall.p W.wall.m (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication hP₁
      W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic
      W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication hM₁ hI₁ τ (J₂ f) z
    have hmul := congrArg (fun t : rationalPoints G => ((c z : ℂˣ) : ℂ)⁻¹ •
      Induction.eval _ _ (J₂ f) t) (mul_one (rationalPoints.map (W.wall.m ≫ W.wall.p) z))
    exact hTarget.trans (h.trans hmul).symm
  have hSurj := innerStageRestriction_surjective hG d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi
    d₁.radical (multiplication_isIso hG d₁)
    W.wall.p W.wall.m (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication hP₁
    W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic
    W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication hM₁ hI₁ τ
  let evG := fun f : representedInduction hG d₁ τ => Induction.eval _ _ f (1 : rationalPoints G)
  let evL := fun f : (lower₁).obj τ => Induction.eval _ _ f (1 : rationalPoints W.wall.M)
  have hEval (f : representedInduction hG d₁ τ) : evL (restrict₁ f) = evG f := by
    have h := innerStageRestriction_eval hG d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi
      d₁.radical (multiplication_isIso hG d₁)
      W.wall.p W.wall.m (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication hP₁
      W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic
      W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication hM₁ hI₁ τ f 1
    let c := innerLeviHalfModulus W.wall.p W.wall.m (outer).inclusion W.wall.parabolic
      W.wall.levi (outer).isRadical (outer).multiplication
    have hc₁ : ((c 1 : ℂˣ) : ℂ)⁻¹ = 1 := by rw [map_one, Units.val_one, inv_one]
    have ht := congrArg₂ (fun (s : ℂ) (t : rationalPoints G) => s • Induction.eval _ _ f t)
      hc₁ (map_one (rationalPoints.map (W.wall.m ≫ W.wall.p)))
    exact h.trans (ht.trans (one_smul ℂ _))
  let ρ := (representedInduction hG d₁ τ).representation
  have hSep (f g : representedInduction hG d₁ τ)
      (h : ∀ x, evG (ρ x f) = evG (ρ x g)) : f = g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have hx := h x
    change Induction.eval _ _ f (1 * x) = Induction.eval _ _ g (1 * x) at hx
    rw [one_mul] at hx
    exact hx
  exact scalar_iff_of_restriction ρ restrict₁ hSurj evG evL hEval hSep (J₂.comp J₁)
    (L₂.toLinearMap.comp L₁.toLinearMap)
    (fun f => (commuteR (J₁ f)).trans (congrArg (fun g => L₂ g) (commuteF f))) c

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 7000000 in
/-- At a rank-one gallery edge the prescribed integral-normalized composite
keeps its scalar under any ambient character trivial on both inner radicals.
The two parameters must be regular for the two upper ordered pairs. -/
theorem galleryScalar_of_ambientTwist
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
    (eta : Induction.SmoothCharacter ℂ (rationalPoints W.wall.M))
    (nu : Induction.SmoothCharacter ℂ (rationalPoints (parameterScheme χ)))
    (hnu : ∀ m, nu.toMonoidHom m = eta.toMonoidHom (rationalPoints.map (W.wall.l ≫ W.wall.q) m))
    (h₁ : pointImage ((rad₁).inclusion ≫ W.wall.q) ≤ eta.toMonoidHom.ker)
    (h₂ : pointImage ((rad₂).inclusion ≫ W.wall.q') ≤ eta.toMonoidHom.ker)
    (hPQ : PQ x y σ) (hQP : PQ y x σ)
    (hPQ' : PQ x y (σ.twist nu.toMonoidHom nu.isOpen_ker))
    (hQP' : PQ y x (σ.twist nu.toMonoidHom nu.isOpen_ker))
    (c : ℂ) (hc : ScalarUpper σ x y c) :
    ScalarUpper (σ.twist nu.toMonoidHom nu.isOpen_ker) x y c := by
  let D₁ := W.extension hG (d x)
  let D₂ := W.extension' hG (d y)
  have hOpp' : pointImage W.wall.q' ⊓ pointImage W.wall.q = pointImage (W.wall.l' ≫ W.wall.q') := by
    rw [inf_comm, W.wall.commonLevi]
    exact W.pointImage_inner_inf
  obtain ⟨eF, heF⟩ := LeviParabolicExtensionDatum.exists_innerComplementEquiv hG
    (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication
    (rad₁).inclusion W.wall.innerParabolic W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication D₁
    (rad₂).inclusion W.wall.innerParabolic' W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication D₂
    (galleryOppositeModel hG ha x) W.wall.commonLevi W.pointImage_inner_inf
  obtain ⟨eR, heR⟩ := LeviParabolicExtensionDatum.exists_innerComplementEquiv hG
    (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication
    (rad₂).inclusion W.wall.innerParabolic' W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication D₂
    (rad₁).inclusion W.wall.innerParabolic W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication D₁
    (galleryOppositeModel hG ha y) W.wall.commonLevi.symm hOpp'
  change (V₂ : Type u) ≃ₜ* representedComplement (d x.opposite) (d y) at eF
  change (V₁ : Type u) ≃ₜ* representedComplement (d y.opposite) (d x) at eR
  let measureF : Measure (V₂) := (HaarUpper x y).map eF.symm
  let measureR : Measure (V₁) := (HaarUpper y x).map eR.symm
  have : measureF.IsHaarMeasure :=
    (map_isHaarMeasure_integral_eq (V₂) eF.symm (HaarUpper x y)).1
  have : measureR.IsHaarMeasure :=
    (map_isHaarMeasure_integral_eq (V₁) eR.symm (HaarUpper y x)).1
  have heqF : HaarUpper x y = measureF.map eF :=
    (MeasurableEquiv.map_map_symm eF.toHomeomorph.toMeasurableEquiv).symm
  have heqR : HaarUpper y x = measureR.map eR :=
    (MeasurableEquiv.map_map_symm eR.toHomeomorph.toMeasurableEquiv).symm
  have hPQF := LeviParabolicExtensionDatum.lower_isPQRegular hG
    (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication
    (rad₁).inclusion W.wall.innerParabolic W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication D₁
    (rad₂).inclusion W.wall.innerParabolic' W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication D₂ a σ hPQ
  have hPQR := LeviParabolicExtensionDatum.lower_isPQRegular hG
    (outer).inclusion W.wall.parabolic W.wall.levi (outer).isRadical (outer).multiplication
    (rad₂).inclusion W.wall.innerParabolic' W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication D₂
    (rad₁).inclusion W.wall.innerParabolic W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication D₁ a σ hQP
  have hF := (pqIntegralIntertwiningOperator.{u, uV} F W.wall.M W.wall.levi.isConnectedReductive
    W.wall.Q (parameterScheme χ) (rad₁).group W.wall.Q' (rad₂).group W.wall.Q' (rad₂).group
    W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication
    W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic' W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication
    W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic' W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication
    W.wall.commonLevi.symm W.wall.commonLevi W.pointImage_inner_inf measureF).2 T a ha σ hPQF
  have hR := (pqIntegralIntertwiningOperator.{u, uV} F W.wall.M W.wall.levi.isConnectedReductive
    W.wall.Q' (parameterScheme χ) (rad₂).group W.wall.Q (rad₁).group W.wall.Q (rad₁).group
    W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic' W.wall.innerLevi' (rad₂).isRadical (rad₂).multiplication
    W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication
    W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic W.wall.innerLevi (rad₁).isRadical (rad₁).multiplication
    W.wall.commonLevi W.wall.commonLevi.symm hOpp' measureR).2 T a ha σ hPQR
  obtain ⟨JF, hJF, _⟩ := hF
  obtain ⟨JR, hJR, _⟩ := hR
  let normF := IsIntegralIntertwiner.{u, uV}
    W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic (rad₁).isRadical W.wall.innerLevi (rad₁).multiplication
    W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic' (rad₂).isRadical W.wall.innerLevi' (rad₂).multiplication
    (V₂) measureF
  let normR := IsIntegralIntertwiner.{u, uV}
    W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic' (rad₂).isRadical W.wall.innerLevi' (rad₂).multiplication
    W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic (rad₁).isRadical W.wall.innerLevi (rad₁).multiplication
    (V₁) measureR
  have compare (τ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
      (hF : PQ x y τ) (hR : PQ y x τ)
      (L₁ : ((lower₁).obj τ).representation.IntertwiningMap ((lower₂).obj τ).representation)
      (L₂ : ((lower₂).obj τ).representation.IntertwiningMap ((lower₁).obj τ).representation)
      (hL₁ : normF τ L₁) (hL₂ : normR τ L₂) :
      ScalarUpper τ x y c ↔ ∀ f, L₂ (L₁ f) = c • f := by
    have hT := integralComposite_scalar_iff hG ha W (d x) (d y) (d x.opposite) (d y.opposite)
      τ hF hR eF eR heF heR measureF measureR (HaarUpper x y) (HaarUpper y x) heqF heqR
      (Jupper τ x y) (Jupper τ y x) L₁ L₂
      (galleryIntegralOperator_spec hG ha K hK τ x y hF)
      (galleryIntegralOperator_spec hG ha K hK τ y x hR) hL₁ hL₂ c
    constructor
    · intro h
      exact hT.mp (fun f => DFunLike.congr_fun h f)
    · intro h
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      exact hT.mpr h
  have hScalar := (compare σ hPQ hQP JF JR hJF hJR).mp hc
  have hnu' : ∀ m, nu.toMonoidHom m = eta.toMonoidHom (rationalPoints.map (W.wall.l' ≫ W.wall.q') m) := by
    intro m
    rw [W.wall.commonLevi]
    exact hnu m
  obtain ⟨E₁, hE₁⟩ := leviInductionCharacterMultiplication W.wall.q W.wall.l (rad₁).inclusion
    W.wall.innerParabolic (rad₁).isRadical W.wall.innerLevi (rad₁).multiplication eta nu σ h₁ hnu
  obtain ⟨E₂, hE₂⟩ := leviInductionCharacterMultiplication W.wall.q' W.wall.l' (rad₂).inclusion
    W.wall.innerParabolic' (rad₂).isRadical W.wall.innerLevi' (rad₂).multiplication eta nu σ h₂ hnu'
  have hTF := isIntegralIntertwiner_twist W.wall.q W.wall.l (rad₁).inclusion
    W.wall.innerParabolic (rad₁).isRadical W.wall.innerLevi (rad₁).multiplication eta nu σ
    W.wall.q' W.wall.l' (rad₂).inclusion W.wall.innerParabolic' (rad₂).isRadical W.wall.innerLevi'
    (rad₂).multiplication measureF JF hJF (inf_le_right.trans h₂) E₁ E₂ hE₁ hE₂
  have hTR := isIntegralIntertwiner_twist W.wall.q' W.wall.l' (rad₂).inclusion
    W.wall.innerParabolic' (rad₂).isRadical W.wall.innerLevi' (rad₂).multiplication eta nu σ
    W.wall.q W.wall.l (rad₁).inclusion W.wall.innerParabolic (rad₁).isRadical W.wall.innerLevi
    (rad₁).multiplication measureR JR hJR (inf_le_right.trans h₁) E₂ E₁ hE₂ hE₁
  refine (compare (σ.twist nu.toMonoidHom nu.isOpen_ker) hPQ' hQP' _ _ hTF hTR).mpr ?_
  exact scalar_conjugation E₁.toLinearEquiv E₂.toLinearEquiv
    JF.toLinearMap JR.toLinearMap c hScalar

end DynamicRankOneWall

end Langlands.Plancherel.DynamicCommonLeviComposition

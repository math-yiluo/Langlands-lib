import Langlands.Representation.Jacquet.StandardBernsteinFixedVectorReduction
import Langlands.Representation.CuspidalSupport.BernsteinStandardStages
import Langlands.Representation.Aubert.General.RationalLeviCuspidalityTransportProof
import Langlands.Representation.Aubert.General.GroupTransport
import Langlands.Representation.Aubert.General.CuspidalRemainderTransport
import Langlands.Representation.Aubert.General.RationalIwasawaCartan
import Langlands.GroupScheme.Rational.StandardLeviNestedTransport

/-! # Standard induction inside a represented standard Levi -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open Langlands.GroupScheme.StandardLeviNested
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u v

local instance innerLeviAffine {F : Type u} [Field F]
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ H)
    (ν : cocharacterLattice T) (K : Finset (SimpleRoot s ν)) :
    IsAffine (bernsteinLeviScheme s ν K).X.left := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsClosedImmersion (Standard.leviHom s ν (rootSet s ν K)).hom.hom.left :=
    Standard.isClosedSubgroup_leviHom s ν (rootSet s ν K)
  exact isAffine_of_isAffineHom (Standard.leviHom s ν (rootSet s ν K)).hom.hom.left

local instance innerLeviTopology {F : Type u} [Field F] [TopologicalSpace F]
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ H)
    (ν : cocharacterLattice T) (K : Finset (SimpleRoot s ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme s ν K)) := pointTopology

variable {F : Type u} [Field F] {G M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T) (J : Finset (SimpleRoot i ν)) (j : M ⟶ G)

/-- A closed representative of the given standard Levi. -/
structure BernsteinLeviPresentation : Prop where
  connectedReductive : IsConnectedReductive M
  closed : IsClosedSubgroup j
  represented : (standardLevi i ν (rootSet i ν J)).IsRepresentedBy j

namespace BernsteinLeviPresentation

variable {i ν J j} (D : BernsteinLeviPresentation i ν J j)

/-- The ambient split torus factored through the represented Levi. -/
abbrev torus := standardLeviTorusFactor i ν (rootSet i ν J) D.represented

variable [TopologicalSpace F]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
local instance : TopologicalSpace (rationalPoints G) := pointTopology
local instance : TopologicalSpace (rationalPoints M) := pointTopology

/-- The actual point group of the representative with its canonical topology. -/
def points : rationalPoints M ≃ₜ* levi i ν J :=
  rationalPointSubgroupHomeomorph F (standardLevi i ν (rootSet i ν J)) j D.represented D.closed

/-- The point equivalence takes ambient values through the specified inclusion. -/
@[simp] theorem points_apply_coe (x : rationalPoints M) :
    (D.points x : rationalPoints G) = rationalPoints.map j x := rfl

variable (family : BernsteinStandardFamily i ν)

include family in
private theorem families :
    simpleRelativeRoots D.torus ν = rootSet i ν J ∧ IsGenericCocharacter D.torus ν ∧
      ∀ K : Set (characterLattice T), K ⊆ rootSet i ν J →
        standardParabolic D.torus ν K = (standardParabolic i ν K).comap j ∧
        standardLevi D.torus ν K = (standardLevi i ν K).comap j ∧
        standardUnipotent D.torus ν K = (standardUnipotent i ν K).comap j :=
  standardLeviStandardFamilies dynamicLie standardCocharacter F G family.connectedReductive T i
    family.maximalSplitTorus ν family.genericCocharacter (rootSet i ν J) (rootSet_subset i ν J)
    M D.connectedReductive j D.represented D.closed

variable [ValuativeRel F] [IsNonarchimedeanLocalField F] in
include family in
/-- The intrinsic Bernstein family with the induced split torus and generic cocharacter. -/
theorem standardFamily : BernsteinStandardFamily D.torus ν :=
  Jacquet.standardBernsteinFamily D.torus ν D.connectedReductive
    (family.maximalSplitTorus.isMaximalSplitTorus_standardLeviTorusFactor i ν (rootSet i ν J)
      D.represented D.closed) (D.families family).2.1

/-- Interpret an intrinsic label as a nested ambient label. -/
def innerIndex (K : Finset (SimpleRoot D.torus ν)) : Finset J :=
  K.map (leviSimpleRootEquivOfEq i D.torus ν J (D.families family).1).toEmbedding

/-- The resulting ambient roots form the same set of characters. -/
theorem rootSet_innerIndex (K : Finset (SimpleRoot D.torus ν)) :
    rootSet i ν (leviIndex J (D.innerIndex family K)) = rootSet D.torus ν K :=
  rootSet_leviIndex_map_leviSimpleRootEquivOfEq i D.torus ν J (D.families family).1 K

/-- The intrinsic standard subgroup functors are preimages of the ambient ones. -/
theorem innerSubgroups (K : Finset (SimpleRoot D.torus ν)) :
    let S := rootSet i ν (leviIndex J (D.innerIndex family K))
    standardParabolic D.torus ν (rootSet D.torus ν K) = (standardParabolic i ν S).comap j ∧
      standardLevi D.torus ν (rootSet D.torus ν K) = (standardLevi i ν S).comap j ∧
      standardUnipotent D.torus ν (rootSet D.torus ν K) = (standardUnipotent i ν S).comap j := by
  dsimp only
  rw [D.rootSet_innerIndex family K]
  exact (D.families family).2.2 _ ((rootSet_subset D.torus ν K).trans
    (D.families family).1.subset)

/-- The intrinsic inducing Levi and its ambient representative are isomorphic over the
ambient group. -/
def innerLeviIso (K : Finset (SimpleRoot D.torus ν)) :
    bernsteinLeviScheme D.torus ν K ≅ bernsteinLeviScheme i ν (leviIndex J (D.innerIndex family K)) :=
  nestedIso D.represented.1 (D.innerSubgroups family K).2.1.symm
    (Standard.isRepresentedBy_leviHom D.torus ν (rootSet D.torus ν K))
    (by
      rw [D.represented.2, ← (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J)).2]
      exact standardLevi_le_range_leviHom family.connectedReductive i family.maximalSplitTorus ν
        family.genericCocharacter (rootSet_subset i ν J) (by
          rintro α ⟨β, hβ, rfl⟩
          exact ⟨β, leviIndex_subset J _ hβ, rfl⟩))
    (Standard.isRepresentedBy_leviHom i ν _)

/-- The inducing Levi isomorphism commutes with both inclusions into the ambient group. -/
theorem innerLeviIso_hom_comp (K : Finset (SimpleRoot D.torus ν)) :
    (D.innerLeviIso family K).hom ≫
      Standard.leviHom i ν (rootSet i ν (leviIndex J (D.innerIndex family K))) =
      Standard.leviHom D.torus ν (rootSet D.torus ν K) ≫ j :=
  nestedIso_hom_comp _ _ _ _ _

/-- The subgroup membership comparisons on rational points for the two presentations. -/
theorem innerPointMembership (K : Finset (SimpleRoot D.torus ν)) (x : rationalPoints M) :
    let L := leviIndex J (D.innerIndex family K)
    (x ∈ parabolic D.torus ν K ↔ D.points x ∈ (parabolic i ν L).subgroupOf (levi i ν J)) ∧
      (x ∈ levi D.torus ν K ↔ D.points x ∈ (levi i ν L).subgroupOf (levi i ν J)) ∧
      (x ∈ unipotent D.torus ν K ↔ D.points x ∈ (unipotent i ν L).subgroupOf (levi i ν J)) := by
  let L := leviIndex J (D.innerIndex family K)
  have h (S : SubgroupFunctor M) (S' : SubgroupFunctor G) (heq : S = S'.comap j) :
      x ∈ S.carrier (Over.mk (𝟙 _)) ↔
        (D.points x : rationalPoints G) ∈ S'.carrier (Over.mk (𝟙 _)) := by
    rw [D.points_apply_coe, heq]
    rfl
  obtain ⟨hp, hl, hu⟩ := D.innerSubgroups family K
  exact ⟨h _ _ hp, h _ _ hl, h _ _ hu⟩

variable [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Induction inside the represented Levi, followed by induction from its literal image,
is direct standard induction of the transported inducing representation. -/
def innerInductionStagesIso (K : Finset (SimpleRoot D.torus ν))
    (σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints (bernsteinLeviScheme D.torus ν K))) :
    let A := D.innerIndex family K
    let L := leviIndex J A
    let H := D.standardFamily family
    let e := D.points
    let τ := bernsteinLiteralLeviRep i ν L (rationalIsoPullback (D.innerLeviIso family K).symm σ)
    let own := normalizedInductionFunctor.{u, max u v} (H.decomposition K) (H.closedUnipotent K)
    let outer := normalizedInductionFunctor.{u, max u v} (family.decomposition J) (family.closedUnipotent J)
    outer.obj (SmoothRep.pullback e.symm (own.obj (bernsteinLiteralLeviRep D.torus ν K σ))) ≅
    (normalizedInductionFunctor.{u, max u v} (family.decomposition L) (family.closedUnipotent L)).obj
      τ := by
  intro A L H e τ own outer
  let := (family.closedLevi J).locallyCompactSpace
  let hle := levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
    family.maximalSplitTorus family.genericCocharacter L J (leviIndex_subset J A)
  let eL := GroupTransport.subgroupEquiv e (fun x => (D.innerPointMembership family K x).2.1)
  let τ' := SmoothRep.pullback (subgroupOfContinuousEquiv hle) τ
  let inner := normalizedInductionFunctor.{u, max u v} (family.leviDecomposition J A)
    ((family.closedUnipotent L).preimage continuous_subtype_val)
  have hpoint (x : levi D.torus ν K) :
      rationalPointIso (D.innerLeviIso family K).symm
        ((leviRationalPointHomeomorph i ν L).symm (subgroupOfContinuousEquiv hle (eL x))) =
      (leviRationalPointHomeomorph D.torus ν K).symm x := by
    let s := D.innerLeviIso family K
    let y := (leviRationalPointHomeomorph D.torus ν K).symm x
    let z := (leviRationalPointHomeomorph i ν L).symm (subgroupOfContinuousEquiv hle (eL x))
    apply (rationalPointIso s).injective
    change rationalPointIso s (rationalPointIso s.symm z) = rationalPointIso s y
    have hz := rationalPointIso_symm_apply_apply s.symm z
    rw [Iso.symm_symm_eq] at hz
    rw [hz]
    apply (leviRationalPointHomeomorph i ν L).injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [leviRationalPointHomeomorph_apply_coe, rationalPointIso_apply,
      subgroupOfContinuousEquiv_apply]
    change rationalPoints.map j (x : rationalPoints M) =
      rationalPoints.map (Standard.leviHom i ν (rootSet i ν L)) (rationalPoints.map s.hom y)
    have hy : rationalPoints.map (Standard.leviHom D.torus ν (rootSet D.torus ν K)) y =
        (x : rationalPoints M) := by
      rw [← leviRationalPointHomeomorph_apply_coe, ContinuousMulEquiv.apply_symm_apply]
    rw [← hy]
    simpa only [rationalPoints_map_comp_apply] using
      congrArg (fun f : bernsteinLeviScheme D.torus ν K ⟶ G => rationalPoints.map f y)
        (D.innerLeviIso_hom_comp family K).symm
  let changeInducer : SmoothRep.pullback eL τ' ≅ bernsteinLiteralLeviRep D.torus ν K σ :=
    SmoothRep.mkIso (equivOfRepresentationEq (by
      ext x w
      exact congrArg (fun m => σ.representation m w) (hpoint x)))
  let transport := GroupTransport.inductionIsoApp.{u, max u v}
    (family.leviDecomposition J A) (H.decomposition K)
    e (fun x => (D.innerPointMembership family K x).1)
    (fun x => (D.innerPointMembership family K x).2.1)
    (fun x => (D.innerPointMembership family K x).2.2)
    ((family.closedUnipotent L).preimage continuous_subtype_val) (H.closedUnipotent K) τ'
  let comparison : SmoothRep.pullback e (inner.obj τ') ≅
      own.obj (bernsteinLiteralLeviRep D.torus ν K σ) := transport ≪≫ own.mapIso changeInducer
  let undo : SmoothRep.pullback e.symm (own.obj (bernsteinLiteralLeviRep D.torus ν K σ)) ≅
      inner.obj τ' := (SmoothRep.pullbackFunctor e.symm).mapIso comparison.symm ≪≫
        SmoothRep.pullbackSymmIso e (inner.obj τ')
  exact outer.mapIso undo ≪≫ (bernsteinStandardInductionStagesIso.{u, v} i ν family J A).app τ

end BernsteinLeviPresentation

/-- Induction from an intrinsic standard Levi of a closed representative of a
standard Levi agrees in two stages with direct induction in the ambient group. -/
def BernsteinInnerStandardInductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F]
    (G M : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (family : BernsteinStandardFamily i ν)
    (J : Finset (SimpleRoot i ν)) (j : M ⟶ G) (D : BernsteinLeviPresentation i ν J j),
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    letI : TopologicalSpace (rationalPoints M) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)]
      (K : Finset (SimpleRoot D.torus ν))
      (σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints (bernsteinLeviScheme D.torus ν K))),
      let A := D.innerIndex family K
      let L := leviIndex J A
      let H := D.standardFamily family
      let e := D.points
      let τ := bernsteinLiteralLeviRep i ν L (rationalIsoPullback (D.innerLeviIso family K).symm σ)
      let own := normalizedInductionFunctor.{u, max u v} (H.decomposition K) (H.closedUnipotent K)
      let outer := normalizedInductionFunctor.{u, max u v} (family.decomposition J) (family.closedUnipotent J)
      Nonempty (outer.obj (SmoothRep.pullback e.symm (own.obj (bernsteinLiteralLeviRep D.torus ν K σ))) ≅
        (normalizedInductionFunctor.{u, max u v} (family.decomposition L) (family.closedUnipotent L)).obj
          τ)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The object isomorphism comes from the transport of normalized induction and
the standard induction-in-stages isomorphism. -/
theorem bernsteinInnerStandardInduction : BernsteinInnerStandardInductionStatement.{u, v} := by
  intro F _ _ _ _ G M _ _ _ T i ν family J j D
  dsimp only
  intro _ _ _ _ K σ
  exact ⟨D.innerInductionStagesIso.{u, v} family K σ⟩

end Langlands.CuspidalSupport

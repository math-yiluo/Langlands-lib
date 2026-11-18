import Langlands.GroupScheme.RelativeLevi.SplitFaceParabolicAction
import Langlands.GroupScheme.RelativeUnipotent.ParabolicVectorLayerLinearity
import Langlands.GroupScheme.RelativeUnipotent.RootWeightQuotientEquivariance
import Langlands.GroupScheme.AutomorphicActionPointIso

/-! # Actual original-parabolic automorphisms of face-weight vector layers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell RelativeUnipotent

variable {R : Type u} [CommRing R] [Nontrivial R]
  {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {fam : J → (Ga R ⟶ G)} {wt : I → ℤ}
  (C : SplitParabolicFaceChart i P fam wt)
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))

local instance splitFaceLinearityAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance splitFaceLinearityAuxiliaryMono :
    Mono (Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)).hom.hom :=
  (Dynamic.Affine.isRepresentedBy_unipotentHom _).1

local instance splitFaceLinearityTermMono (d : ℕ) :
    Mono (C.weights.inclusion d).hom.hom :=
  (C.weights.isRepresentedBy_inclusion d).1

/-- The face-realizing cocharacter acts through the actual torus action on each term. -/
def faceScalarAction (d : ℕ) :
    AutomorphicAction (Gm (Spec (CommRingCat.of R))).toGrp (C.weights.groupScheme d) :=
  C.weights.cocharacterAction
    (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter))
    C.root_comp (fun a T s x => (hfam a).equivariant T s x) C.faceCocharacter d

omit [Nontrivial R] [DecidableEq I] [Fintype J] in
include hfam in
/-- This is the actual ambient face-cocharacter conjugation on every scheme test. -/
theorem faceScalarAction_comp (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (s : T ⟶ (Gm (Spec (CommRingCat.of R))).X)
    (x : T ⟶ (C.weights.groupScheme d).X) :
    (C.faceScalarAction hfam d).act s x ≫
        (C.weights.ambientInclusion
          (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) d).hom.hom =
      (s ≫ (AffineRegularBorel.cocharacter i C.faceCocharacter).hom.hom) *
        (x ≫ (C.weights.ambientInclusion
          (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) d).hom.hom) *
        (s ≫ (AffineRegularBorel.cocharacter i C.faceCocharacter).hom.hom)⁻¹ := by
  let j := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  let hu : TorusEquivariant i (fun a => P.root a) fam :=
    fun a T s x => (hfam a).equivariant T s x
  let v := CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I C.faceCocharacter)
  have hi := C.weights.torusAction_inclusion j C.root_comp hu d (s ≫ v.hom.hom) x
  have hc := C.chart.torusAction_comp j C.root_comp hu (s ≫ v.hom.hom)
    (x ≫ (C.weights.inclusion d).hom.hom)
  have he := (congrArg (fun y => y ≫ j.hom.hom) hi).trans hc
  simpa only [faceScalarAction, RootWeightData.cocharacterAction,
    AutomorphicAction.restrict_act, RootWeightData.ambientInclusion,
    AffineRegularBorel.cocharacter, Grp.comp_hom_hom, Category.assoc, j, hu, v] using he

omit [Nontrivial R] [DecidableEq I] in
include hfam in
/-- The actual quotient has the positive scalar power of the realized face height. -/
theorem quotientMap_faceScalarAction (d : ℕ) :
    (C.faceScalarAction hfam d).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d))
        (C.faceMultiplier * (d + 1))) (C.weights.quotientMap d) := by
  apply C.weights.quotientMap_isEquivariant_of_realization
    (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter))
    C.root_comp (fun a T s x => (hfam a).equivariant T s x)
    C.faceCocharacter C.faceMultiplier
  intro k
  rw [C.facePairing, C.weight_eq]

include hG hmax hP hfam in
/-- The original parabolic action retains the prescribed ambient conjugation. -/
theorem originalParabolicAction_comp (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (u : T ⟶ (AffineRegularBorel.borel i wt).X)
    (x : T ⟶ (C.weights.groupScheme d).X) :
    (C.originalParabolicAction hG hmax hP hfam d).act u x ≫
        (C.weights.ambientInclusion
          (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) d).hom.hom =
      (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom) *
        (x ≫ (C.weights.ambientInclusion
          (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) d).hom.hom) *
        (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)⁻¹ := by
  simp only [originalParabolicAction, AutomorphicAction.onRepresentedSubgroup_act_comp,
    AutomorphicAction.conjugation_act]

/-- Evaluate the actual original-parabolic action on a represented term. -/
def originalParabolicTermIso (d : ℕ)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (AffineRegularBorel.borel i wt).X) :
    C.weights.groupScheme d ≅ C.weights.groupScheme d :=
  (C.originalParabolicAction hG hmax hP hfam d).basePointIso u

include hG hmax hP hfam in
/-- The evaluated term automorphism is actual ambient conjugation by the parabolic point. -/
theorem originalParabolicTermIso_comp (d : ℕ)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (AffineRegularBorel.borel i wt).X)
    (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ (C.weights.groupScheme d).X) :
    (x ≫ (C.originalParabolicTermIso hG hmax hP hfam d u).hom.hom.hom) ≫
        (C.weights.ambientInclusion
          (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) d).hom.hom =
      G.constantPoint (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom) T *
        (x ≫ (C.weights.ambientInclusion
          (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) d).hom.hom) *
        (G.constantPoint (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom) T)⁻¹ := by
  rw [originalParabolicTermIso, AutomorphicAction.comp_basePointIso_hom,
    C.originalParabolicAction_comp hG hmax hP hfam]
  simp only [constantPoint, Category.assoc]

include hG hmax hP hfam in
/-- Actual parabolic term automorphisms commute with the actual consecutive inclusion. -/
theorem originalParabolicTermIso_step (d : ℕ)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (AffineRegularBorel.borel i wt).X) :
    C.weights.step d ≫ (C.originalParabolicTermIso hG hmax hP hfam d u).hom =
      (C.originalParabolicTermIso hG hmax hP hfam (d + 1) u).hom ≫ C.weights.step d := by
  let j := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  have : Mono (C.weights.ambientInclusion j d).hom.hom := by
    change Mono ((C.weights.inclusion d).hom.hom ≫ j.hom.hom)
    exact mono_comp' (C.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter i C.cocharacter)).1
  have hs (T : Over (Spec (CommRingCat.of R)))
      (x : T ⟶ (C.weights.groupScheme (d + 1)).X) :
      (x ≫ (C.weights.step d).hom.hom) ≫ (C.weights.ambientInclusion j d).hom.hom =
        x ≫ (C.weights.ambientInclusion j (d + 1)).hom.hom := by
    simpa only [RootWeightData.ambientInclusion, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun y => y ≫ j.hom.hom) (C.weights.comp_step_inclusion d T x)
  apply hom_ext_points
  intro T x
  change (x ≫ (C.weights.step d).hom.hom) ≫
      (C.originalParabolicTermIso hG hmax hP hfam d u).hom.hom.hom =
    (x ≫ (C.originalParabolicTermIso hG hmax hP hfam (d + 1) u).hom.hom.hom) ≫
      (C.weights.step d).hom.hom
  apply (cancel_mono (C.weights.ambientInclusion j d).hom.hom).mp
  rw [C.originalParabolicTermIso_comp hG hmax hP hfam, hs, hs,
    C.originalParabolicTermIso_comp hG hmax hP hfam]

/-- The actual vector quotient automorphism induced by original-parabolic conjugation. -/
def originalParabolicQuotientIso (d : ℕ)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (AffineRegularBorel.borel i wt).X) :
    VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (C.weights.exactSupport d)) ≅
      VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (C.weights.exactSupport d)) :=
  C.weights.conjugationQuotientIso d
    (C.originalParabolicTermIso hG hmax hP hfam d u)
    (C.originalParabolicTermIso hG hmax hP hfam (d + 1) u)
    (C.originalParabolicTermIso_step hG hmax hP hfam d u)

include hG hmax hP hfam in
/-- The constructed quotient automorphism descends the actual original-parabolic term action. -/
theorem originalParabolicQuotientIso_fac (d : ℕ)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (AffineRegularBorel.borel i wt).X) :
    C.weights.quotientMap d ≫ (C.originalParabolicQuotientIso hG hmax hP hfam d u).hom =
      (C.originalParabolicTermIso hG hmax hP hfam d u).hom ≫ C.weights.quotientMap d :=
  C.weights.conjugationQuotientIso_fac d _ _ _

include hG hmax hP hfam in
/-- Full actual parabolic conjugation is scalar-equivariant on the actual vector layer. -/
theorem originalParabolicQuotientIso_isEquivariant (d : ℕ)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (AffineRegularBorel.borel i wt).X) :
    (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d))
      (C.faceMultiplier * (d + 1))).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d))
        (C.faceMultiplier * (d + 1)))
      (C.originalParabolicQuotientIso hG hmax hP hfam d u).hom := by
  intro T s x
  let j := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  have hnorm : (SubgroupFunctor.range (C.weights.inclusion d ≫ j)).IsNormalizedBy
      (Dynamic.parabolic (AffineRegularBorel.cocharacter i C.faceCocharacter)) := by
    rw [C.parabolic_faceCocharacter hG hmax hP hfam]
    exact C.range_inclusion_isNormalizedBy_originalParabolic hG hmax hP hfam d
  have hp : u ≫ (AffineRegularBorel.inclusion i wt).hom.hom ∈
      (Dynamic.parabolic (AffineRegularBorel.cocharacter i C.faceCocharacter)).carrier
        (Over.mk (𝟙 _)) := by
    rw [C.parabolic_faceCocharacter hG hmax hP hfam,
      ← (Dynamic.Affine.isRepresentedBy_parabolicHom
        (AffineRegularBorel.cocharacter i wt)).2]
    exact SubgroupFunctor.mem_range.mpr ⟨u, rfl⟩
  exact C.weights.conjugationQuotientIso_isEquivariant j
    (AffineRegularBorel.cocharacter i C.faceCocharacter)
    (C.isRepresentedBy_faceCocharacter hG hmax hP hfam) d hnorm
    (C.faceScalarAction hfam d) (C.faceScalarAction_comp hfam d)
    (C.faceMultiplier * (d + 1)) (C.quotientMap_faceScalarAction hfam d)
    (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom) hp
    (C.originalParabolicTermIso hG hmax hP hfam d u)
    (C.originalParabolicTermIso hG hmax hP hfam (d + 1) u)
    (C.originalParabolicTermIso_step hG hmax hP hfam d u)
    (C.originalParabolicTermIso_comp hG hmax hP hfam d u) s x

include hG hmax hP hfam in
/-- The all-algebra scalar identity is proved for the actual original-parabolic quotient automorphism. -/
theorem originalParabolicQuotientIso_hasScalarWeight (d : ℕ)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (AffineRegularBorel.borel i wt).X) :
    VectorGroup.HasScalarWeight
      (VectorGroup.pointTransformation
        (C.originalParabolicQuotientIso hG hmax hP hfam d u).hom)
      (C.faceMultiplier * (d + 1)) :=
  VectorGroup.hasScalarWeight_of_equivariant _ _
    (C.originalParabolicQuotientIso_isEquivariant hG hmax hP hfam d u)

/-- The actual original-parabolic quotient action is linear over every coefficient algebra. -/
def originalParabolicLayerLinearEquiv (d : ℕ)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (AffineRegularBorel.borel i wt).X)
    (A : CommAlgCat.{u} (CommRingCat.of R)) :
    (Fin (Nat.card (C.weights.exactSupport d)) → A) ≃ₗ[A]
      (Fin (Nat.card (C.weights.exactSupport d)) → A) :=
  VectorGroup.linearEquivOfWeight (C.originalParabolicQuotientIso hG hmax hP hfam d u)
    (Nat.mul_pos C.faceMultiplier_pos (Nat.succ_pos d))
    (C.originalParabolicQuotientIso_hasScalarWeight hG hmax hP hfam d u) A

include hG hmax hP hfam in
/-- The original actual quotient morphism is the morphism of its base-ring matrix. -/
theorem originalParabolicQuotientIso_eq_matrixHom (d : ℕ)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (AffineRegularBorel.borel i wt).X) :
    (C.originalParabolicQuotientIso hG hmax hP hfam d u).hom =
      VectorGroup.matrixHom (VectorGroup.weightMatrix
        (VectorGroup.pointTransformation
          (C.originalParabolicQuotientIso hG hmax hP hfam d u).hom)) :=
  VectorGroup.eq_matrixHom_of_hasScalarWeight _
    (Nat.mul_pos C.faceMultiplier_pos (Nat.succ_pos d))
    (C.originalParabolicQuotientIso_hasScalarWeight hG hmax hP hfam d u)

end Langlands.GroupScheme.SplitParabolicFaceChart

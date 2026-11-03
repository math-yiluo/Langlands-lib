import Langlands.AlgebraicGeometry.Picard.ClosedFibreGenericFrames
import Langlands.AlgebraicGeometry.Picard.NormalizedTransitionExtension
import Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement

/-! # Generic line-bundle extension with explicit affine projectivity -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))

/-- Projectivity of the actual algebras on affine opens meeting the closed fibre. -/
def AffineClosedFibreSectionProjectivity : Prop :=
  ∀ (U : X.Opens) (hU : IsAffineOpen U),
    (p ⁻¹' {IsLocalRing.closedPoint R} ∩ (U : Set X)).Nonempty →
      letI := affineSectionAlgebra p hU
      Module.Projective R Γ(X, U)

include p in
/-- The published integral-fibre projectivity proposition, if supplied,
applies to precisely the actual affine section algebras used here. -/
theorem affineClosedFibreSectionProjectivity_of_integralFibreProjectivity
    [Smooth p] [GeometricallyConnected p]
    (h : Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement.{u}) :
    AffineClosedFibreSectionProjectivity p := by
  intro U hU hmeet
  let := affineSectionAlgebra p hU
  let := finitePresentation_affineSectionAlgebra p hU
  let := flat_affineSectionAlgebra p hU
  let := geometricallyIntegral_affineSectionAlgebra p hU hmeet
  exact h R Γ(X, U) inferInstance inferInstance inferInstance

variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (q : Y ⟶ X) (s : Y ⟶ Spec (CommRingCat.of K))
    (H : IsPullback q s p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    [Smooth p] [GeometricallyConnected p] [UniversallyClosed p] [IsSeparated p]
    (hproj : AffineClosedFibreSectionProjectivity p)
    (hinj : ∀ U : X.Opens, Function.Injective (q.app U))
    (D : LineBundle Y) (F : ClosedFibreGenericFrames q D p)

include p K s H hproj hinj F in
/-- Affine closed-fibre frames and projectivity of actual affine algebras
give an actual extension of the generic line bundle. -/
theorem exists_lineBundle_of_closedFibre_frames_of_projective :
    ∃ E : LineBundle X, Nonempty (((LineBundle.pullback q).obj E).obj ≅ D.obj) := by
  let : IsIntegral (p.fiber (IsLocalRing.closedPoint R)) :=
    integral_fibre_of_smooth_geometricallyConnected p _
  let i₀ := genericPoint (p.fiber (IsLocalRing.closedPoint R))
  have hInf : ∀ {U V : X.Opens}, IsAffineOpen U → IsAffineOpen V →
      IsAffineOpen (U ⊓ V) := by
    intro U V hU hV
    exact isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (pullback.diagonal p)) ⊤ (isAffineOpen_top _)
      U (by simp) V (by simp) hU hV
  have hpair := fun i j => hInf (F.affine i) (F.affine j)
  have hmeet : ∀ i j,
      (p ⁻¹' {IsLocalRing.closedPoint R} ∩
        ((F.opens i ⊓ F.opens j) : Set X)).Nonempty := by
    intro i j
    exact ⟨closedFibreGenericPoint p, (closedFibreGenericPoint_spec p).mem,
      F.commonPoint_mem i, F.commonPoint_mem j⟩
  let n := CocycleGluing.affineGenericScalarNormalization
    (q := q) (T := F.opens) (g := CocycleGluing.frameCocycle F.frame F.isFrame) (i₀ := i₀)
    p K s H F.affine (hpair i₀) (hmeet i₀)
    (fun i => hproj _ (hpair i₀ i) (hmeet i₀ i))
  apply CocycleGluing.exists_lineBundle_of_normalized_frames p K s H hinj F.iSup_eq_top D
    F.isFrame n hpair
    (fun i j => hInf (hpair i j) (F.affine i₀)) ?_
    (fun i j => hproj _ (hpair i j) (hmeet i j))
  intro i j
  exact ⟨closedFibreGenericPoint p, (closedFibreGenericPoint_spec p).mem,
    ⟨F.commonPoint_mem i, F.commonPoint_mem j⟩, F.commonPoint_mem i₀⟩

/-- The actual total bundle obtained from closed-fibre frames and actual
affine section projectivity. -/
def lineBundleOfClosedFibreFrames : LineBundle X :=
  Classical.choose (exists_lineBundle_of_closedFibre_frames_of_projective p K q s H
    hproj hinj D F)

/-- The chosen total bundle pulls back to the original generic bundle as
an actual module sheaf under `q`. -/
def closedFibreFramesIso :
    ((LineBundle.pullback q).obj
      (lineBundleOfClosedFibreFrames p K q s H hproj hinj D F)).obj ≅ D.obj :=
  Classical.choice (Classical.choose_spec
    (exists_lineBundle_of_closedFibre_frames_of_projective p K q s H hproj hinj D F))

variable {q s H hinj D F}

/-- A generic line bundle extends along the canonical generic projection
when the total smooth proper geometry has the stated affine projectivity. -/
def projectiveGenericLineBundleExtension
    (D : LineBundle (pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    LineBundle X :=
  lineBundleOfClosedFibreFrames p K (pullback.fst _ _) (pullback.snd _ _)
    (.of_hasPullback _ _) hproj (genericPullback_app_injective K p) D
    (smoothClosedFibreGenericFrames p K D)

/-- The canonical generic restriction of the chosen extension is the
original line-bundle sheaf. -/
def projectiveGenericLineBundleExtensionIso
    (D : LineBundle (pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    ((LineBundle.pullback (pullback.fst _ _)).obj
      (projectiveGenericLineBundleExtension p K hproj D)).obj ≅ D.obj :=
  closedFibreFramesIso p K (pullback.fst _ _) (pullback.snd _ _)
    (.of_hasPullback _ _) hproj (genericPullback_app_injective K p) D
    (smoothClosedFibreGenericFrames p K D)

end Langlands.AlgebraicGeometry.Picard

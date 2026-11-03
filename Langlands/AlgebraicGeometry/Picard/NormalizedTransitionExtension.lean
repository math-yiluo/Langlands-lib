import Langlands.AlgebraicGeometry.Picard.GenericFrameNormalization
import Langlands.AlgebraicGeometry.Picard.GenericTransitionExtension

/-! # Extending normalized generic frame transitions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.CocycleGluing

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X Y : Scheme.{u}} {ι : Type u}
    (p : X ⟶ Spec (CommRingCat.of R))
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {q : Y ⟶ X} (s : Y ⟶ Spec (CommRingCat.of K))
    (H : IsPullback q s p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    [Smooth p] [GeometricallyConnected p]
    {T : ι → X.Opens} {g : ∀ i j, Γ(Y, q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j)ˣ} {i₀ : ι}

/-- A normalized generic transition lifts to a total unit by testing it
on the common affine reference subopen meeting the closed fibre. -/
def GenericScalarNormalization.transitionUnit
    (n : GenericScalarNormalization q T g i₀) (hg : IsCocycle g)
    (i j : ι) (hij : IsAffineOpen (T i ⊓ T j))
    (hW : IsAffineOpen ((T i ⊓ T j) ⊓ T i₀))
    (hmeet : (p ⁻¹' {IsLocalRing.closedPoint R} ∩
      (((T i ⊓ T j) ⊓ T i₀) : Set X)).Nonempty)
    (hproj : letI := affineSectionAlgebra p hij;
      Module.Projective R Γ(X, T i ⊓ T j)) :
    {a : Γ(X, T i ⊓ T j)ˣ //
      sectionUnitPullback q (T i ⊓ T j) a = unitGaugeCocycle g n.scalar i j} := by
  let W := (T i ⊓ T j) ⊓ T i₀
  let b : Γ(Y, q ⁻¹ᵁ (T i ⊓ T j))ˣ := unitGaugeCocycle g n.scalar i j
  let c : Γ(X, W)ˣ :=
    (sectionUnitRestrict (le_inf inf_le_right (inf_le_left.trans inf_le_left))
      (n.totalUnit i))⁻¹ *
    sectionUnitRestrict (le_inf inf_le_right (inf_le_left.trans inf_le_right))
      (n.totalUnit j)
  have hc :
      Y.presheaf.map (homOfLE (q.preimage_mono (inf_le_left :
        W ≤ T i ⊓ T j))).op (b : Γ(Y, q ⁻¹ᵁ (T i ⊓ T j))) =
          q.app W (c : Γ(X, W)) := by
    have h := n.transition_restrict hg i j
      (W := W) inf_le_right (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)
    exact congrArg (fun z : Γ(Y, q ⁻¹ᵁ W)ˣ => (z : Γ(Y, q ⁻¹ᵁ W))) h
  let a := affineGenericUnitOfRestriction p hij hW inf_le_left K q s H
    hmeet hproj b c hc
  refine ⟨a.val, ?_⟩
  apply Units.ext
  exact a.property

variable (hinj : ∀ U : X.Opens, Function.Injective (q.app U))
    (hcover : (⨆ i, T i) = ⊤) (D : LineBundle Y)
    {e : ∀ i, Γ(D.obj, q ⁻¹ᵁ T i)}
    (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (q ⁻¹ᵁ T i))
    (n : GenericScalarNormalization q T (frameCocycle e he) i₀)
    (hpair : ∀ i j, IsAffineOpen (T i ⊓ T j))
    (htriple : ∀ i j, IsAffineOpen ((T i ⊓ T j) ⊓ T i₀))
    (hmeet : ∀ i j, (p ⁻¹' {IsLocalRing.closedPoint R} ∩
      (((T i ⊓ T j) ⊓ T i₀) : Set X)).Nonempty)
    (hproj : ∀ i j, letI := affineSectionAlgebra p (hpair i j);
      Module.Projective R Γ(X, T i ⊓ T j))

include p K s H hinj hcover he n hpair htriple hmeet hproj in
/-- Normalization and projectivity of the actual overlap algebras suffice
to extend a generic line bundle to an actual total line bundle. -/
theorem exists_lineBundle_of_normalized_frames :
    ∃ E : LineBundle X, Nonempty (((LineBundle.pullback q).obj E).obj ≅ D.obj) := by
  have he' := unitGaugeFrames_isFrame e he n.scalar
  apply exists_lineBundle_of_frameCocycle_lifts q hinj hcover D he'
  intro i j
  let a := n.transitionUnit p K s H
    (isCocycle_of_isTransition he (isTransition_frameCocycle he)) i j
    (hpair i j) (htriple i j) (hmeet i j) (hproj i j)
  refine ⟨a.val, ?_⟩
  rw [frameCocycle_unitGaugeFrames e he n.scalar]
  have ha := a.property
  change Units.map (q.app (T i ⊓ T j)).hom.toMonoidHom a.val = _ at ha
  rw [Scheme.Hom.app_eq_appLE] at ha
  exact ha

/-- Choose an actual total line bundle extending the normalized generic
frames. The scalar changes affect frames, not the given generic bundle. -/
def lineBundleOfNormalizedFrames : LineBundle X :=
  Classical.choose (exists_lineBundle_of_normalized_frames p K s H hinj hcover D
    he n hpair htriple hmeet hproj)

/-- The chosen extension comes with an actual module-sheaf isomorphism
under the original morphism `q`. -/
def normalizedFramesIso :
    ((LineBundle.pullback q).obj
      (lineBundleOfNormalizedFrames p K s H hinj hcover D he n
        hpair htriple hmeet hproj)).obj ≅ D.obj :=
  Classical.choice (Classical.choose_spec
    (exists_lineBundle_of_normalized_frames p K s H hinj hcover D
      he n hpair htriple hmeet hproj))

end Langlands.AlgebraicGeometry.Picard.CocycleGluing

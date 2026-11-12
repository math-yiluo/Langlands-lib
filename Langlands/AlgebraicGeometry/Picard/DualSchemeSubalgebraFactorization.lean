import Langlands.AlgebraicGeometry.SubalgebraFactorizationFiniteType
import Langlands.AlgebraicGeometry.Picard.DualScheme
import Langlands.AlgebraicGeometry.Picard.LineBundleNormalization
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse
import Langlands.AlgebraicGeometry.Picard.Functor
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso
import Langlands.AlgebraicGeometry.Picard.OpenLocus
import Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricOpenLocusBridgeProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroFamilyGeometricPointComparison
import Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricDetectionProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AbelianScheme.MumfordTrivialLocus

/-! # Morphisms from affine schemes to the chosen dual factor through finite stages -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Every actual rigidified family of an abelian scheme over an arbitrary base scheme has a
geometric Picard-zero open locus. -/
theorem exists_isPicardZeroOpenLocus {S : Scheme.{u}} (A : AbelianScheme S) (P : Over S)
    (L : RigidifiedFamily A P) : ∃ U : P.left.Opens, IsPicardZeroOpenLocus A L U := by
  obtain ⟨U, hU⟩ := exists_isPicardZeroFamily_relativePullback_iff_of_fibreCriterion
    (fun G M ↦ ⟨mumfordTrivialLocus G M, fun K _ _ t ↦
      isTranslationInvariant_fibreLineBundle_iff G M K t⟩) A P L
  exact ⟨U, isPicardZeroOpenLocus_of_geometricPoints picardZeroGeometricDetection A L U hU⟩

variable {R : Type u} [CommRing R] (A : AbelianScheme (Spec (CommRingCat.of R)))

/-- A rigidified family over the spectrum of an `R`-algebra `B` is, up to isomorphism, the
pullback of a rigidified family over the spectrum of a finitely generated subalgebra of `B`. -/
theorem exists_rigidifiedFamily_subalgebra {B : Type u} [CommRing B] [Algebra R B]
    (F : RigidifiedFamily A (affineBase R B)) :
    ∃ (B₁ : Subalgebra R B) (_ : B₁.FG) (F₁ : RigidifiedFamily A (affineBase R B₁)),
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
          (affineSubalgebraMap B₁)
          (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) F₁) =
        RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) F := by
  let f := A.X.hom
  let T := affineBase R B
  let L₀ : LineBundle ((relativeSpace f).obj T) := (RigidifiedLineBundle.forget _).obj F
  obtain ⟨B₁, hB₁, -, L₁, ⟨e⟩⟩ := PicardGroupoid.exists_affineFamily_subalgebra f L₀ ∅
  let T₁ := affineBase R B₁
  let q : T ⟶ T₁ := affineSubalgebraMap B₁
  let c : (relativeSpace f).obj T ⟶ (relativeSpace f).obj T₁ := (relativeSpace f).map q
  let ε := (relativeSection f (unitSection A) (unitSection_comp A)).app T
  let ε₁ := (relativeSection f (unitSection A) (unitSection_comp A)).app T₁
  let p := (relativeProjection f).app T
  let p₁ := (relativeProjection f).app T₁
  have sec₁ : ε₁ ≫ p₁ = 𝟙 T₁.left := relativeSection_projection _ _ _ T₁
  have hεc : ε ≫ c = q.left ≫ ε₁ :=
    ((relativeSection f (unitSection A) (unitSection_comp A)).naturality q).symm
  have hcp : c ≫ p₁ = p ≫ q.left := (relativeProjection f).naturality q
  let N₁ : LineBundle T₁.left := (LineBundle.pullback ε₁).obj L₁
  let F₁ : RigidifiedFamily A T₁ :=
    LineBundle.normalize pullbackTensorComparisonIsIso p₁ ε₁ sec₁ L₁ N₁.inverse
      N₁.tensorInverseIso
  refine ⟨B₁, hB₁, F₁, ?_⟩
  -- the carrier of the pulled-back normalized family has the class of `L₀`
  have he : ((LineBundle.pullback c).obj L₁).classOf = L₀.classOf :=
    (LineBundle.classOf_eq_iff_iso _ _).mpr ⟨e.hom.iso⟩
  have hrig : ((LineBundle.pullback ε).obj L₀).classOf = 0 := by
    rw [← LineBundle.classOf_trivial]
    exact (LineBundle.classOf_eq_iff _ _).mpr ⟨F.obj.rigidification.symm⟩
  have hclass : ((LineBundle.pullback c).obj
      ((RigidifiedLineBundle.forget _).obj F₁)).classOf = L₀.classOf := by
    change ((LineBundle.pullback c).obj (LineBundle.tensor pullbackTensorComparisonIsIso L₁
      ((LineBundle.pullback p₁).obj N₁.inverse))).classOf = L₀.classOf
    rw [← Group.pullback_lineBundle_classOf, LineBundle.classOf_tensor, map_add,
      ← Group.pullback_lineBundle_classOf, LineBundle.classOf_inverse,
      ← Group.pullback_lineBundle_classOf, Group.pullback_lineBundle_classOf c L₁, he,
      ← AddMonoidHom.comp_apply, ← Group.pullback_comp, hcp, map_neg,
      Group.pullback_comp, AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply (Group.pullback q.left),
      ← Group.pullback_comp, ← hεc, Group.pullback_comp, AddMonoidHom.comp_apply,
      Group.pullback_lineBundle_classOf c L₁, he, Group.pullback_lineBundle_classOf, hrig,
      map_zero, neg_zero, add_zero]
  obtain ⟨e₁⟩ := (LineBundle.classOf_eq_iff_iso _ _).mp hclass
  exact Quotient.sound (RigidifiedLineBundle.nonempty_iso_of_forget_iso
    pullbackTensorComparisonIsIso p (relativeSection_projection _ _ _ T) e₁)

variable (hA : HasDualScheme A)

/-- Every morphism over `Spec R` from the spectrum of an `R`-algebra `B` to the chosen dual
factors through the spectrum of a finitely generated `R`-subalgebra of `B`. -/
theorem exists_dualScheme_subalgebra_factorization (B : Type u) [CommRing B] [Algebra R B]
    (x : affineBase R B ⟶ dualScheme A hA) :
    ∃ (B₁ : Subalgebra R B) (_ : B₁.FG) (y : affineBase R B₁ ⟶ dualScheme A hA),
      affineSubalgebraMap B₁ ≫ y = x := by
  let F := (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
    x).obj (poincareFamily A hA)
  have hF : IsPicardZeroFamily A F :=
    picardZeroPullback _ A _ _ x _ (poincareFamily_universal A hA).1
  obtain ⟨B₁, hB₁, F₁, hF₁⟩ := exists_rigidifiedFamily_subalgebra A F
  obtain ⟨U, hU⟩ := exists_isPicardZeroOpenLocus A (affineBase R B₁) F₁
  have hrange : Set.range (affineSubalgebraMap B₁).left ⊆ U := by
    refine (hU _ (affineSubalgebraMap B₁)).mp ?_
    change IsPicardZeroClass A (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
      (unitSection_comp A) (affineSubalgebraMap B₁)
      (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) F₁))
    rw [hF₁]
    exact hF
  obtain ⟨B₂, hB₂, hle, hB₂U⟩ := exists_affineAlgebraStageMap_range_subset B₁ hB₁ U hrange
  let q₂ := RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A) F₁
    (affineBase R B₂) (affineAlgebraStageMap hle)
  have hq₂ : IsPicardZeroClass A q₂ := (hU _ _).mpr hB₂U
  refine ⟨B₂, hB₂, dualClassify A hA _ ⟨q₂, hq₂⟩, ?_⟩
  rw [← dualClassify_pullback A Langlands.SchemeModule.RigidifiedModule.pullbackCoherence
    picardZeroPullback hA]
  symm
  apply dualClassify_unique
  change _ = RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
    (affineSubalgebraMap B₂) q₂
  rw [← RigidifiedLineBundle.classifyingMap_comp A.X.hom (unitSection A) (unitSection_comp A)
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence, affineAlgebraStageMap_restrict]
  exact hF₁.symm

/-- The chosen dual of an abelian scheme over an affine base is locally of finite type. -/
theorem dualScheme_locallyOfFiniteType : LocallyOfFiniteType (dualScheme A hA).hom :=
  locallyOfFiniteType_of_subalgebraFactorization _
    (fun B _ _ x ↦ exists_dualScheme_subalgebra_factorization A hA B x)

/-- The chosen dual of an abelian scheme over a noetherian affine base is locally of finite
presentation. -/
theorem dualScheme_locallyOfFinitePresentation [IsNoetherianRing R] :
    LocallyOfFinitePresentation (dualScheme A hA).hom :=
  locallyOfFinitePresentation_of_subalgebraFactorization _
    (fun B _ _ x ↦ exists_dualScheme_subalgebra_factorization A hA B x)

end Langlands.AbelianScheme

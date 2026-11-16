import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.AlgebraicGeometry.SchemeLimitRelativePropertyProof
import Langlands.AlgebraicGeometry.SchemePureFibreDimensionDescent
import Langlands.AlgebraicGeometry.RelativeDimensionLoci
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedSurjectivityLimitDescent
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentBridge
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone

/-! # Finite coefficient descent of quasi-finite flat surjective homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

open Langlands.AlgebraicGeometry
open AffineLimit SchemeLimitModel.Geometry SchemeFiberGeometry
open Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The three morphism properties retained by a noetherian quasi-finite model. -/
abbrev quasiFiniteFlatSurjectiveProperty : MorphismProperty Scheme.{u} :=
  @LocallyQuasiFinite ⊓ @Flat ⊓ @Surjective

private theorem flat_structural_descent :
    SchemeStructuralPropertyDescent.{u} @Flat := by
  intro I _ _ D S X Y _ _ t a b f w _ _ _ _ _ _ c hc p hp
  have : LocallyOfFinitePresentation (f ≫ b) := by rw [w]; infer_instance
  have : QuasiCompact (f ≫ b) := by rw [w]; infer_instance
  have : QuasiSeparated (f ≫ b) := by rw [w]; infer_instance
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation_of_comp f b
  have : QuasiCompact f := QuasiCompact.of_comp f b
  have : QuasiSeparated f := QuasiSeparated.of_comp f b
  exact relativeFlatDescent D t a b f w c hc p hp

private theorem quasiFinite_structural_descent :
    SchemeStructuralPropertyDescent.{u} @LocallyQuasiFinite := by
  intro I _ _ D S X Y _ _ t a b f w _ _ _ _ _ _ c hc p hp
  have : LocallyOfFinitePresentation (f ≫ b) := by rw [w]; infer_instance
  have : QuasiCompact (f ≫ b) := by rw [w]; infer_instance
  have : QuasiSeparated (f ≫ b) := by rw [w]; infer_instance
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation_of_comp f b
  have : QuasiCompact f := QuasiCompact.of_comp f b
  have : QuasiSeparated f := QuasiSeparated.of_comp f b
  have hft {T : Scheme.{u}} (q : T ⟶ S) :
      LocallyOfFiniteType (AffineLimit.baseChangeMap a b f w q) :=
    MorphismProperty.of_isPullback (baseChangeMap_cartesian a b f w q).flip
      (inferInstance : LocallyOfFiniteType f)
  have : LocallyOfFiniteType (AffineLimit.baseChangeMap a b f w p) := hft p
  rw [← hasPureDimensionFibers_zero_iff_locallyQuasiFinite]
  refine (SchemeLimitModel.relativePureFibreDimensionDescent
    0 I D S X Y t a b f w c hc p hp).trans ?_
  exact exists_congr fun i => by
    have : LocallyOfFiniteType (AffineLimit.baseChangeMap a b f w (t.app i)) :=
      hft (t.app i)
    exact hasPureDimensionFibers_zero_iff_locallyQuasiFinite _

private theorem structural_inf_descent
    (P Q : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    (hP : SchemeStructuralPropertyDescent P)
    (hQ : SchemeStructuralPropertyDescent Q) :
    SchemeStructuralPropertyDescent (P ⊓ Q) := by
  intro I _ _ D S X Y _ _ t a b f w _ _ _ _ _ _ c hc p hp
  constructor
  · intro h
    obtain ⟨i, hi⟩ := (hP D t a b f w c hc p hp).mp h.1
    obtain ⟨j, hj⟩ := (hQ D t a b f w c hc p hp).mp h.2
    obtain ⟨k, ki, kj, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    exact ⟨k,
      MorphismProperty.of_isPullback (morphismDiagram_cartesian a b f w D t ki).flip hi,
      MorphismProperty.of_isPullback (morphismDiagram_cartesian a b f w D t kj).flip hj⟩
  · rintro ⟨i, hi⟩
    exact MorphismProperty.of_isPullback
      (coneMorphism_cartesian a b f w D t c p hp i).flip hi

/-- The three properties are detected together at one stage of an affine limit. -/
theorem quasiFiniteFlatSurjective_structural_descent :
    SchemeStructuralPropertyDescent.{u} quasiFiniteFlatSurjectiveProperty :=
  structural_inf_descent _ _
    (structural_inf_descent _ _ quasiFinite_structural_descent flat_structural_descent)
    surjective_schemeStructuralPropertyDescent

open Langlands.AlgebraicGeometry.NoetherianApproximation
open P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC

private def propertyCoefficientStages (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] : FGIndex R A →o Subalgebra R A where
  toFun i := i.1
  monotone' _ _ h := h

private theorem propertyCoefficientStages_cover {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] (a : A) :
    ∃ i : FGIndex R A, a ∈ propertyCoefficientStages R A i := by
  classical
  refine ⟨⟨Algebra.adjoin R ↑({a} : Finset A), Subalgebra.fg_adjoin_finset _⟩, ?_⟩
  exact Algebra.subset_adjoin (by simp)

/-- Structural scheme descent specializes to the actual group base change
over finitely generated coefficient subalgebras. -/
theorem exists_fg_hom_property
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hP : SchemeStructuralPropertyDescent P)
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] [LocallyOfFinitePresentation H.X.hom]
    [QuasiCompact H.X.hom] [QuasiSeparated H.X.hom]
    (f : G ⟶ H) (hf : P ((baseChange (Spec.algebraMap R A)).map f).hom.hom.left) :
    ∃ (T : Subalgebra R A), T.FG ∧
      P ((baseChange (Spec.algebraMap R T)).map f).hom.hom.left := by
  let S := propertyCoefficientStages R A
  let D := SubalgebraStages.specDiagram S
  let t : D ⟶ (Functor.const _).obj (Spec (CommRingCat.of R)) :=
    { app i := SubalgebraStages.specHom S i.unop
      naturality := by
        intro i j r
        change SubalgebraStages.specTrans S r.unop.le ≫
          SubalgebraStages.specHom S j.unop =
          SubalgebraStages.specHom S i.unop ≫ 𝟙 _
        rw [Category.comp_id]
        exact SubalgebraStages.specTrans_specHom S r.unop.le }
  obtain ⟨hc⟩ := nonempty_isLimit_specCone S propertyCoefficientStages_cover
  have htop : P (AffineLimit.baseChangeMap G.X.hom H.X.hom f.hom.hom.left
      (Over.w f.hom.hom) (SubalgebraStages.specHomTop (A₀ := R) (A := A))) :=
    (P.arrow_mk_iso_iff
      (overPullbackSchemeArrowIso f.hom.hom (Spec.algebraMap R A))).mp hf
  obtain ⟨i, hi⟩ := (hP D t G.X.hom H.X.hom f.hom.hom.left (Over.w f.hom.hom)
    (SubalgebraStages.specCone S) hc (SubalgebraStages.specHomTop (A₀ := R) (A := A))
    (SubalgebraStages.specCone_π_app_specHom S)).mp htop
  exact ⟨i.unop.1, i.unop.2,
    (P.arrow_mk_iso_iff
      (overPullbackSchemeArrowIso f.hom.hom (Spec.algebraMap R i.unop.1))).mpr hi⟩

/-- The locally quasi-finite flat surjective map descends to finite coefficients
without any finiteness assumption on the map. -/
theorem exists_fg_hom_quasiFinite_flat_surjective
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] [LocallyOfFinitePresentation H.X.hom]
    [QuasiCompact H.X.hom] [QuasiSeparated H.X.hom]
    (f : G ⟶ H)
    (hf : quasiFiniteFlatSurjectiveProperty
      ((baseChange (Spec.algebraMap R A)).map f).hom.hom.left) :
    ∃ (T : Subalgebra R A), T.FG ∧
      quasiFiniteFlatSurjectiveProperty
        ((baseChange (Spec.algebraMap R T)).map f).hom.hom.left :=
  exists_fg_hom_property quasiFiniteFlatSurjectiveProperty
    quasiFiniteFlatSurjective_structural_descent R A f hf

end Langlands.GroupScheme.Descent.FiniteCoefficient

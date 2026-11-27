import Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof
import Langlands.AlgebraicGeometry.ClosedLocusFromAffineChartsProof
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Noetherian.Defs

/-! # Closed agreement after base change from a finite flat scheme -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AffineClosedFactorizationLocus

variable {S X Y T U : Scheme.{u}}

private def Agree (p : X ⟶ S) (f g : X ⟶ Y) (t : T ⟶ S) : Prop :=
  pullback.fst p t ≫ f = pullback.fst p t ≫ g

private lemma agree_comp_iff (p : X ⟶ S) (f g : X ⟶ Y) (t : T ⟶ S) (b : U ⟶ T) :
    Agree p f g (b ≫ t) ↔ Agree (pullback.snd p t) (pullback.fst p t ≫ f)
      (pullback.fst p t ≫ g) b := by
  unfold Agree
  rw [← cancel_epi (pullbackLeftPullbackSndIso p t b).hom]
  simp only [pullbackLeftPullbackSndIso_hom_fst_assoc]

private lemma agree_stable (p : X ⟶ S) (f g : X ⟶ Y) (t : T ⟶ S) (b : U ⟶ T)
    (ht : Agree p f g t) : Agree p f g (b ≫ t) := by
  rw [agree_comp_iff, Agree, ht]

private lemma agree_of_affineOpens (p : X ⟶ S) (f g : X ⟶ Y) (t : T ⟶ S)
    (h : ∀ V : S.affineOpens, Agree p f g ((t ⁻¹ᵁ (V : S.Opens)).ι ≫ t)) :
    Agree p f g t := by
  let 𝒰 : T.OpenCover := T.openCoverOfIsOpenCover
    (fun V : S.affineOpens ↦ t ⁻¹ᵁ (V : S.Opens))
    (t.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))
  unfold Agree
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ (pullback.snd p t)) _ _ fun V ↦ ?_
  let W : S.affineOpens := V
  change pullback.fst (pullback.snd p t) (t ⁻¹ᵁ (W : S.Opens)).ι ≫
      (pullback.fst p t ≫ f) = pullback.fst _ _ ≫ (pullback.fst p t ≫ g)
  exact (agree_comp_iff p f g t _).mp (h W)

private lemma affine_agree_locus {R : CommRingCat.{u}} [IsNoetherianRing R]
    (X Y : Over (Spec R)) [IsFinite X.hom] [Flat X.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y) : ∃ (Z : Scheme.{u}) (j : Z ⟶ Spec R), IsClosedImmersion j ∧
      ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec R),
        (∃ k : T ⟶ Z, k ≫ j = t) ↔ Agree X.hom f.left g.left t := by
  let I : Over (Spec R) := Over.mk (𝟙 _)
  let a := fst X I ≫ f
  let b := fst X I ≫ g
  let e := equalizer.ι a b
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have hcoords : HasFpqcProjectiveCoordinateModule X := by
    let φ : R ⟶ Γ(X.left, ⊤) := (Scheme.ΓSpecIso R).inv ≫ X.hom.appTop
    have hfin : φ.hom.Finite := X.hom.finite_appTop.comp
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2)
    have hflat : φ.hom.Flat := (RingHom.Flat.of_bijective
      (f := (Scheme.ΓSpecIso R).inv.hom)
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)).comp X.hom.flat_appTop
    have : Module.Finite R ((algΓ R).obj X).unop := hfin
    have : Module.Flat R ((algΓ R).obj X).unop := hflat
    have : Module.FinitePresentation R ((algΓ R).obj X).unop :=
      Module.finitePresentation_of_finite R _
    have : Module.Projective R ((algΓ R).obj X).unop := Module.Flat.projective_of_finitePresentation
    refine ⟨CommAlgCat.of R R, inferInstance, ?_⟩
    exact Module.Projective.of_equiv' (TensorProduct.lid R ((algΓ R).obj X).unop).symm
  obtain ⟨Z, j, hj, hZ⟩ := ClosedFactorizationLocusProof.closedFactorizationLocus
    R X inferInstance inferInstance hcoords I _ e inferInstance
  refine ⟨Z.left, j.left, hj, fun {T} t ↦ ?_⟩
  let t' : Over.mk t ⟶ I := Over.mkIdTerminal.from _
  have ht' : t'.left = t := by simpa [I] using t'.w
  have hfac := (over_factorization_iff j t').symm
  rw [ht'] at hfac
  refine hfac.trans ((hZ _ t').trans ?_)
  constructor
  · rintro ⟨q, hq⟩
    have h : (X ◁ t') ≫ a = (X ◁ t') ≫ b := by
      rw [← hq, Category.assoc, Category.assoc, equalizer.condition]
    simpa only [Agree, Over.comp_left, Over.fst_left, Over.mk_hom] using
      congrArg CommaMorphism.left (show fst X (Over.mk t) ≫ f = fst X (Over.mk t) ≫ g by
        simpa only [a, b, ← Category.assoc, whiskerLeft_fst] using h)
  · intro h
    have h' : fst X (Over.mk t) ≫ f = fst X (Over.mk t) ≫ g := Over.OverMorphism.ext h
    have h'' : (X ◁ t') ≫ a = (X ◁ t') ≫ b := by
      simpa only [a, b, ← Category.assoc, whiskerLeft_fst] using h'
    exact ⟨equalizer.lift (X ◁ t') h'', equalizer.lift_ι _ _⟩

/-- Agreement of two maps from a finite flat scheme into a separated scheme over
    the base is a closed condition on the entire changed source. -/
theorem exists_finiteFlat_agreement_locus [IsLocallyNoetherian S]
    (X Y : Over S) [IsFinite X.hom] [Flat X.hom] [IsSeparated Y.hom] (f g : X ⟶ Y) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ S), IsClosedImmersion j ∧
      ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S),
        (∃ k : T ⟶ Z, k ≫ j = t) ↔ pullback.fst X.hom t ≫ f.left = pullback.fst X.hom t ≫ g.left := by
  refine closedLocusFromAffineCharts S (fun {_} t ↦ Agree X.hom f.left g.left t)
    (fun {_ _} b t ↦ agree_stable X.hom f.left g.left t b)
    (fun {_} t ↦ agree_of_affineOpens X.hom f.left g.left t) fun U ↦ ?_
  let r := U.2.fromSpec
  let X' := (Over.pullback r).obj X
  let Y' := (Over.pullback r).obj Y
  let f' := (Over.pullback r).map f
  let g' := (Over.pullback r).map g
  have : IsFinite X'.hom := inferInstanceAs (IsFinite (pullback.snd X.hom r))
  have : Flat X'.hom := inferInstanceAs (Flat (pullback.snd X.hom r))
  have : IsSeparated Y'.hom := inferInstanceAs (IsSeparated (pullback.snd Y.hom r))
  have : IsNoetherianRing Γ(S, (U : S.Opens)) := IsLocallyNoetherian.component_noetherian U
  obtain ⟨Z, j, hj, hZ⟩ := affine_agree_locus X' Y' f' g'
  let := hj
  refine ⟨Z, j ≫ U.2.isoSpec.inv, inferInstance, fun {T} t ↦ ?_⟩
  have ht : (t ≫ U.2.isoSpec.hom) ≫ r = t ≫ (U : S.Opens).ι := by
    simp [r, U.2.isoSpec_hom_fromSpec]
  have hfac := factorization_comp_iso_iff j (t ≫ U.2.isoSpec.hom) U.2.isoSpec.symm
  simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] at hfac
  rw [hfac, hZ, ← ht, agree_comp_iff X.hom f.left g.left r (t ≫ U.2.isoSpec.hom)]
  unfold Agree
  constructor
  · intro h
    simpa only [Category.assoc, X', f', g', Over.pullback_obj_hom, Over.pullback_map_left,
      pullback.lift_fst]
      using congrArg (· ≫ pullback.fst Y.hom r) h
  · intro h
    apply pullback.hom_ext
    · simpa only [Category.assoc, X', f', g', Over.pullback_obj_hom, Over.pullback_map_left,
      pullback.lift_fst] using h
    · simp only [Category.assoc, f', g', Over.pullback_map_left, pullback.lift_snd]

end Langlands.AlgebraicGeometry

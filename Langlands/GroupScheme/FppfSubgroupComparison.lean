import Langlands.GroupScheme.Reductive.AffinePinnedComparisonDescent

/-! # Fppf locality of actual subgroup comparison squares -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {A B G H : GroupScheme S} {U : Over S}
  (i : A ⟶ G) (j : B ⟶ H) (e : G ≅ H)
  (t : LocalGroupIso A B U)

/-- An actual comparison square on the cover gives its pointwise square on
all relative tests and at every point of the cover. -/
theorem ofBaseChangeIso_subgroup_square
    (τ : (baseChange U.hom).obj A ≅ (baseChange U.hom).obj B)
    (hτ : (baseChange U.hom).map i ≫ (baseChange U.hom).map e.hom =
      τ.hom ≫ (baseChange U.hom).map j)
    {Z : Over S} (a : Z ⟶ U) (x : Z ⟶ A.X) :
    (ofBaseChangeIso τ).toFun a x ≫ j.hom.hom =
      x ≫ i.hom.hom ≫ e.hom.hom.hom := by
  change coverPointsEquiv B a
      ((coverPointsEquiv A a).symm x ≫ τ.hom.hom.hom) ≫ j.hom.hom = _
  rw [← coverPointsEquiv_comp, Category.assoc]
  change coverPointsEquiv H a
      ((coverPointsEquiv A a).symm x ≫ (τ.hom ≫ (baseChange U.hom).map j).hom.hom) = _
  rw [← hτ]
  change coverPointsEquiv H a
      (((coverPointsEquiv A a).symm x ≫ ((baseChange U.hom).map i).hom.hom) ≫
        ((baseChange U.hom).map e.hom).hom.hom) = _
  rw [coverPointsEquiv_comp, coverPointsEquiv_comp, MulEquiv.apply_symm_apply]
  exact Category.assoc _ _ _

variable [Mono j.hom.hom]
  (ht : ∀ {Z : Over S} (a : Z ⟶ U) (x : Z ⟶ A.X),
    t.toFun a x ≫ j.hom.hom = x ≫ i.hom.hom ≫ e.hom.hom.hom)

include ht in
/-- A comparison square into a monomorphism forces the local family to be
independent of the cover point. -/
theorem isIndependent_of_square : t.IsIndependent := by
  intro Z a b x
  change t.toFun a x = t.toFun b x
  apply (cancel_mono j.hom.hom).mp
  rw [ht, ht]

variable [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom]

/-- Descend a local subgroup comparison whose ambient square is global. -/
def descendOfSquare : A ≅ B :=
  t.descendFppf (isIndependent_of_square i j e t ht)

include ht in
/-- The descended subgroup isomorphism has the original ambient square. -/
theorem descendOfSquare_square :
    i ≫ e.hom = (descendOfSquare i j e t ht).hom ≫ j := by
  apply hom_ext_points
  intro Z x
  let he : t.IsIndependent := isIndependent_of_square i j e t ht
  change x ≫ i.hom.hom ≫ e.hom.hom.hom =
    x ≫ (t.toLocalGroupHom.descendFppf he).hom.hom ≫ j.hom.hom
  rw [← Category.assoc x (t.toLocalGroupHom.descendFppf he).hom.hom j.hom.hom,
    LocalGroupHom.comp_descendFppf]
  apply Over.OverMorphism.ext
  have : Epi (fst Z U).left := by
    change Epi (CategoryTheory.Limits.pullback.fst Z.hom U.hom)
    infer_instance
  apply (cancel_epi (fst Z U).left).mp
  have hv := t.toLocalGroupHom.valueFppf_fac he x
  change fst Z U ≫ t.toLocalGroupHom.valueFppf he x =
    t.toFun (snd Z U) (fst Z U ≫ x) at hv
  have hs := ht (snd Z U) (fst Z U ≫ x)
  have h : fst Z U ≫ (t.toLocalGroupHom.valueFppf he x ≫ j.hom.hom) =
      fst Z U ≫ (x ≫ i.hom.hom ≫ e.hom.hom.hom) := by
    rw [← Category.assoc, hv, hs]
    simp only [Category.assoc]
  exact (congrArg (fun k => k.left) h).symm

/-- A subgroup isomorphism with the stated square is unique, because the target
inclusion is a monomorphism. -/
theorem iso_unique_of_square (τ σ : A ≅ B)
    (hτ : i ≫ e.hom = τ.hom ≫ j) (hσ : i ≫ e.hom = σ.hom ≫ j) : τ = σ := by
  apply Iso.ext
  apply Grp.hom_ext
  exact (cancel_mono j.hom.hom).mp (congrArg (fun k => k.hom.hom) (hτ.symm.trans hσ))

/-- An actual subgroup comparison square exists globally as soon as it exists
on one arbitrary fppf cover. No pinning or constant lattice map is required. -/
theorem existsUnique_iso_of_baseChange_square
    (τ : (baseChange U.hom).obj A ≅ (baseChange U.hom).obj B)
    (hτ : (baseChange U.hom).map i ≫ (baseChange U.hom).map e.hom =
      τ.hom ≫ (baseChange U.hom).map j) :
    ∃! σ : A ≅ B, i ≫ e.hom = σ.hom ≫ j := by
  let t := ofBaseChangeIso τ
  have ht : ∀ {Z : Over S} (a : Z ⟶ U) (x : Z ⟶ A.X),
      t.toFun a x ≫ j.hom.hom = x ≫ i.hom.hom ≫ e.hom.hom.hom :=
    ofBaseChangeIso_subgroup_square i j e τ hτ
  refine ⟨descendOfSquare i j e t ht, descendOfSquare_square i j e t ht, ?_⟩
  intro σ hσ
  exact iso_unique_of_square i j e σ _ hσ (descendOfSquare_square i j e t ht)

end Langlands.GroupScheme.LocalGroupIso

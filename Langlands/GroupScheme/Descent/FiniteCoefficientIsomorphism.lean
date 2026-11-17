import Langlands.GroupScheme.Descent.FiniteCoefficientHomGeneral
import Langlands.GroupScheme.Descent.FiniteCoefficientHomProperties
import Langlands.AlgebraicGeometry.AffineLimitIsomorphismDescent
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Torus.DiagonalizableFppfQuotient

/-! # Isomorphisms of affine groups over finite coefficients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

open Langlands.AlgebraicGeometry
open AffineLimit SchemeLimitModel.Geometry
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.NoetherianApproximation
open P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC

private def isoCoefficientStages (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] : FGIndex R A →o Subalgebra R A where
  toFun i := i.1
  monotone' _ _ h := h

private theorem isoCoefficientStages_cover {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] (a : A) :
    ∃ i : FGIndex R A, a ∈ isoCoefficientStages R A i := by
  classical
  refine ⟨⟨Algebra.adjoin R ↑({a} : Finset A), Subalgebra.fg_adjoin_finset _⟩, ?_⟩
  exact Algebra.subset_adjoin (by simp)

/-- A specified map of affine finitely presented schemes that is an
isomorphism over an algebra is an isomorphism at some finite coefficient stage. -/
theorem exists_fg_isIso {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X Y : Over (Spec (CommRingCat.of R))}
    [IsAffine X.left] [IsAffine Y.left]
    [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom]
    (f : X ⟶ Y) [IsIso ((Over.pullback (Spec.algebraMap R A)).map f).left] :
    ∃ (T : Subalgebra R A), T.FG ∧
      IsIso ((Over.pullback (Spec.algebraMap R T)).map f).left := by
  let S := isoCoefficientStages R A
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
  obtain ⟨hc⟩ := nonempty_isLimit_specCone S isoCoefficientStages_cover
  let P : MorphismProperty Scheme.{u} := @IsIso Scheme.{u} _
  have htop : P (AffineLimit.baseChangeMap X.hom Y.hom f.left f.w
      (SubalgebraStages.specHomTop (A₀ := R) (A := A))) :=
    (P.arrow_mk_iso_iff
      (overPullbackSchemeArrowIso f (Spec.algebraMap R A))).mp inferInstance
  have : IsIso (AffineLimit.baseChangeMap X.hom Y.hom f.left f.w
      (SubalgebraStages.specHomTop (A₀ := R) (A := A))) := htop
  obtain ⟨i, hi⟩ := exists_isIso_baseChangeMap D t X.hom Y.hom f.left f.w
    (SubalgebraStages.specCone S) hc
    (SubalgebraStages.specHomTop (A₀ := R) (A := A))
    (SubalgebraStages.specCone_π_app_specHom S)
  exact ⟨i.unop.1, i.unop.2,
    (P.arrow_mk_iso_iff
      (overPullbackSchemeArrowIso f (Spec.algebraMap R i.unop.1))).mpr hi⟩

private theorem iso_fg_tower {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (T : Subalgebra R A) (U : Subalgebra T A) (hT : T.FG) (hU : U.FG) :
    (U.restrictScalars R).FG := by
  have h₁ : Algebra.FiniteType R T := (Subalgebra.fg_iff_finiteType _).mp hT
  have h₂ : Algebra.FiniteType T U := (Subalgebra.fg_iff_finiteType _).mp hU
  have h₃ : Algebra.FiniteType R U := Algebra.FiniteType.trans h₁ h₂
  exact (Subalgebra.fg_iff_finiteType (U.restrictScalars R)).mpr h₃

private theorem iso_spec_comp (R B A : Type u) [CommRing R] [CommRing B]
    [CommRing A] [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A] :
    Spec.algebraMap B A ≫ Spec.algebraMap R B = Spec.algebraMap R A := by
  rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (G H : GroupScheme (Spec (CommRingCat.of R)))

/-- A finite coefficient stage on which two already defined groups are isomorphic. -/
structure IsomorphismModel where
  coefficients : Subalgebra R A
  finite : coefficients.FG
  iso : (baseChange (Spec.algebraMap R coefficients)).obj G ≅
    (baseChange (Spec.algebraMap R coefficients)).obj H

/-- Isomorphism of two affine finitely presented groups over an algebra
already holds over finite coefficients containing any prescribed finite subset. -/
theorem exists_isomorphismModel
    [IsAffine G.X.left] [LocallyOfFinitePresentation G.X.hom]
    [IsAffine H.X.left] [LocallyOfFinitePresentation H.X.hom]
    (e : (baseChange (Spec.algebraMap R A)).obj G ≅
      (baseChange (Spec.algebraMap R A)).obj H) (s : Finset A) :
    ∃ D : IsomorphismModel R A G H, (s : Set A) ⊆ D.coefficients := by
  obtain ⟨T, hT, hs, g, hg⟩ := homGeneral R A G H e.hom s
  let G₀ := (baseChange (Spec.algebraMap R T)).obj G
  let H₀ := (baseChange (Spec.algebraMap R T)).obj H
  let cG := pullbackComparison (Spec.algebraMap R T) (Spec.algebraMap T A)
    (Spec.algebraMap R A) (iso_spec_comp R T A) G
  let cH := pullbackComparison (Spec.algebraMap R T) (Spec.algebraMap T A)
    (Spec.algebraMap R A) (iso_spec_comp R T A) H
  have he : (baseChange (Spec.algebraMap T A)).map g =
      cG.hom ≫ e.hom ≫ cH.inv := by
    apply (cancel_mono cH.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hg
  have : IsIso ((baseChange (Spec.algebraMap T A)).map g) := by
    rw [he]
    infer_instance
  have : IsIso ((Over.pullback (Spec.algebraMap T A)).map g.hom.hom).left :=
    (Over.forget _).map_isIso ((Grp.forget _).map
      ((baseChange (Spec.algebraMap T A)).map g))
  have : IsAffine G₀.X.left := by
    change IsAffine (pullback G.X.hom (Spec.algebraMap R T))
    infer_instance
  have : IsAffine H₀.X.left := by
    change IsAffine (pullback H.X.hom (Spec.algebraMap R T))
    infer_instance
  have : LocallyOfFinitePresentation G₀.X.hom := by
    change LocallyOfFinitePresentation (pullback.snd G.X.hom (Spec.algebraMap R T))
    infer_instance
  have : LocallyOfFinitePresentation H₀.X.hom := by
    change LocallyOfFinitePresentation (pullback.snd H.X.hom (Spec.algebraMap R T))
    infer_instance
  obtain ⟨U, hU, hUiso⟩ := exists_fg_isIso (A := A) g.hom.hom
  let v := (baseChange (Spec.algebraMap T U)).map g
  have : IsIso v.hom.hom.left := hUiso
  let eo : ((baseChange (Spec.algebraMap T U)).obj G₀).X ≅
      ((baseChange (Spec.algebraMap T U)).obj H₀).X :=
    Over.isoMk (asIso v.hom.hom.left) (Over.w v.hom.hom)
  have : IsMonHom eo.hom := by
    change IsMonHom v.hom.hom
    infer_instance
  let ev : (baseChange (Spec.algebraMap T U)).obj G₀ ≅
      (baseChange (Spec.algebraMap T U)).obj H₀ :=
    Grp.mkIso' eo
  let eG := pullbackComparison (Spec.algebraMap R T) (Spec.algebraMap T U)
    (Spec.algebraMap R U) (iso_spec_comp R T U) G
  let eH := pullbackComparison (Spec.algebraMap R T) (Spec.algebraMap T U)
    (Spec.algebraMap R U) (iso_spec_comp R T U) H
  refine ⟨{
    coefficients := U.restrictScalars R
    finite := iso_fg_tower T U hT hU
    iso := eG.symm ≪≫ ev ≪≫ eH }, ?_⟩
  intro x hx
  exact U.algebraMap_mem ⟨x, hs hx⟩

/-- Choose a finite coefficient stage on which the groups are isomorphic. -/
def isomorphismModel
    [IsAffine G.X.left] [LocallyOfFinitePresentation G.X.hom]
    [IsAffine H.X.left] [LocallyOfFinitePresentation H.X.hom]
    (e : (baseChange (Spec.algebraMap R A)).obj G ≅
      (baseChange (Spec.algebraMap R A)).obj H) : IsomorphismModel R A G H :=
  Classical.choose (exists_isomorphismModel R A G H e ∅)

variable {H}

/-- A diagonalizable model with a fixed finitely generated full character
group over an algebra is already available at some finite coefficient stage. -/
theorem exists_fg_isDiagonalizable
    [IsAffine G.X.left] [LocallyOfFinitePresentation G.X.hom]
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (e : (baseChange (Spec.algebraMap R A)).obj G ≅
      (Diagonalizable.groupScheme (CommRingCat.of A) Λ).toGrp) (s : Finset A) :
    ∃ (T : Subalgebra R A), T.FG ∧ (s : Set A) ⊆ T ∧
      RelativeMultiplicativeType.IsDiagonalizable
        ((baseChange (Spec.algebraMap R T)).obj G) := by
  let D := (Diagonalizable.groupScheme (CommRingCat.of R) Λ).toGrp
  have : IsAffineHom D.X.hom := inferInstanceAs
    (IsAffineHom (Diagonalizable.groupScheme (CommRingCat.of R) Λ).X.hom)
  have : IsAffine D.X.left := isAffine_of_isAffineHom D.X.hom
  have : LocallyOfFinitePresentation D.X.hom :=
    Diagonalizable.locallyOfFinitePresentation (CommRingCat.of R) Λ
  obtain ⟨M, hs⟩ := exists_isomorphismModel R A G D
    (e ≪≫ (Diagonalizable.baseChangeIso (Spec.algebraMap R A) Λ).symm) s
  refine ⟨M.coefficients, M.finite, hs, ?_⟩
  exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
    (M.iso ≪≫ Diagonalizable.baseChangeIso (Spec.algebraMap R M.coefficients) Λ)
    (Diagonalizable.isDiagonalizable_groupScheme (CommRingCat.of M.coefficients) Λ)

end Langlands.GroupScheme.Descent.FiniteCoefficient

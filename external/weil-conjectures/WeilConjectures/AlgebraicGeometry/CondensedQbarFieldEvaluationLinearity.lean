/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation

import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare

/-! # Compatibility of bounded coefficient constructions
Source: RefactorInstruction, Section 4, coefficient realization and geometric fibers.
-/

@[expose] public section

universe u v v' w w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private noncomputable abbrev ev (K : Type u) [Field K] [IsAlgClosed K] :=
  sheafToPresheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1} ⋙
    (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))

private theorem comparison_tensor (K K' : Type u)
    [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K'] (i : K →+* K')
    (P Q : Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1}) :
    let f := Spec.map (CommRingCat.ofHom i)
    let H := upperStar Ab.{u + 1} f
    let τ := geometricFieldEvaluationComparison f Ab.{u + 1}
    Functor.LaxMonoidal.μ (ev K) P Q ≫ τ.app (P ⊗ Q) =
      (τ.app P ⊗ₘ τ.app Q) ≫ Functor.LaxMonoidal.μ (H ⋙ ev K') P Q := by
  dsimp only
  let f := Spec.map (CommRingCat.ofHom i)
  let H := upperStar Ab.{u + 1} f
  let L := lowerStar Ab.{u + 1} f
  let T := op (Scheme.ProEt.mk (𝟙 (Spec (.of K))))
  let T' := op (Scheme.ProEt.mk (𝟙 (Spec (.of K'))))
  let q : (Scheme.proEtaleBaseChange f).obj (Scheme.ProEt.mk (𝟙 (Spec (.of K)))) ≅
      Scheme.ProEt.mk (𝟙 (Spec (.of K'))) := MorphismProperty.Over.isoMk
    (asIso (pullback.snd (𝟙 (Spec (.of K))) f)) (Category.comp_id _)
  let s := q.inv.op
  let η := (upperStarLowerStarAdjunction Ab.{u + 1} f).unit
  have h := NatTrans.IsMonoidal.tensor (τ := Functor.whiskerRight η (ev K)) P Q
  have hL := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (Scheme.proEtaleBaseChange f) Ab.{u + 1}
      (Scheme.ProEt.topology (Spec (.of K)))
      (Scheme.ProEt.topology (Spec (.of K'))) (H.obj P) (H.obj Q) T
  simp only [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.id_μ] at h
  change Functor.LaxMonoidal.μ (ev K) P Q ≫ (η.app (P ⊗ Q)).hom.app T =
    ((η.app P).hom.app T ⊗ₘ (η.app Q).hom.app T) ≫
      (Functor.LaxMonoidal.μ (sheafToPresheaf _ Ab) (L.obj (H.obj P))
        (L.obj (H.obj Q))).app T ≫
      (Functor.LaxMonoidal.μ L (H.obj P) (H.obj Q)).hom.app T ≫
      (Functor.LaxMonoidal.μ H P Q).hom.app ((Scheme.proEtaleBaseChange f).op.obj T) at h
  erw [reassoc_of% hL] at h
  change (Functor.LaxMonoidal.μ (ev K) P Q ≫
    (η.app (P ⊗ Q)).hom.app T) ≫ ((H.obj (P ⊗ Q)).obj.map s) = _
  rw [h]
  have hn := (Functor.LaxMonoidal.μ H P Q).hom.naturality s
  have hm := (Functor.LaxMonoidal.μ (sheafToPresheaf _ Ab) (H.obj P)
    (H.obj Q)).naturality s
  simp only [Category.assoc] at *
  erw [← hn, ← reassoc_of% hm]
  change _ = (((η.app P).hom.app T ≫ (H.obj P).obj.map s) ⊗ₘ
    ((η.app Q).hom.app T ≫ (H.obj Q).obj.map s)) ≫ _
  rw [← tensorHom_comp_tensorHom, Category.assoc]
  rfl

private theorem comparison_action (ℓ : ℕ) [Fact ℓ.Prime]
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K')
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K)))) :
    let f := Spec.map (CommRingCat.ofHom i)
    let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))
    let H := upperStar Ab.{u + 1} f
    let τ := geometricFieldEvaluationComparison f Ab.{u + 1}
    Functor.LaxMonoidal.μ (ev K) A M.X ≫ (ev K).map (Mod.act M.X) ≫ τ.app M.X =
      (τ.app A ⊗ₘ τ.app M.X) ≫ Functor.LaxMonoidal.μ (H ⋙ ev K') A M.X ≫
        (H ⋙ ev K').map (Mod.act M.X) := by
  dsimp only
  let τ : ev K ⟶ upperStar Ab (Spec.map (CommRingCat.ofHom i)) ⋙ ev K' :=
    geometricFieldEvaluationComparison _ Ab
  rw [show (ev K).map (Mod.act M.X) ≫ τ.app M.X =
    τ.app (_ ⊗ M.X) ≫ (upperStar Ab (Spec.map (CommRingCat.ofHom i)) ⋙ ev K').map
      (Mod.act M.X) from τ.naturality (Mod.act M.X)]
  rw [← Category.assoc, comparison_tensor]
  simp only [Category.assoc]

private theorem fieldFiber_smul (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type u) [Field K] [IsAlgClosed K]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))))
    (r : PadicAlgCl ℓ) (m : (ev K).obj M.X) :
    (((CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj M).smul r).asHom.hom m =
      (Mod.act ((ev K).mapMod _ |>.obj M).X)
        ((inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom)
          (ULift.up r) ⊗ₜ[ℤ] m) := by
  change ((inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom) ▷ _ ≫
    Mod.act ((ev K).mapMod _ |>.obj M).X) (ULift.up r ⊗ₜ[ℤ] m) = _
  rw [AddCommGrpCat.comp_apply,
    AddCommGrpCat.MonoidalCategory.whiskerRight_tmul]

private theorem comap_map_action
    {C : Type v} [Category.{v'} C] [MonoidalCategory C]
    {D : Type w} [Category.{w'} D] [MonoidalCategory D]
    (H : C ⥤ D) [H.LaxMonoidal] (F : D ⥤ Ab.{u + 1}) [F.LaxMonoidal]
    (A : C) [MonObj A] (B : D) [MonObj B]
    (α : B ⟶ H.obj A) [IsMonHom α] (M : Mod C A)
    (r : F.obj B) (m : F.obj (H.obj M.X)) :
    (Mod.act ((F.mapMod B).obj ((Mod.comap α).obj ((H.mapMod A).obj M))).X).hom
        (r ⊗ₜ[ℤ] m) =
      (Functor.LaxMonoidal.μ (H ⋙ F) A M.X ≫
        (H ⋙ F).map (Mod.act M.X)).hom ((F.map α).hom r ⊗ₜ[ℤ] m) := by
  change (Functor.LaxMonoidal.μ F _ _ ≫
    F.map (α ▷ H.obj M.X ≫ Functor.LaxMonoidal.μ H A M.X ≫
      H.map (Mod.act M.X))).hom _ = _
  rw [Functor.map_comp, ← Category.assoc, ← Functor.LaxMonoidal.μ_natural_left]
  simp only [Category.assoc]
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.MonoidalCategory.whiskerRight_tmul]
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_map, Functor.map_comp,
    Category.assoc]
  rfl

private theorem pullbackFiber_smul_aux (ℓ : ℕ) [Fact ℓ.Prime]
    (K' : Type u) [Field K'] [IsAlgClosed K']
    {C : Type v} [Category.{v'} C] [MonoidalCategory C]
    (H : C ⥤ Sheaf (Scheme.ProEt.topology (Spec (.of K'))) Ab.{u + 1})
    [H.LaxMonoidal] (A : C) [MonObj A]
    (α : H.obj A ⟶ condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K')))
    [IsIso α] [IsMonHom α] (M : Mod C A)
    (r : PadicAlgCl ℓ) (m : (ev K').obj (H.obj M.X)) :
    let N := (CondensedQbarGeometricEvaluation.fieldFiber K' ℓ).obj
      ((Mod.comap (inv α)).obj ((H.mapMod A).obj M))
    (N.smul r).asHom.hom m =
      (Functor.LaxMonoidal.μ (H ⋙ ev K') A M.X ≫
        (H ⋙ ev K').map (Mod.act M.X)).hom
          (((ev K').map (inv α))
            ((inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K' ℓ).hom.hom)
              (ULift.up r)) ⊗ₜ[ℤ] m) := by
  dsimp only
  let M' := (Mod.comap (inv α)).obj ((H.mapMod A).obj M)
  have hs := fieldFiber_smul ℓ K' M' r m
  refine hs.trans ?_
  exact comap_map_action H (ev K') A
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K')))
    (inv α) M _ m

private theorem pullbackFiber_smul (ℓ : ℕ) [Fact ℓ.Prime]
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K')
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))))
    (r : PadicAlgCl ℓ)
    (m : (ev K').obj ((upperStar Ab (Spec.map (CommRingCat.ofHom i))).obj M.X)) :
    let f := Spec.map (CommRingCat.ofHom i)
    let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))
    let H := upperStar Ab.{u + 1} f
    let α := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f
    let N := (CondensedQbarGeometricEvaluation.fieldFiber K' ℓ).obj
      ((Mod.comap (inv α)).obj ((H.mapMod A).obj M))
    (N.smul r).asHom.hom m =
      (Functor.LaxMonoidal.μ (H ⋙ ev K') A M.X ≫
        (H ⋙ ev K').map (Mod.act M.X)).hom
          (((ev K').map (inv α))
            ((inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K' ℓ).hom.hom)
              (ULift.up r)) ⊗ₜ[ℤ] m) := by
  dsimp only
  exact pullbackFiber_smul_aux ℓ K' (upperStar Ab (Spec.map (CommRingCat.ofHom i)))
    _ (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ)
      (Spec.map (CommRingCat.ofHom i))) M r m
set_option backward.isDefEq.respectTransparency false in

private theorem main_of_coeff (ℓ : ℕ) [Fact ℓ.Prime]
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K')
    (hc :
      inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom ≫
        (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i)) Ab).app
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))) =
      inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K' ℓ).hom.hom ≫
        (ev K').map (inv (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ)
          (Spec.map (CommRingCat.ofHom i)))))
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))))
    (r : PadicAlgCl ℓ) :
    let f := Spec.map (CommRingCat.ofHom i)
    let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))
    let H := upperStar Ab.{u + 1} f
    let α := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f
    let N := (CondensedQbarGeometricEvaluation.fieldFiber K' ℓ).obj
      ((Mod.comap (inv α)).obj ((H.mapMod A).obj M))
    (geometricFieldEvaluationComparison f Ab).app M.X ≫ (N.smul r).asHom =
      (((CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj M).smul r).asHom ≫
        (geometricFieldEvaluationComparison f Ab).app M.X := by
  dsimp only
  apply AddCommGrpCat.ext
  intro m
  simp only [AddCommGrpCat.comp_apply]
  change (((CondensedQbarGeometricEvaluation.fieldFiber K' ℓ).obj
    ((Mod.comap (inv (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ)
      (Spec.map (CommRingCat.ofHom i))))).obj
        (((upperStar Ab (Spec.map (CommRingCat.ofHom i))).mapMod _).obj M))).smul r).asHom.hom
      (((geometricFieldEvaluationComparison _ Ab).app M.X).hom m) =
    ((geometricFieldEvaluationComparison _ Ab).app M.X).hom
      ((((CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj M).smul r).asHom.hom m)
  rw [pullbackFiber_smul ℓ K K' i M r _, fieldFiber_smul ℓ K M r m]
  let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))
  let H := upperStar Ab (Spec.map (CommRingCat.ofHom i))
  let τ : ev K ⟶ H ⋙ ev K' := geometricFieldEvaluationComparison _ Ab
  let a := (inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom)
    (ULift.up r)
  let b := ((ev K').map (inv (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ)
    (Spec.map (CommRingCat.ofHom i)))))
      ((inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K' ℓ).hom.hom)
        (ULift.up r))
  have ha : (τ.app A).hom a = b := congrArg (fun k ↦ k.hom (ULift.up r)) hc
  have hh : (τ.app M.X).hom
      ((Functor.LaxMonoidal.μ (ev K) A M.X ≫ (ev K).map (Mod.act M.X)).hom
        (a ⊗ₜ[ℤ] m)) =
    (Functor.LaxMonoidal.μ (H ⋙ ev K') A M.X ≫ (H ⋙ ev K').map (Mod.act M.X)).hom
      ((τ.app A).hom a ⊗ₜ[ℤ] (τ.app M.X).hom m) :=
    congrArg (fun k ↦ k.hom (a ⊗ₜ[ℤ] m)) (comparison_action ℓ K K' i M)
  rw [ha] at hh
  exact hh.symm

/-- The specified abelian comparison preserves the scalar action on every module.

Source: Bhatt--Scholze, Example 4.1.10; RefactorInstruction, Section 4,
geometric-fiber comparison, steps 1--3
(auxiliary; not a blueprint node).

Proof in words: the comparison is the inverse-image adjunction unit followed by
restriction along the canonical terminal-object comparison. Both respect the lax
monoidal maps: use monoidality of the adjunction unit, then naturality of the
restriction map for the tensor action and tensor unit. Apply this identity to the
internal action A tensor M -> M. It identifies the evaluated source action with
the evaluated inverse-image action, with coefficient transported by the evaluation
comparison on A and by condensedPullbackHom. To identify this coefficient map in
the fixed Qbar_l coordinates, precompose with the invertible globalCoefficientIso
and the bounded-presheaf unit at the terminal object. A bounded function on Spec(K)
is constant, and its pullback to Spec(K') has the same value. The normalized
profinite-test formula globalCoefficientIso_test identifies both comparisons;
fieldUnitIso cancels the units, and boundedPointIso evaluates the same constant.
The resulting coefficient square commutes since all precomposed maps are
surjective. Restriction along inv(condensedPullbackHom) cancels that coefficient
map, so the ordinary module action and ULift restriction give the stated scalar
identity, for every module and every scalar. Identity embeddings, zero modules,
and transcendental extensions satisfy the same argument; no algebraicity is used.
-/
theorem condensedQbar_field_evaluation_linear (ℓ : ℕ) [Fact ℓ.Prime]
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K')
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))))
    (r : PadicAlgCl ℓ) :
    let f := Spec.map (CommRingCat.ofHom i)
    let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))
    let H := upperStar Ab.{u + 1} f
    let α := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f
    let N := ((H.mapMod A ⋙ Mod.comap (inv α)) ⋙
      CondensedQbarGeometricEvaluation.fieldFiber K' ℓ).obj M
    (geometricFieldEvaluationComparison f Ab).app M.X ≫ (N.smul r).asHom =
      (((CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj M).smul r).asHom ≫
        (geometricFieldEvaluationComparison f Ab).app M.X := by
  exact main_of_coeff ℓ K K' i (condensedQbar_field_coefficient_square ℓ K K' i) M r

end AlgebraicGeometry.ProEtale

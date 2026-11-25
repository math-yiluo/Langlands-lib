/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonAffineCech
import WeilConjectures.CategoryTheory.ModuleCechCriterion
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine

/-! # Affine sections of the intrinsic comparison of an injective

Source: Stacks Project, Tags 099U and 099V, affine vanishing in the proof of
comparison; blueprint lemma-acyclicity-pulled-back-injectives, first two paragraphs.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

private theorem cech_objects_mem {C : Type*} [Category* C]
    (B : ObjectProperty C) [B.IsClosedUnderLimitsOfShape WalkingCospan]
    {T : Type*} {U : C} {V : T → C} {f : ∀ t, V t ⟶ U}
    (S : SiteCechComplex V f) (hU : B U) (hV : ∀ t, B (V t))
    (p : ℕ) (a : Fin (p + 1) → T) : B (S.W p a) := by
  induction p with
  | zero => simpa only [S.W_zero] using hV (a 0)
  | succ p ih =>
    let b : Fin (p + 1) → T := a ∘ Fin.succ
    let t := S.indexMap a Fin.succ
    have ht (k : Fin (p + 1)) : t ≫ S.pr p b k = S.pr (p + 1) a k.succ :=
      S.indexMap_pr a Fin.succ k
    let g := S.pr p b 0 ≫ f (b 0)
    have hw : S.pr (p + 1) a 0 ≫ f (a 0) = t ≫ g := by
      dsimp only [g]
      rw [← Category.assoc, ht]
      exact (S.comm (p + 1) a (Fin.succ 0)).symm
    let c := PullbackCone.mk (S.pr (p + 1) a 0) t hw
    have hext {n : ℕ} {a : Fin (n + 1) → T} {Z : C}
        (r s : Z ⟶ S.W n a) (h : ∀ k, r ≫ S.pr n a k = s ≫ S.pr n a k) :
        r = s := by
      have hs (k) : (s ≫ S.pr n a k) ≫ f (a k) =
          (s ≫ S.pr n a 0) ≫ f (a 0) := by
        simp only [Category.assoc, S.comm]
      obtain ⟨l, _, hl⟩ := S.universal n a Z (fun k ↦ s ≫ S.pr n a k) hs
      exact (hl r h).trans (hl s (fun _ ↦ rfl)).symm
    let arrows (z : PullbackCone (f (a 0)) g) :
        ∀ k : Fin (p + 1 + 1), z.pt ⟶ V (a k) :=
      Fin.cases z.fst (fun k ↦ z.snd ≫ S.pr p b k)
    have comm (z : PullbackCone (f (a 0)) g) (k : Fin (p + 1 + 1)) :
        arrows z k ≫ f (a k) = arrows z 0 ≫ f (a 0) := by
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · rfl
      · change (z.snd ≫ S.pr p b k) ≫ f (b k) = z.fst ≫ f (a 0)
        rw [Category.assoc, S.comm p b k]
        exact z.condition.symm
    let lift (z : PullbackCone (f (a 0)) g) :=
      (S.universal (p + 1) a z.pt (arrows z) (comm z)).choose
    have hl (z : PullbackCone (f (a 0)) g) (k) :
        lift z ≫ S.pr (p + 1) a k = arrows z k :=
      (S.universal (p + 1) a z.pt (arrows z) (comm z)).choose_spec.1 k
    have hc : IsLimit c := by
      refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
      · intro z
        exact hl z 0
      · intro z
        apply hext
        intro k
        rw [Category.assoc, ht]
        simpa only [arrows, Fin.cases_succ] using hl z k.succ
      · intro z m hm₁ hm₂
        apply hext
        intro k
        refine Fin.cases ?_ (fun k ↦ ?_) k
        · exact hm₁.trans (hl z 0).symm
        · calc
            m ≫ S.pr (p + 1) a k.succ = (m ≫ t) ≫ S.pr p b k := by
              rw [Category.assoc, ht]
            _ = z.snd ≫ S.pr p b k := by rw [hm₂]
            _ = arrows z k.succ := rfl
            _ = lift z ≫ S.pr (p + 1) a k.succ := (hl z k.succ).symm
    apply B.prop_of_isLimit hc
    intro j
    cases j with
    | none => exact hU
    | some j => cases j with
      | left => exact hV (a 0)
      | right => exact ih b

private theorem module_cech_vanishing {C : Type w} [SmallCategory C] [HasPullbacks C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] (K : GrothendieckTopology C)
    (hK : J.toGrothendieck = K) (R : Sheaf K RingCat.{w})
    [EnoughInjectives (SheafOfModules.{w} R)] (B : Set C)
    (hbasis : ∀ U : C, ∃ (T : Type w) (V : T → C) (f : ∀ t, V t ⟶ U),
      Presieve.ofArrows V f ∈ J U ∧ ∀ t, V t ∈ B)
    (hproducts : ∀ (U : C) (T : Type w) (V : T → C) (f : ∀ t, V t ⟶ U),
      U ∈ B → (∀ t, V t ∈ B) → ∀ (S : SiteCechComplex V f)
      (p : ℕ) (a : Fin (p + 1) → T), S.W p a ∈ B)
    (hrefine : ∀ (U : C), U ∈ B →
      ∀ (T : Type w) (V : T → C) (f : ∀ t, V t ⟶ U),
      Presieve.ofArrows V f ∈ J U →
      ∃ (m : ℕ) (W : Fin m → C) (g : ∀ a, W a ⟶ U),
        (∀ a, W a ∈ B) ∧ Presieve.ofArrows W g ∈ J U ∧
          ∀ a, ∃ (t : T) (k : W a ⟶ V t), k ≫ f t = g a)
    (M : SheafOfModules.{w} R)
    (hM : ∀ (U : C) (m : ℕ) (V : Fin m → C) (f : ∀ a, V a ⟶ U),
      U ∈ B → (∀ a, V a ∈ B) → Presieve.ofArrows V f ∈ J U →
      ∀ (S : SiteCechComplex V f) (p : ℕ), 0 < p →
        IsZero ((S.cohomologyFunctor p).obj M.val.presheaf))
    (U : C) (hU : U ∈ B) (q : ℕ) :
    IsZero (((SheafOfModules.toSheaf R ⋙ sheafToPresheaf K AddCommGrpCat.{w} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)).rightDerived (q + 1)).obj M) := by
  classical
  subst K
  let products := fun (U : C) (T : Type w) (V : T → C) (f : ∀ t, V t ⟶ U)
    (_hU : U ∈ B) (_hV : ∀ t, V t ∈ B) (hc : Presieve.ofArrows V f ∈ J U) ↦
      (SiteCechComplex.exists_of_covering J hc).some
  have hp := fun U T V f hU hV hc p a ↦
    hproducts U T V f hU hV (products U T V f hU hV hc) p a
  have hz := (module_cech_acyclicity_criterion J R B hbasis products hp hrefine).2
    M hM U hU (q + 1) (Nat.succ_pos q) (injectiveResolution M)
  exact hz.of_iso ((injectiveResolution M).isoRightDerivedObj _ (q + 1))

private theorem affine_finite_refinement (Y : Scheme.{u})
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    (R : Sieve V) (hR : R ∈ Scheme.ProEt.topology Y V) :
    ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ i, proAffineEtale (U i).left.hom) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
        Scheme.ProEt.topology Y V := by
  classical
  let X : Y.AffineProEt := .mk V.hom hV
  let F := Scheme.AffineProEt.toProEt Y
  have hr : R.functorPullback F (X := X) ∈ Scheme.AffineProEt.topology Y X :=
    F.cover_lift _ _ hR
  obtain ⟨ι, hι, W, f, hf, hsurj⟩ :=
    Scheme.AffineProEt.exists_finite_jointly_surjective_of_mem_topology hr
  let := hι
  let := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let U (i : Fin (Fintype.card ι)) : Over V := Over.mk (F.map (f (e i)))
  refine ⟨Fintype.card ι, U, fun i ↦ (W (e i)).prop, fun i ↦ hf (e i), ?_⟩
  apply Precoverage.generate_mem_toGrothendieck
  change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
    Scheme.ProEt.precoverage Y V
  rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
  let D : PreZeroHypercover V.left :=
    ⟨Fin (Fintype.card ι), fun i ↦ (W (e i)).left, fun i ↦ (f (e i)).left⟩
  have hs : ∀ x : V.left, ∃ i, x ∈ Set.range (D.f i) := by
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    refine ⟨e.symm i, ?_⟩
    change x ∈ Set.range (f (e (e.symm i))).left
    rw [e.apply_symm_apply]
    exact ⟨y, hy⟩
  have : ∀ i, IsAffine (D.X i) := fun i ↦ (W (e i)).prop.isAffine
  have : IsAffine V.left := hV.isAffine
  have hD : QuasiCompactCover D :=
    ⟨fun {O} hO ↦ IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun i ↦ (D.f i).isSpectralMap) (fun x _ ↦ hs x) O.2 hO.isCompact⟩
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hD,
    (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).2
      ⟨hs, fun i ↦ by
        change WeaklyEtale (f (e i)).left
        infer_instance⟩⟩

private theorem model_finite_refinement (X : Scheme.{u})
    (U : Scheme.coefficientProEtaleSiteModel.{u, v} X)
    (hU : proAffineEtale (AsSmall.down.obj U).hom)
    (T : Type (max v (u + 1)))
    (V : T → Scheme.coefficientProEtaleSiteModel.{u, v} X) (f : ∀ t, V t ⟶ U)
    (hc : Presieve.ofArrows V f ∈
      (Scheme.coefficientProEtaleModelTopology.{u, v} X).toPrecoverage U) :
    ∃ (m : ℕ) (W : Fin m → Scheme.coefficientProEtaleSiteModel.{u, v} X)
      (g : ∀ a, W a ⟶ U),
      (∀ a, proAffineEtale (AsSmall.down.obj (W a)).hom) ∧
      Presieve.ofArrows W g ∈
        (Scheme.coefficientProEtaleModelTopology.{u, v} X).toPrecoverage U ∧
      ∀ a, ∃ (t : T) (k : W a ⟶ V t), k ≫ f t = g a := by
  rcases U with ⟨U₀⟩
  let U : Scheme.coefficientProEtaleSiteModel.{u, v} X := AsSmall.up.obj U₀
  let D : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt := AsSmall.down
  have hcov : (Sieve.ofArrows V f).functorPushforward D ∈
      Scheme.ProEt.topology X (D.obj U) :=
    (CoverPreserving.of_isContinuous D
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (Scheme.ProEt.topology X)).cover_preserve hc
  rw [Sieve.functorPushforward_ofArrows] at hcov
  obtain ⟨m, W, hW, hw, hcover⟩ := affine_finite_refinement X (D.obj U) hU _ hcov
  let E : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X := AsSmall.up
  refine ⟨m, (fun a ↦ E.obj (W a).left), (fun a ↦ E.map (W a).hom), hW, ?_, ?_⟩
  · change Sieve.ofArrows (fun a ↦ E.obj (W a).left) (fun a ↦ E.map (W a).hom) ∈
      Scheme.coefficientProEtaleModelTopology.{u, v} X U
    have h := (CoverPreserving.of_isContinuous E (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).cover_preserve hcover
    rw [Sieve.functorPushforward_ofArrows] at h
    dsimp only [E, D, U, AsSmall.up, AsSmall.down] at h ⊢
    exact h
  · intro a
    obtain ⟨t, k, hk⟩ := Sieve.ofArrows.exists (hw a)
    refine ⟨t, E.map k, ?_⟩
    apply ULift.ext
    exact hk.symm

private theorem model_affine_basis (X : Scheme.{u})
    (U : Scheme.coefficientProEtaleSiteModel.{u, v} X) :
    ∃ (T : Type (max v (u + 1)))
      (V : T → Scheme.coefficientProEtaleSiteModel.{u, v} X) (f : ∀ t, V t ⟶ U),
      Presieve.ofArrows V f ∈
        (Scheme.coefficientProEtaleModelTopology.{u, v} X).toPrecoverage U ∧
      ∀ t, proAffineEtale (AsSmall.down.obj (V t)).hom := by
  rcases U with ⟨U₀⟩
  let U : Scheme.coefficientProEtaleSiteModel.{u, v} X := AsSmall.up.obj U₀
  let D : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt := AsSmall.down
  let E : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X := AsSmall.up
  let F := Scheme.AffineProEt.toProEt X
  let T := ULift.{max v (u + 1)} (Σ Z : X.AffineProEt, F.obj Z ⟶ D.obj U)
  let V : T → X.ProEt := fun t ↦ F.obj t.down.1
  let f : ∀ t : T, V t ⟶ D.obj U := fun t ↦ t.down.2
  have hc : Sieve.ofArrows V f ∈ Scheme.ProEt.topology X (D.obj U) := by
    apply (Scheme.ProEt.topology X).superset_covering ?_ (F.is_cover_of_isCoverDense _ _)
    rintro Z g ⟨⟨W, a, b, hab⟩⟩
    exact (Sieve.mem_ofArrows_iff V f g).2 ⟨ULift.up ⟨W, b⟩, a, hab.symm⟩
  refine ⟨T, (fun t ↦ E.obj (V t)), (fun t ↦ E.map (f t)), ?_, ?_⟩
  · change Sieve.ofArrows (fun t ↦ E.obj (V t)) (fun t ↦ E.map (f t)) ∈
      Scheme.coefficientProEtaleModelTopology.{u, v} X U
    have h := (CoverPreserving.of_isContinuous E (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).cover_preserve hc
    rw [Sieve.functorPushforward_ofArrows] at h
    dsimp only [E, D, U, AsSmall.up, AsSmall.down] at h ⊢
    exact h
  · intro t
    exact t.down.1.prop

/-- Positive derived sections of the comparison pullback vanish over affine etale objects.
Source: Stacks Project, Tag 099U (lemma-affine-vanishing) and Tag 099V
(lemma-relative-comparison), first proof paragraph; blueprint
lemma-acyclicity-pulled-back-injectives, affine restriction and Cech computation
(auxiliary; not a blueprint node).

Proof: use the affine ind-etale basis directly on the coefficient-sized pro-etale
model. Transport cover-density and finite covering refinements through AsSmall.up.
Closure under pullbacks gives closure of all chosen Cech intersections, by induction
using their universal properties. The finite affine Cech calculation gives zero positive
Cech cohomology for the intrinsic comparison pullback. Apply the module Cech criterion
to an injective resolution in the intrinsic module category, then its canonical
right-derived evaluation isomorphism. The requested affine etale object belongs to the
basis. Thus neither localization nor a change to an abelian-sheaf resolution is needed.
No hypothesis on the size of A relative to u, other than the displayed common universe,
is used. Empty coverings and the zero coefficient ring are included -/
theorem coefficientComparison_affineSections_vanishing (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    [HasSheafify (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)}]
    [HasSheafify (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)}]
    [EnoughInjectives (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A))]
    (I : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A)) [Injective I]
    (W : X.AffineEtale) (q : ℕ) :
    IsZero (((SheafOfModules.toSheaf.{max v (u + 1)}
      (siteModuleRings (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) ⋙
      sheafToPresheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
        AddCommGrpCat.{max v (u + 1)} ⋙
      (evaluation (Scheme.coefficientProEtaleSiteModel.{u, v} X)ᵒᵖ
        AddCommGrpCat.{max v (u + 1)}).obj
          (op ((Scheme.smallModelComparisonInclusion.{u, v} X).obj
            (AsSmall.up.obj ((Scheme.AffineEtale.Spec X).obj W))))).rightDerived (q + 1)).obj
              ((constructibleComparisonPullback.{u, v} X A).obj I)) := by
  classical
  let C := Scheme.coefficientProEtaleSiteModel.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let J := K.toPrecoverage
  let D : C ⥤ X.ProEt := AsSmall.down
  have : D.IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_inverse
  have : HasPullbacks C := Adjunction.hasLimitsOfShape_of_equivalence D
  let B : ObjectProperty C :=
    (proAffineEtale.overObj (X := X)).inverseImage (D ⋙ Scheme.ProEt.forget X)
  have hK : J.toGrothendieck = K := by
    apply le_antisymm K.toGrothendieck_toPrecoverage_le
    intro U S hS
    have hs : Sieve.generate S.arrows ∈ J.toGrothendieck U :=
      Precoverage.generate_mem_toGrothendieck
        ((K.arrows_mem_toPrecoverage_iff S).2 hS)
    simpa only [Sieve.generate_sieve] using hs
  let M := (constructibleComparisonPullback.{u, v} X A).obj I
  apply module_cech_vanishing J K hK _ B (model_affine_basis X) ?_
    (model_finite_refinement X) M ?_ _ ?_ q
  · intro U T V f hU hV S p a
    exact cech_objects_mem B S hU hV p a
  · intro U m V f hU hV hc S p hp
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    exact coefficientComparison_affineCech_vanishing X A I U m V f hU hV hc S q
  · change proAffineEtale ((Scheme.AffineEtale.Spec X).obj W).hom
    have hAffine : IsAffine ((Scheme.AffineEtale.Spec X).obj W).left := by
      change IsAffine (Scheme.Spec.obj W.left)
      infer_instance
    exact @proAffineEtale.of_isAffine ((Scheme.AffineEtale.Spec X).obj W).left X
      hAffine ((Scheme.AffineEtale.Spec X).obj W).hom
      ((Scheme.AffineEtale.Spec X).obj W).prop

end AlgebraicGeometry.ProEtale

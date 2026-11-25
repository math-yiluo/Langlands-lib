/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Scalar coherence for derived systems

## References

* Zheng, Construction 4.1 and Proposition 4.17
* Stacks Tags 06YY, 07A4, 07A6 and 08J9
* Zheng Construction 4.1
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096

attribute [local irreducible] WeilConjectures.SemilinearSections.hasDerived
  HasDerivedCategory.standard CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The scalar adjunctions and their two composition compatibilities. -/
structure SystemScalarCoherence where
  /-- Actual derived scalar extension for every composite coefficient homomorphism. -/
  scalar : ∀ {m n : ℕ} (h : n ≤ m),
    ScalarData.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)
  /-- Tensor reassociation for iterated coefficient extension. -/
  scalarComposition : ∀ {l m n : ℕ} (h : n ≤ m) (k : m ≤ l),
    (scalar k).T ⋙ (scalar h).T ≅ (scalar (h.trans k)).T
  /-- Reassociation is the left-adjoint comparison of actual scalar restrictions. -/
  scalarComposition_transpose : ∀ {l m n : ℕ} (h : n ≤ m) (k : m ≤ l)
    (P : D.{c, v, max c v r} J (B l)) (Q : D.{c, v, max c v r} J (B n))
    (f : (scalar (h.trans k)).T.obj P ⟶ Q),
    ((scalar k).adjunction.homEquiv _ _)
      (((scalar h).adjunction.homEquiv _ _)
        ((scalarComposition h k).hom.app P ≫ f)) =
      ((scalar (h.trans k)).adjunction.homEquiv _ _) f ≫
        (restrictionComposition.{c, v, max c v r} J B τ h k).inv.app Q
  /-- The actual reduction maps satisfy the tensor-associator cocycle. -/
  reduction_cocycle : ∀ {l m n : ℕ} (h : n ≤ m) (k : m ≤ l)
    (M : DS.{c, v, max c v r} J B τ),
    (scalar h).T.map (reduction.{c, v, max c v r} J B τ k (scalar k) M) ≫
        reduction.{c, v, max c v r} J B τ h (scalar h) M =
      (scalarComposition h k).hom.app ((e.{c, v, max c v r} J B τ l).obj M) ≫
        reduction.{c, v, max c v r} J B τ (h.trans k) (scalar (h.trans k)) M

private theorem scalar_nonempty {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) : Nonempty (ScalarData.{c, v, max c v r} φ) :=
  (semilinearScalarData.{c, v, r} J (fun _ ↦ R) (fun _ ↦ 𝟙 R)
    (fun _ ↦ S) (fun _ ↦ 𝟙 S) (fun _ ↦ φ) (by intro n; simp)).2 0

private theorem transpose_conjugate {X Z : Type*} [Category X] [Category Z]
    {F G : X ⥤ Z} {U V : Z ⥤ X} (a : F ⊣ U) (b : G ⊣ V)
    (α : U ⟶ V) (P : X) (Q : Z) (f : F.obj P ⟶ Q) :
    b.homEquiv _ _ (((conjugateEquiv a b).symm α).app P ≫ f) =
      a.homEquiv _ _ f ≫ α.app Q := by
  rw [Adjunction.homEquiv_apply, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm, Category.assoc, ← α.naturality]
  rw [Adjunction.homEquiv_apply, Category.assoc]

private theorem transpose_comparison
    {X Y Z : Type*} [Category X] [Category Y] [Category Z]
    {L : X ⥤ Y} {R : Y ⥤ X} {L' : Y ⥤ Z} {R' : Z ⥤ Y}
    {L'' : X ⥤ Z} {R'' : Z ⥤ X}
    (a : L ⊣ R) (b : L' ⊣ R') (d : L'' ⊣ R'') (i : R' ⋙ R ≅ R'')
    (P : X) (Q : Z) (f : L''.obj P ⟶ Q) :
    a.homEquiv _ _ (b.homEquiv _ _
        ((a.leftAdjointCompIso b d i).hom.app P ≫ f)) =
      d.homEquiv _ _ f ≫ i.inv.app Q := by
  have ht := transpose_conjugate d (a.comp b) i.inv P Q f
  rw [Adjunction.comp_homEquiv] at ht
  dsimp only [Equiv.trans] at ht
  exact ht

section ExactTriangles

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors

variable {A₀ A₁ A₂ A₃ : Type*}
  [Category A₀] [Category A₁] [Category A₂] [Category A₃]
  [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian A₃]
  [HasDerivedCategory A₀] [HasDerivedCategory A₁]
  [HasDerivedCategory A₂] [HasDerivedCategory A₃]

private def triangle {F : A₀ ⥤ A₁} {G : A₀ ⥤ A₂} {R : A₂ ⥤ A₁}
    [F.Additive] [G.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (δ : F ⟶ G ⋙ R) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ R.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso A₀ (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    ((G ⋙ R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory (G ⋙ R).mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex δ (.up ℤ)) DerivedCategory.Q) ≫
      (Functor.mapDerivedCategoryCompIso G R).inv

private theorem triangle_fac {F : A₀ ⥤ A₁} {G : A₀ ⥤ A₂} {R : A₂ ⥤ A₁}
    [F.Additive] [G.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (δ : F ⟶ G ⋙ R) (P : CochainComplex A₀ ℤ) :
    (triangle δ).app (DerivedCategory.Q.obj P) ≫
      R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
      R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
    F.mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex δ (.up ℤ)).app P) := by
  have hF : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso A₀ (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory =
    F.mapDerivedCategoryFactors := rfl
  have hG : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso A₀ (.up ℤ))
      ((G ⋙ R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (G ⋙ R).mapDerivedCategory = (G ⋙ R).mapDerivedCategoryFactors := rfl
  simp only [triangle, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Localization.liftNatTrans_app]
  simp only [hF, hG, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

variable (F : A₀ ⥤ A₁) (G : A₀ ⥤ A₂) (H : A₀ ⥤ A₃)
  (R : A₂ ⥤ A₁) (S : A₃ ⥤ A₂) (T : A₃ ⥤ A₁)
  [F.Additive] [G.Additive] [H.Additive] [R.Additive] [S.Additive] [T.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

private theorem triangle_comp (a : F ⟶ G ⋙ R) (b : G ⟶ H ⋙ S)
    (d : F ⟶ H ⋙ T) (i : S ⋙ R ≅ T)
    (hi : ∀ X, a.app X ≫ R.map (b.app X) ≫ i.hom.app (H.obj X) = d.app X) :
    triangle a ≫ Functor.whiskerRight (triangle b) R.mapDerivedCategory ≫
        Functor.whiskerLeft H.mapDerivedCategory
          ((Functor.mapDerivedCategoryCompIso S R) ≪≫
            Functor.mapDerivedCategoryNatIso i).hom = triangle d := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A₀ (.up ℤ))
  intro P
  let Pn := (H.mapHomologicalComplex (.up ℤ)).obj P
  let c := (Functor.mapDerivedCategoryCompIso S R) ≪≫
    Functor.mapDerivedCategoryNatIso i
  have hc : c.hom.app (DerivedCategory.Q.obj Pn) ≫ T.mapDerivedCategoryFactors.hom.app Pn =
      R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app Pn) ≫
        R.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj Pn) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex i.hom (.up ℤ)).app Pn) := by
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso S R).inv.app
      (DerivedCategory.Q.obj Pn))).mp
    simp only [c, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
      Iso.inv_hom_id_app_assoc]
    rw [Functor.mapDerivedCategoryNatIso_fac,
      Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  apply (cancel_mono (T.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
    T.mapDerivedCategoryFactors.hom.app Pn)).mp
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  have hn := c.hom.naturality (H.mapDerivedCategoryFactors.hom.app P)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, hc]
  rw [← R.mapDerivedCategory.map_comp_assoc, ← R.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  rw [triangle_fac b P, R.mapDerivedCategory.map_comp_assoc]
  have hb := R.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex b (.up ℤ)).app P)
  dsimp only [Functor.comp_map] at hb
  erw [reassoc_of% hb]
  rw [reassoc_of% (triangle_fac a P), triangle_fac d P]
  simp only [← Functor.map_comp]
  congr 1
  apply congrArg DerivedCategory.Q.map
  apply HomologicalComplex.Hom.ext
  funext n
  exact hi (P.X n)

end ExactTriangles

private def ordinaryComp {l m n : ℕ} (h : n ≤ m) (k : m ≤ l) :
    res.{c, v, max c v r} (coefficientMap J B τ h) ⋙
      res.{c, v, max c v r} (coefficientMap J B τ k) ≅
    res.{c, v, max c v r} (coefficientMap J B τ (h.trans k)) :=
  (restrictionComposition_existsUnique.{c, v, max c v r} J B τ h k).exists.choose

private theorem ordinary_cocycle {l m n : ℕ} (h : n ≤ m) (k : m ≤ l)
    (M : Systems.{c, v, max c v r} J B τ) :
    (transition.{c, v, max c v r} J B τ k).app M ≫
      (res (coefficientMap J B τ k)).map ((transition J B τ h).app M) ≫
      (ordinaryComp.{c, v, r} J B τ h k).hom.app ((evaluation J B τ n).obj M) =
    (transition J B τ (h.trans k)).app M := by
  have ht (a b : ℕ) (hab : b ≤ a) (U : Cᵒᵖ) :=
    (transition_exists.{c, v, max c v r} J B τ hab).exists.choose_spec M U
  have hc (N : Mod.{c, v, max c v r} J (B n)) (U : Cᵒᵖ) :=
    (restrictionComposition_existsUnique.{c, v, max c v r} J B τ h k).exists.choose_spec N U
  ext U x
  change ((ordinaryComp.{c, v, r} J B τ h k).hom.app
      ((evaluation J B τ n).obj M)).val.app U
      (((res (coefficientMap J B τ k)).map ((transition J B τ h).app M)).val.app U
        (((transition J B τ k).app M).val.app U x)) = _
  have hk := congrFun (eq_of_heq (ht l m k U)) x
  have hh := congrFun (eq_of_heq (ht m n h U))
    (((transition J B τ k).app M).val.app U x)
  have hhk := congrFun (eq_of_heq (ht l n (h.trans k) U)) x
  have hcc := congrFun (eq_of_heq (hc ((evaluation J B τ n).obj M) U))
    (((res (coefficientMap J B τ k)).map ((transition J B τ h).app M)).val.app U
      (((transition J B τ k).app M).val.app U x))
  change ((ordinaryComp.{c, v, r} J B τ h k).hom.app
      ((evaluation J B τ n).obj M)).val.app U
      (((res (coefficientMap J B τ k)).map ((transition J B τ h).app M)).val.app U
        (((transition J B τ k).app M).val.app U x)) = _ at hcc
  rw [hcc]
  change (((transition J B τ h).app M).val.app U)
    (((transition J B τ k).app M).val.app U x) = _
  change (((transition J B τ k).app M).val.app U) x = _ at hk
  change (((transition J B τ h).app M).val.app U)
    (((transition J B τ k).app M).val.app U x) = _ at hh
  change (((transition J B τ (h.trans k)).app M).val.app U) x = _ at hhk
  rw [hh, hk]
  erw [hhk]
  rw [← M.val.map_comp_apply]
  have he : (Prod.mkHom (homOfLE k) (𝟙 U.unop)).op ≫
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op =
      (Prod.mkHom (homOfLE (h.trans k)) (𝟙 U.unop)).op := by
    apply Quiver.Hom.unop_inj
    ext <;> simp
  exact M.val.congr_map_apply he x

private theorem derived_cocycle {l m n : ℕ} (h : n ≤ m) (k : m ≤ l)
    (M : DS.{c, v, max c v r} J B τ) :
    (derivedTransition.{c, v, max c v r} J B τ k).app M ≫
      (resD (coefficientMap J B τ k)).map ((derivedTransition J B τ h).app M) =
    (derivedTransition J B τ (h.trans k)).app M ≫
      (restrictionComposition.{c, v, max c v r} J B τ h k).inv.app
        ((e J B τ n).obj M) := by
  have hh := NatTrans.congr_app
    (triangle_comp (evaluation.{c, v, max c v r} J B τ l)
      (evaluation.{c, v, max c v r} J B τ m)
      (evaluation.{c, v, max c v r} J B τ n)
      (res (coefficientMap J B τ k)) (res (coefficientMap J B τ h))
      (res (coefficientMap J B τ (h.trans k)))
      (transition J B τ k) (transition J B τ h) (transition J B τ (h.trans k))
      (ordinaryComp.{c, v, r} J B τ h k) (ordinary_cocycle.{c, v, r} J B τ h k)) M
  change (derivedTransition J B τ k).app M ≫
      (resD (coefficientMap J B τ k)).map ((derivedTransition J B τ h).app M) ≫
      (restrictionComposition J B τ h k).hom.app ((e J B τ n).obj M) =
    (derivedTransition J B τ (h.trans k)).app M at hh
  exact (Iso.eq_comp_inv ((restrictionComposition J B τ h k).app
    ((e J B τ n).obj M))).2 (by simpa only [Iso.app_hom, Category.assoc] using hh)

/-- Normalized scalar adjunctions and the reduction cocycle, without tensor or Hom data. -/
theorem systemScalarCoherence_nonempty :
    Nonempty (SystemScalarCoherence.{c, v, r} J B τ) := by
  classical
  let S : ∀ {m n : ℕ} (h : n ≤ m),
      ScalarData.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h) :=
    fun h ↦ (scalar_nonempty.{c, v, r} J (coefficientMap J B τ h)).some
  refine ⟨{ scalar := S
            scalarComposition := fun h k ↦
              (S k).adjunction.leftAdjointCompIso (S h).adjunction
                (S (h.trans k)).adjunction (restrictionComposition J B τ h k)
            scalarComposition_transpose := fun h k P Q f ↦
              transpose_comparison (S k).adjunction (S h).adjunction
                (S (h.trans k)).adjunction (restrictionComposition J B τ h k) P Q f
            reduction_cocycle := ?_ }⟩
  intro l m n h k M
  apply ((S h).adjunction.homEquiv _ _).injective
  apply ((S k).adjunction.homEquiv _ _).injective
  rw [(S h).adjunction.homEquiv_naturality_left,
    transpose_comparison (S k).adjunction (S h).adjunction
      (S (h.trans k)).adjunction (restrictionComposition J B τ h k)]
  rw [(S k).adjunction.homEquiv_naturality_right]
  simp only [reduction, Equiv.apply_symm_apply]
  exact derived_cocycle.{c, v, r} J B τ h k M

end WeilConjectures.SemilinearSections

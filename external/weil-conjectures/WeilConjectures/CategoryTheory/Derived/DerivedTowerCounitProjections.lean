/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import
  WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Derived constant towers and the actual inverse-limit counit

Source: Stacks Project, Derived Categories, Tags 09T5 and 0FND;
Cohomology on Sites, Tag 0941 (blueprint: lem-coef-derived-tower-counit-projections).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v wA wT uJ vJ

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem monicKInjectiveResolutions
    {C : Type u} [Category.{v} C] [Abelian C]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q) :
    Abelian.HasKInjectiveResolutions C := by
  constructor
  intro K
  obtain ⟨I, q, hI, hq⟩ := h K
  -- Add a contractible summand to make the resolution monic in every degree.
  let T := CochainComplex.mappingCone (𝟙 K)
  let e : HomotopyEquiv (T ⊞ I) I :=
    { hom := biprod.snd
      inv := biprod.inr
      homotopyHomInvId := by
        let h₀ : Homotopy (𝟙 T) 0 :=
          CochainComplex.mappingCone.liftHomotopy _ _ _
            (CochainComplex.mappingCone.snd _) 0 (by simp) (by simp)
        let h₁ := (h₀.compRight (biprod.inl : T ⟶ T ⊞ I)).compLeft
          (biprod.fst : T ⊞ I ⟶ T)
        let h₂ := Homotopy.add h₁ (Homotopy.refl
          ((biprod.snd : T ⊞ I ⟶ I) ≫ biprod.inr))
        exact (Homotopy.ofEq (by simp)).trans
          (h₂.symm.trans (Homotopy.ofEq (by simp)))
      homotopyInvHomId := Homotopy.ofEq (by simp) }
  have : (T ⊞ I).IsKInjective := e.symm.isKInjective
  let i : K ⟶ T ⊞ I :=
    biprod.lift (CochainComplex.mappingCone.inr (𝟙 K)) q
  have hi : Mono i := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    have hfac : i.f n ≫ (biprod.fst : T ⊞ I ⟶ T).f n ≫
        (CochainComplex.mappingCone.snd (𝟙 K)).v n n (add_zero n) = 𝟙 _ := by
      simp [i, T]
    exact mono_of_mono_fac hfac
  have : QuasiIso e.hom := e.quasiIso_hom
  have : QuasiIso i := by
    have : QuasiIso (i ≫ e.hom) := by simpa [i, e] using hq
    exact (quasiIso_iff_comp_right i e.hom).mp inferInstance
  exact ⟨T ⊞ I, inferInstance, i, hi, inferInstance⟩

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Additivity of constant strict towers, with level zero denoting level one.
Source: Stacks 0941 (blueprint: lem-coef-derived-tower-counit-projections). -/
instance strictTowerConstantAdditive : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).Additive where
  map_add := rfl

variable [HasLimitsOfShape ℕᵒᵖ A]

/-- Inverse limit is additive because it preserves binary products and zero morphisms.
Source: Stacks 0941 (blueprint: lem-coef-derived-tower-counit-projections). -/
instance strictTowerLimitAdditive : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
  Functor.additive_of_preserves_binary_products _

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wT} (ℕᵒᵖ ⥤ A)]

/-- The derived constant/limit adjunction, normalized by its actual tower projections.
Source: Stacks Project, Derived Categories, Tags 09T5 and 0FND; Cohomology on Sites,
Tag 0941 (blueprint: lem-coef-derived-tower-counit-projections).

Here `n : ℕ` denotes the paper's level `n + 1`. The transformation `κ` is the total
right-derived comparison on complexes. Its universal property is `hRL`, and `hκ`
expresses computation on K-injective towers. The isomorphisms `c` implement
`e_n Δ ≅ id`; their displayed formula fixes the canonical termwise identification.
The counit is normalized as a morphism in the derived tower category itself.
The formula for every resolution `q : M ⟶ I` is written after composing with the
invertible `κ.app I` and `Q(q_n)`, so it is exactly the inverse-projection formula
without choosing additional inverses. The transformations `π n` encode both
naturality in the derived tower and independence of the resolution.

Proof plan:
1. The limit universal property gives `constLimAdj`, whose counit is the family
   of limit projections. Constants and evaluations are exact by levelwise
   abelianity (lem-weil-tower-category-levelwise-abelian). Apply the exact-functor
   factorization (situation-conventions) and the termwise
   homotopy adjunction (lem-weil-pbc-termwise-adjunction-homotopy).
2. The exact constant left adjoint shows that the termwise limit of a K-injective
   tower is K-injective (lem-weil-pbc-right-adjoint-preserves-kinjective). The
   total-derived comparison is invertible on those towers
   (lem-weil-pbc-kinjective-total-derived). For q : M → I the comparison is
   rho_q = RL(Qq) followed by the inverse of κ_I.
3. Compute Hom into I and LI in the homotopy categories by
   lem-weil-pbc-kinjective-hom-derived. The ordinary adjunction then gives the
   derived Hom bijection. Its inverse sends h to Q(gamma_I) after Δ(rho_q h),
   followed by the inverse of Qq.
4. Lift a derived map between two resolutions uniquely to a homotopy class.
   Naturality of κ and of the ordinary counit gives naturality of the Hom
   bijection and independence of resolutions. Naturality in the other variable
   extends from chain maps and inverse quasi-isomorphisms by localization.
5. Take the transpose of the identity for the counit and the inverse transpose
   of the identity for the unit. Naturality gives both triangle identities.
6. On a K-injective tower the transpose of the identity is the ordinary counit.
   Its evaluation is the limit projection. Counit naturality transports this
   equality along every resolution q, giving the displayed resolution formula.
   No equality of derived tower maps is inferred merely from their evaluations.
7. For λ, compose Δλ with the counit. Counit naturality and λ-naturality prove
   naturality in the arbitrary parameter category J. Evaluation, step 6, and
   the canonical c give the final component formula. -/
theorem derived_tower_counit_projections
    (h : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : M ⟶ I), CochainComplex.IsKInjective I ∧ QuasiIso q)
    (RL : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    (κ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RL)
    (hRL : ∀ G : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A,
      Function.Bijective (fun β : RL ⟶ G ↦ κ ≫ Functor.whiskerLeft DerivedCategory.Q β))
    (hκ : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, CochainComplex.IsKInjective I → IsIso (κ.app I)) :
    ∃ (adj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ RL)
      (c : ∀ n : ℕ, (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⋙
        ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ≅ 𝟭 (DerivedCategory A))
      (π : ∀ n : ℕ, RL ⟶ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory),
      (∀ (n : ℕ) (N : CochainComplex A ℤ),
        (c n).hom.app (DerivedCategory.Q.obj N) =
          ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map
            ((Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app N) ≫
          ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app
            (((Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (.up ℤ)).obj N)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), CochainComplex.IsKInjective I →
        (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map (κ.app I) ≫
            adj.counit.app (DerivedCategory.Q.obj I) =
          (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((Adjunction.mapHomologicalComplex (.up ℤ)
              (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim)).counit.app I)) ∧
      (∀ (n : ℕ) (M I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : M ⟶ I)
        [QuasiIso q], CochainComplex.IsKInjective I →
        κ.app I ≫ inv (RL.map (DerivedCategory.Q.map q)) ≫
            (π n).app (DerivedCategory.Q.obj M) ≫
            ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app M ≫
            DerivedCategory.Q.map
              ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).map q) =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)) ∧
      (∀ (n : ℕ) (B : DerivedCategory (ℕᵒᵖ ⥤ A)),
        ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map (adj.counit.app B) =
          (c n).hom.app (RL.obj B) ≫ (π n).app B) ∧
      (∀ (J : Type uJ) [Category.{vJ} J]
        (C : J ⥤ DerivedCategory A) (B : J ⥤ DerivedCategory (ℕᵒᵖ ⥤ A))
        (lam : C ⟶ B ⋙ RL),
        ∃ η : C ⋙ (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⟶ B,
          (∀ j : J, η.app j =
            (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map (lam.app j) ≫
              adj.counit.app (B.obj j)) ∧
          (∀ (n : ℕ) (j : J),
            ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map (η.app j) =
              (c n).hom.app (C.obj j) ≫ lam.app j ≫ (π n).app (B.obj j))) := by
  classical
  let := monicKInjectiveResolutions h
  let L := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A)
  let Ld := L.mapDerivedCategory
  let α := L.mapDerivedCategoryFactors.hom
  let W := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)
  have hκ' (X : CochainComplex.KInjectives (ℕᵒᵖ ⥤ A)) :
      IsIso (κ.app X.obj) := hκ X.obj X.property
  let : RL.IsRightDerivedFunctor κ W := by
    constructor
    constructor
    refine ⟨IsInitial.ofUniqueHom (fun Z ↦ StructuredArrow.homMk
      ((Equiv.ofBijective _ (hRL Z.right)).symm Z.hom)
      ((Equiv.ofBijective _ (hRL Z.right)).apply_symm_apply Z.hom)) ?_⟩
    intro Z m
    apply StructuredArrow.hom_ext
    apply (hRL Z.right).injective
    exact m.w.trans ((Equiv.ofBijective _ (hRL Z.right)).apply_symm_apply Z.hom).symm
  let : (RL ⋙ Ld).IsRightDerivedFunctor
      (Functor.whiskerRight κ Ld ≫ (Functor.associator _ _ _).hom) W :=
    (CochainComplex.KInjectives.localizerMorphism _)
      |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure κ hκ' Ld
  let : Ld.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso A (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ L.mapDerivedCategoryFactors
  let : (Ld ⋙ RL).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α RL)
      (HomologicalComplex.quasiIso A (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight L.mapDerivedCategoryFactors RL)
  -- The abstract derived adjunction retains the ordinary counit's factorization.
  let adj := (constLimAdj.mapHomologicalComplex (.up ℤ)).derived
    (HomologicalComplex.quasiIso A (.up ℤ)) W α κ
  have hcounit (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      Ld.map (κ.app I) ≫ adj.counit.app (DerivedCategory.Q.obj I) =
        α.app ((lim.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((constLimAdj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
    exact (constLimAdj.mapHomologicalComplex (.up ℤ)).derivedε_fac_app W α κ I
  let E (n : ℕ) := (evaluation ℕᵒᵖ A).obj (op n)
  let Ed (n : ℕ) := (E n).mapDerivedCategory
  let b (n : ℕ) : DerivedCategory.Q ⋙ (Ld ⋙ Ed n) ≅ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight L.mapDerivedCategoryFactors (Ed n) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (L.mapHomologicalComplex (.up ℤ))
        (E n).mapDerivedCategoryFactors
  let c (n : ℕ) : Ld ⋙ Ed n ≅ 𝟭 (DerivedCategory A) := by
    letI : Localization.Lifting DerivedCategory.Q
        (HomologicalComplex.quasiIso A (.up ℤ)) DerivedCategory.Q (Ld ⋙ Ed n) := ⟨b n⟩
    exact Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      (Ld ⋙ Ed n) (𝟭 _) (Iso.refl _)
  have hc (n : ℕ) (N : CochainComplex A ℤ) :
      (c n).hom.app (DerivedCategory.Q.obj N) =
        (Ed n).map (α.app N) ≫
          (E n).mapDerivedCategoryFactors.hom.app
            ((L.mapHomologicalComplex (.up ℤ)).obj N) := by
    dsimp [c]
    rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
    simp [Localization.Lifting.iso, b, α]
  -- Define projections from the actual counit, so naturality is built in.
  let π (n : ℕ) : RL ⟶ Ed n :=
    Functor.whiskerLeft RL (c n).inv ≫ Functor.whiskerRight adj.counit (Ed n)
  have hπ (n : ℕ) (B : DerivedCategory (ℕᵒᵖ ⥤ A)) :
      (Ed n).map (adj.counit.app B) = (c n).hom.app (RL.obj B) ≫ (π n).app B := by
    simp [π]
  have hproj (n : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      κ.app I ≫ (π n).app (DerivedCategory.Q.obj I) ≫
          (E n).mapDerivedCategoryFactors.hom.app I =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) := by
    change κ.app I ≫ ((c n).inv.app (RL.obj (DerivedCategory.Q.obj I)) ≫
      (Ed n).map (adj.counit.app (DerivedCategory.Q.obj I))) ≫ _ = _
    have hn := (c n).inv.naturality (κ.app I)
    change κ.app I ≫ (c n).inv.app (RL.obj (DerivedCategory.Q.obj I)) =
      (c n).inv.app (DerivedCategory.Q.obj
        ((lim.mapHomologicalComplex (.up ℤ)).obj I)) ≫ (Ed n).map (Ld.map (κ.app I)) at hn
    simp only [Category.assoc]
    rw [reassoc_of% hn]
    rw [← (Ed n).map_comp_assoc, hcounit]
    have heval := (E n).mapDerivedCategoryFactors_hom_naturality
      ((constLimAdj.mapHomologicalComplex (.up ℤ)).counit.app I)
    dsimp only [Functor.id_obj, Functor.comp_obj] at heval
    rw [(Ed n).map_comp, Category.assoc, heval]
    rw [← reassoc_of% (hc n ((lim.mapHomologicalComplex (.up ℤ)).obj I))]
    simp only [Iso.inv_hom_id_app_assoc]
    rfl
  refine ⟨adj, c, π, hc, fun I _ ↦ hcounit I, ?_, hπ, ?_⟩
  · intro n M I q _ _
    have hn := (π n).naturality (DerivedCategory.Q.map q)
    change RL.map (DerivedCategory.Q.map q) ≫ (π n).app (DerivedCategory.Q.obj I) =
      (π n).app (DerivedCategory.Q.obj M) ≫ (Ed n).map (DerivedCategory.Q.map q) at hn
    rw [← (E n).mapDerivedCategoryFactors_hom_naturality q]
    rw [← reassoc_of% hn]
    simp only [IsIso.inv_hom_id_assoc]
    exact hproj n I
  · intro J _ C B lam
    let η : C ⋙ Ld ⟶ B :=
      Functor.whiskerRight lam Ld ≫ Functor.whiskerLeft B adj.counit
    refine ⟨η, fun _ ↦ rfl, ?_⟩
    intro n j
    change (Ed n).map (Ld.map (lam.app j) ≫ adj.counit.app (B.obj j)) = _
    rw [(Ed n).map_comp, hπ, ← Category.assoc]
    simpa only [Functor.comp_map, Functor.id_map, Functor.comp_obj,
      Functor.id_obj, Category.assoc] using
      congrArg (fun f ↦ f ≫ (π n).app (B.obj j))
        ((c n).hom.naturality (lam.app j))

end CategoryTheory

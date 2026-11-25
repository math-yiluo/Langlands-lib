/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Normalized comparison for an exact square preserving K-injectives

Source: Stacks Project, Derived Categories, Tags 070I, 070Y and 070K; exact-square
extraction of the tower normalization argument
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison).

The units are expressed on the homotopy category, as in def-sfb-right-derived-functor.
The canonical localization factors are retained in the two normalization arrows.

## Main definitions and statements

* `KInjectiveExactSquare.leftUnit` and `rightUnit`: the arrows a and b.
* `KInjectiveExactSquare.delta`: the comparison b a⁻¹ on K-injectives.
* `KInjectiveExactSquare.existsUnique_normalized`: descent, formula and uniqueness.
-/

@[expose] public section

set_option autoImplicit false

universe uA' uA uB' uB vA' vA vB' vB wA' wA wB' wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.KInjectiveExactSquare

variable {A' : Type uA'} {A : Type uA} {B' : Type uB'} {B : Type uB}
  [Category.{vA'} A'] [Category.{vA} A] [Category.{vB'} B'] [Category.{vB} B]
  [Abelian A'] [Abelian A] [Abelian B'] [Abelian B]
  [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wA} A]
  [HasDerivedCategory.{wB'} B'] [HasDerivedCategory.{wB} B]
  (H' : A' ⥤ B') (H : A ⥤ B) (r : A' ⥤ A) (s : B' ⥤ B)
  [H'.Additive] [H.Additive] [r.Additive] [s.Additive]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  [PreservesFiniteLimits s] [PreservesFiniteColimits s]
  (h : H' ⋙ s = r ⋙ H)
  (RH' : DerivedCategory A' ⥤ DerivedCategory B')
  (RH : DerivedCategory A ⥤ DerivedCategory B)
  (η' : H'.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RH')
  (η : H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RH)

/-- The canonical strict-square identification on homotopy categories, directed from Hr to sH'.
Source: Stacks Tags 070I and 070Y, exact-square extraction, proof step 1
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison). -/
def sourceIso :
    r.mapHomotopyCategory (.up ℤ) ⋙ H.mapHomotopyCategory (.up ℤ) ≅
      H'.mapHomotopyCategory (.up ℤ) ⋙ s.mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (Iso.refl (r ⋙ H)) (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (eqToIso h) (.up ℤ)).symm

/-- The arrow a_J, including the inverse exact-localization factor for s.
Source: Stacks Tags 070Y and 070K, exact-square extraction, proof step 1
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison). -/
noncomputable def leftUnit (J : CochainComplex A' ℤ) :
    DerivedCategory.Qh.obj ((H.mapHomotopyCategory (.up ℤ)).obj
      ((r.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A' (.up ℤ)).obj J))) ⟶
      (RH' ⋙ s.mapDerivedCategory).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) :=
  DerivedCategory.Qh.map ((sourceIso H' H r s h).hom.app
      ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) ≫
    s.mapDerivedCategoryFactorsh.inv.app ((H'.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) ≫
    s.mapDerivedCategory.map (η'.app ((HomotopyCategory.quotient A' (.up ℤ)).obj J))

/-- The arrow b_J, including RH of the inverse exact-localization factor for r.
Source: Stacks Tags 070Y and 070K, exact-square extraction, proof step 1
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison). -/
noncomputable def rightUnit (J : CochainComplex A' ℤ) :
    DerivedCategory.Qh.obj ((H.mapHomotopyCategory (.up ℤ)).obj
      ((r.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A' (.up ℤ)).obj J))) ⟶
      (r.mapDerivedCategory ⋙ RH).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) :=
  η.app ((r.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) ≫
    RH.map (r.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient A' (.up ℤ)).obj J))

/-- The normalized comparison δ_J = b_J a_J⁻¹, when a_J is invertible.
Source: Stacks Tags 070I, 070Y and 070K, exact-square extraction, proof step 1
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison). -/
noncomputable def delta (J : CochainComplex A' ℤ)
    (ha : IsIso (leftUnit H' H r s h RH' η' J)) :
    (RH' ⋙ s.mapDerivedCategory).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) ⟶
      (r.mapDerivedCategory ⋙ RH).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) :=
  letI := ha
  inv (leftUnit H' H r s h RH' η' J) ≫ rightUnit H r RH η J

private theorem unit_isIso
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wA} C] [HasDerivedCategory.{wB} D]
    (F : C ⥤ D) [F.Additive]
    (enough : ∀ K : CochainComplex C ℤ,
      ∃ (J : CochainComplex C ℤ) (f : K ⟶ J), J.IsKInjective ∧ QuasiIso f)
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (θ : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (universal : ∀ G : DerivedCategory C ⥤ DerivedCategory D,
      Function.Bijective (fun α : RF ⟶ G ↦ θ ≫ Functor.whiskerLeft DerivedCategory.Qh α))
    (J : CochainComplex C ℤ) [J.IsKInjective] :
    IsIso (θ.app ((HomotopyCategory.quotient C (.up ℤ)).obj J)) := by
  -- Transfer invertibility from the canonical universal pair to the given pair.
  obtain ⟨e, he, _⟩ := F.rightDerivedFunctorOfQuasiIsoResolutions_unique enough RF θ universal
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso enough J
  rw [← he]
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-- An exact strictly commuting square preserving K-injectives has a unique comparison
normalized only on K-injectives, natural on homotopy classes and independent of resolutions.
Source: Stacks Project, Derived Categories, Tags 070I, 070Y and 070K; exact-square extraction
(blueprint: lem-weil-pbc-kinjective-exact-square-comparison).

Proof plan:
1. The units of the fixed universal pairs are invertible on K-injectives by
   def-sfb-right-derived-functor. The preservation hypothesis applies this also to rJ.
   The canonical factors of situation-conventions are invertible,
   so a_J and b_J are isomorphisms with common source Q(HrJ).
2. Additive functors preserve chain homotopies. Naturality of the units and localization
   factors gives A(Qf)a_J = a_J'V(f) and B(Qf)b_J = b_J'V(f). Cancelling a gives naturality
   of delta for every homotopy class between K-injectives.
3. By lem-weil-pbc-kinjective-hom-derived every derived map between these objects is the
   image of a homotopy class. Every derived object is isomorphic to QJ for a K-injective J,
   by the arbitrary-quasi-isomorphism hypothesis and def-weil-abstract-derived-category.
4. For u : M ≅ QJ define beta_M = A(u) delta_J B(u inverse). For another v : M ≅ QJ',
   apply step 3 to u inverse followed by v. Its naturality identity proves independence.
5. For f : M ⟶ N use resolutions u and v and the derived map u inverse followed by f
   followed by v. Step 3 proves naturality of beta. Its factors are invertible, hence beta
   is a natural isomorphism. Choosing u = identity gives the normalization and the formula.
6. Any other normalized natural isomorphism agrees with delta on QJ by cancelling a_J.
   Naturality along each u gives the same formula everywhere, proving uniqueness using
   normalization only on K-injectives. No adjunction, tower or monomorphic resolution is used.
-/
theorem existsUnique_normalized
    (enough' : ∀ K : CochainComplex A' ℤ,
      ∃ (J : CochainComplex A' ℤ) (f : K ⟶ J), J.IsKInjective ∧ QuasiIso f)
    (enough : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (f : K ⟶ J), J.IsKInjective ∧ QuasiIso f)
    (preserves : ∀ J : CochainComplex A' ℤ, J.IsKInjective →
      CochainComplex.IsKInjective ((r.mapHomologicalComplex (.up ℤ)).obj J))
    (universal' : ∀ G : DerivedCategory A' ⥤ DerivedCategory B',
      Function.Bijective (fun α : RH' ⟶ G ↦ η' ≫ Functor.whiskerLeft DerivedCategory.Qh α))
    (universal : ∀ G : DerivedCategory A ⥤ DerivedCategory B,
      Function.Bijective (fun α : RH ⟶ G ↦ η ≫ Functor.whiskerLeft DerivedCategory.Qh α)) :
    ∃ (ha : ∀ J : CochainComplex A' ℤ, J.IsKInjective →
        IsIso (leftUnit H' H r s h RH' η' J))
      (_hb : ∀ J : CochainComplex A' ℤ, J.IsKInjective → IsIso (rightUnit H r RH η J))
      (β : RH' ⋙ s.mapDerivedCategory ≅ r.mapDerivedCategory ⋙ RH),
      (∀ (J : CochainComplex A' ℤ), J.IsKInjective →
        leftUnit H' H r s h RH' η' J ≫
          β.hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) =
        rightUnit H r RH η J) ∧
      (∀ γ : RH' ⋙ s.mapDerivedCategory ≅ r.mapDerivedCategory ⋙ RH,
        (∀ (J : CochainComplex A' ℤ), J.IsKInjective →
          leftUnit H' H r s h RH' η' J ≫
            γ.hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)) =
          rightUnit H r RH η J) → γ = β) ∧
      (∀ (J J' : CochainComplex A' ℤ) (hJ : J.IsKInjective) (hJ' : J'.IsKInjective)
          (f : (HomotopyCategory.quotient A' (.up ℤ)).obj J ⟶
            (HomotopyCategory.quotient A' (.up ℤ)).obj J'),
        (RH' ⋙ s.mapDerivedCategory).map (DerivedCategory.Qh.map f) ≫
            delta H' H r s h RH' RH η' η J' (ha J' hJ') =
          delta H' H r s h RH' RH η' η J (ha J hJ) ≫
            (r.mapDerivedCategory ⋙ RH).map (DerivedCategory.Qh.map f)) ∧
      (∀ (M : DerivedCategory A') (J : CochainComplex A' ℤ) (hJ : J.IsKInjective)
          (u : M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J)),
        β.hom.app M = (RH' ⋙ s.mapDerivedCategory).map u.hom ≫
          delta H' H r s h RH' RH η' η J (ha J hJ) ≫
            (r.mapDerivedCategory ⋙ RH).map u.inv) ∧
      (∀ (M : DerivedCategory A') (J J' : CochainComplex A' ℤ)
          (hJ : J.IsKInjective) (hJ' : J'.IsKInjective)
          (u : M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J))
          (v : M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient A' (.up ℤ)).obj J')),
        (RH' ⋙ s.mapDerivedCategory).map u.hom ≫
            delta H' H r s h RH' RH η' η J (ha J hJ) ≫
              (r.mapDerivedCategory ⋙ RH).map u.inv =
          (RH' ⋙ s.mapDerivedCategory).map v.hom ≫
            delta H' H r s h RH' RH η' η J' (ha J' hJ') ≫
              (r.mapDerivedCategory ⋙ RH).map v.inv) := by
  classical
  let π := HomotopyCategory.quotient A' (.up ℤ)
  let Q : HomotopyCategory A' (.up ℤ) ⥤ DerivedCategory A' := DerivedCategory.Qh
  let F := RH' ⋙ s.mapDerivedCategory
  let G := r.mapDerivedCategory ⋙ RH
  -- Package the normalization arrows as natural transformations before cancellation.
  let a : r.mapHomotopyCategory (.up ℤ) ⋙
      H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ Q ⋙ F :=
    Functor.whiskerRight (sourceIso H' H r s h).hom DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (H'.mapHomotopyCategory (.up ℤ)) s.mapDerivedCategoryFactorsh.inv ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight η' s.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom
  let b : r.mapHomotopyCategory (.up ℤ) ⋙
      H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ Q ⋙ G :=
    Functor.whiskerLeft (r.mapHomotopyCategory (.up ℤ)) η ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight r.mapDerivedCategoryFactorsh.inv RH ≫
      (Functor.associator _ _ _).hom
  have ha (J : CochainComplex A' ℤ) (hJ : J.IsKInjective) :
      IsIso (leftUnit H' H r s h RH' η' J) := by
    have := unit_isIso H' enough' RH' η' universal' J
    unfold leftUnit
    infer_instance
  have hb (J : CochainComplex A' ℤ) (hJ : J.IsKInjective) :
      IsIso (rightUnit H r RH η J) := by
    have := preserves J hJ
    have hunit := unit_isIso H enough RH η universal
      ((r.mapHomologicalComplex (.up ℤ)).obj J)
    have : IsIso (η.app ((r.mapHomotopyCategory (.up ℤ)).obj (π.obj J))) :=
      (NatTrans.isIso_app_iff_of_iso η
        ((r.mapHomotopyCategoryFactors (.up ℤ)).app J)).mpr hunit
    unfold rightUnit
    infer_instance
  have a_app (J : CochainComplex A' ℤ) :
      a.app (π.obj J) = leftUnit H' H r s h RH' η' J := by
    simp [a, leftUnit, π]
  have b_app (J : CochainComplex A' ℤ) :
      b.app (π.obj J) = rightUnit H r RH η J := by
    simp [b, rightUnit, π]
  have ha' (J : CochainComplex A' ℤ) (hJ : J.IsKInjective) :
      IsIso (a.app (π.obj J)) := by rw [a_app]; exact ha J hJ
  have hb' (J : CochainComplex A' ℤ) (hJ : J.IsKInjective) :
      IsIso (b.app (π.obj J)) := by rw [b_app]; exact hb J hJ
  let d (J : CochainComplex A' ℤ) (hJ : J.IsKInjective) :
      F.obj (Q.obj (π.obj J)) ⟶ G.obj (Q.obj (π.obj J)) :=
    letI := ha' J hJ
    inv (a.app (π.obj J)) ≫ b.app (π.obj J)
  have hd (J : CochainComplex A' ℤ) (hJ : J.IsKInjective) :
      d J hJ = delta H' H r s h RH' RH η' η J (ha J hJ) := by
    have := ha' J hJ
    have := ha J hJ
    dsimp only [d, delta]
    congr 1
    · apply IsIso.inv_eq_inv.mpr
      exact a_app J
    · exact b_app J
  have dn (J J' : CochainComplex A' ℤ) (hJ : J.IsKInjective) (hJ' : J'.IsKInjective)
      (f : π.obj J ⟶ π.obj J') :
      F.map (Q.map f) ≫ d J' hJ' = d J hJ ≫ G.map (Q.map f) := by
    have := ha' J hJ
    have := ha' J' hJ'
    apply (cancel_epi (a.app (π.obj J))).1
    change a.app (π.obj J) ≫ (F.map (Q.map f) ≫
      (inv (a.app (π.obj J')) ≫ b.app (π.obj J'))) =
        a.app (π.obj J) ≫ ((inv (a.app (π.obj J)) ≫ b.app (π.obj J)) ≫
          G.map (Q.map f))
    have an := a.naturality f
    dsimp only [Functor.comp_map] at an
    rw [← Category.assoc, ← an]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact b.naturality f
  -- Every derived morphism into a K-injective is the image of a homotopy class.
  have dn' (J J' : CochainComplex A' ℤ) (hJ : J.IsKInjective) (hJ' : J'.IsKInjective)
      (f : Q.obj (π.obj J) ⟶ Q.obj (π.obj J')) :
      F.map f ≫ d J' hJ' = d J hJ ≫ G.map f := by
    obtain ⟨g, rfl⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (π.obj J) J').surjective f
    exact dn J J' hJ hJ' g
  -- Resolve a representative of each derived object, using arbitrary quasi-isomorphisms.
  choose J f hJ hf using enough'
  let j (X : DerivedCategory A') := J (DerivedCategory.Q.objPreimage X)
  have hj (X : DerivedCategory A') : (j X).IsKInjective := hJ _
  have hq (K : CochainComplex A' ℤ) : IsIso (DerivedCategory.Q.map (f K)) := by
    have := hf K
    infer_instance
  let e (X : DerivedCategory A') : X ≅ Q.obj (π.obj (j X)) :=
    (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫
      asIso (DerivedCategory.Q.map (f (DerivedCategory.Q.objPreimage X))) ≪≫
      (DerivedCategory.quotientCompQhIso A').symm.app (j X)
  -- Conjugate the comparison on replacements, then descend its naturality.
  let c (X : DerivedCategory A') : F.obj X ⟶ G.obj X :=
    F.map (e X).hom ≫ d (j X) (hj X) ≫ G.map (e X).inv
  have cn {X Y : DerivedCategory A'} (f : X ⟶ Y) :
      F.map f ≫ c Y = c X ≫ G.map f := by
    have ht := dn' (j X) (j Y) (hj X) (hj Y) ((e X).inv ≫ f ≫ (e Y).hom)
    have ht' := congrArg
      (fun t ↦ F.map (e X).hom ≫ t ≫ G.map (e Y).inv) ht
    simpa only [c, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_map_assoc, Iso.inv_hom_id_map_assoc,
      Iso.hom_inv_id_map, Category.comp_id] using ht'
  have ci (X : DerivedCategory A') : IsIso (c X) := by
    have := ha' (j X) (hj X)
    have := hb' (j X) (hj X)
    dsimp only [c, d]
    infer_instance
  let β : F ≅ G := NatIso.ofComponents (fun X ↦ asIso (c X)) (fun f ↦ cn f)
  -- Compare the chosen replacement with any other one; this also proves independence.
  have formula (X : DerivedCategory A') (J : CochainComplex A' ℤ) (hJ : J.IsKInjective)
      (u : X ≅ Q.obj (π.obj J)) :
      β.hom.app X = F.map u.hom ≫ d J hJ ≫ G.map u.inv := by
    have ht := dn' (j X) J (hj X) hJ ((e X).inv ≫ u.hom)
    have ht' := congrArg (fun t ↦ F.map (e X).hom ≫ t ≫ G.map u.inv) ht
    change c X = _
    simpa only [c, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_map_assoc, Iso.inv_hom_id_map_assoc,
      Iso.hom_inv_id_map, Category.comp_id] using ht'.symm
  have atJ (J : CochainComplex A' ℤ) (hJ : J.IsKInjective) :
      β.hom.app (Q.obj (π.obj J)) = d J hJ := by
    simpa using formula (Q.obj (π.obj J)) J hJ (Iso.refl _)
  refine ⟨ha, hb, β, ?_, ?_, ?_, ?_, ?_⟩
  · intro J hJ
    have := ha' J hJ
    rw [atJ J hJ, ← a_app, ← b_app]
    exact IsIso.hom_inv_id_assoc _ _
  · intro γ hγ
    apply Iso.ext
    apply NatTrans.ext
    funext X
    have heq : γ.hom.app (Q.obj (π.obj (j X))) = β.hom.app (Q.obj (π.obj (j X))) := by
      have := ha (j X) (hj X)
      apply (cancel_epi (leftUnit H' H r s h RH' η' (j X))).1
      rw [hγ (j X) (hj X), atJ (j X) (hj X), ← b_app, ← a_app]
      have := ha' (j X) (hj X)
      change _ = a.app (π.obj (j X)) ≫ (inv (a.app (π.obj (j X))) ≫ _)
      simp
    apply (cancel_mono (G.map (e X).hom)).1
    rw [← γ.hom.naturality, ← β.hom.naturality, heq]
  · intro J J' hJ hJ' f
    rw [← hd J hJ, ← hd J' hJ']
    exact dn J J' hJ hJ' f
  · intro X J hJ u
    rw [← hd J hJ]
    exact formula X J hJ u
  · intro X J J' hJ hJ' u v
    rw [← hd J hJ, ← hd J' hJ', ← formula X J hJ u, ← formula X J' hJ' v]

end CategoryTheory.KInjectiveExactSquare

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows

/-!
# Projection-formula arrows and their specified finite-total inverse

Source: Weil conjectures blueprint, proper base change, definition 1264
(blueprint: def-weil-pbc-projection-formula-arrows).
-/

@[expose] public section

universe u v u' v' w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) (V : B ⥤ A) [L.Additive] [V.Additive] (adj : L ⊣ V)
  (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)

/-- The ordinary counit mate t_{M,P}.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionMate (M : B) (P : A) :
    V.obj M ⊗ P ⟶ V.obj (M ⊗ L.obj P) :=
  adj.homEquiv _ _ ((e (V.obj M) P).hom ≫ (adj.counit.app M ⊗ₘ 𝟙 (L.obj P)))

omit [Abelian A] [Abelian B] [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts A] [HasCoproducts B] [L.Additive] [V.Additive] in
set_option backward.isDefEq.respectTransparency false in
private lemma tensorAdjunctionMate_naturality
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (M : B) {P Q : A} (f : P ⟶ Q) :
    (𝟙 (V.obj M) ⊗ₘ f) ≫ tensorAdjunctionMate L V adj e M Q =
      tensorAdjunctionMate L V adj e M P ≫ V.map (𝟙 M ⊗ₘ L.map f) := by
  unfold tensorAdjunctionMate
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  rw [← Category.assoc, he, L.map_id]
  simp only [Category.assoc]
  congr 1
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- For finite free coefficients the ordinary mate is the finite-product comparison.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: the unit equation reduces the mate in rank one to the identity by the
adjunction triangle identity. Naturality and additivity identify rank N with the
N-fold finite-sum map. Finite sums are products and the right adjoint preserves
products, including the empty product. Thus the comparison is invertible. -/
theorem tensorAdjunctionMate_free_isIso
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (M : B) (N : ℕ) :
    IsIso (tensorAdjunctionMate L V adj e M (∏ᶜ fun _ : Fin N ↦ 𝟙_ A)) := by
  classical
  let T := tensorLeft (V.obj M)
  let U := L ⋙ tensorLeft M ⋙ V
  let t : T ⟶ U :=
    { app := tensorAdjunctionMate L V adj e M
      naturality := by
        intro P Q f
        simpa only [T, U, Functor.comp_map, tensorLeft, curriedTensor_obj_map, id_tensorHom] using
          tensorAdjunctionMate_naturality L V adj e he M f }
  have ht : t.app (𝟙_ A) ≫ V.map ((𝟙 M ⊗ₘ j.hom) ≫ (ρ_ M).hom) =
      (ρ_ (V.obj M)).hom := by
    change tensorAdjunctionMate L V adj e M _ ≫ _ = _
    unfold tensorAdjunctionMate
    rw [← adj.homEquiv_naturality_right]
    apply (adj.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    rw [← hj]
    simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Category.comp_id,
      Category.id_comp]
    have hcomm : adj.counit.app M ⊗ₘ j.hom =
        (𝟙 (L.obj (V.obj M)) ⊗ₘ j.hom) ≫
          (adj.counit.app M ⊗ₘ 𝟙 (𝟙_ B)) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    rw [hcomm]
    simp only [Category.assoc, tensorHom_id]
    rw [rightUnitor_naturality]
  have : IsIso (t.app (𝟙_ A)) := by
    have : IsIso (t.app (𝟙_ A) ≫ V.map ((𝟙 M ⊗ₘ j.hom) ≫ (ρ_ M).hom)) := by
      rw [ht]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (V.map ((𝟙 M ⊗ₘ j.hom) ≫ (ρ_ M).hom))
  have hw : t.app (∏ᶜ fun _ : Fin N ↦ 𝟙_ A) ≫
      piComparison U (fun _ : Fin N ↦ 𝟙_ A) =
      piComparison T (fun _ : Fin N ↦ 𝟙_ A) ≫
        Limits.Pi.map (fun _ : Fin N ↦ t.app (𝟙_ A)) := by
    apply Pi.hom_ext
    intro k
    simp only [Category.assoc, piComparison_comp_π, Pi.map_π, piComparison_comp_π_assoc]
    exact (t.naturality (Pi.π (fun _ : Fin N ↦ 𝟙_ A) k)).symm
  have : IsIso (t.app (∏ᶜ fun _ : Fin N ↦ 𝟙_ A) ≫
      piComparison U (fun _ : Fin N ↦ 𝟙_ A)) := by
    rw [hw]
    infer_instance
  change IsIso (t.app _)
  exact IsIso.of_isIso_comp_right _ (piComparison U (fun _ : Fin N ↦ 𝟙_ A))

/-- The specified free inverse q_{M,N}, the inverse of t and not an arbitrary map.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionFreeInverse
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (M : B) (N : ℕ) :=
  @inv _ _ _ _ (tensorAdjunctionMate L V adj e M (∏ᶜ fun _ : Fin N ↦ 𝟙_ A))
    (tensorAdjunctionMate_free_isIso L V adj e he j hj M N)

/-- The displayed splitting formula for s_{a,r}, equally for any single retract.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionRetractInverse
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (M : B) (P : A) (N : ℕ)
    (i : P ⟶ ∏ᶜ fun _ : Fin N ↦ 𝟙_ A)
    (p : (∏ᶜ fun _ : Fin N ↦ 𝟙_ A) ⟶ P) :
    V.obj (M ⊗ L.obj P) ⟶ V.obj M ⊗ P :=
  V.map (𝟙 M ⊗ₘ L.map i) ≫ tensorAdjunctionFreeInverse L V adj e he j hj M N ≫
    (𝟙 (V.obj M) ⊗ₘ p)

set_option backward.isDefEq.respectTransparency false in
private lemma tensorAdjunctionRetractInverse_identities
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (M : B) (P : A) (N : ℕ)
    (i : P ⟶ ∏ᶜ fun _ : Fin N ↦ 𝟙_ A)
    (p : (∏ᶜ fun _ : Fin N ↦ 𝟙_ A) ⟶ P) (hip : i ≫ p = 𝟙 P) :
    tensorAdjunctionMate L V adj e M P ≫
        tensorAdjunctionRetractInverse L V adj e he j hj M P N i p = 𝟙 _ ∧
      tensorAdjunctionRetractInverse L V adj e he j hj M P N i p ≫
        tensorAdjunctionMate L V adj e M P = 𝟙 _ := by
  let := tensorAdjunctionMate_free_isIso L V adj e he j hj M N
  unfold tensorAdjunctionRetractInverse tensorAdjunctionFreeInverse
  constructor
  · rw [← Category.assoc, ← tensorAdjunctionMate_naturality L V adj e he M i]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [tensorHom_comp_tensorHom, hip, Category.id_comp, id_tensorHom_id]
  · simp only [Category.assoc]
    rw [tensorAdjunctionMate_naturality L V adj e he M p]
    rw [IsIso.inv_hom_id_assoc, ← V.map_comp, tensorHom_comp_tensorHom,
      ← L.map_comp, hip, L.map_id, Category.id_comp, id_tensorHom_id, V.map_id]


private noncomputable def restrictCofanIsColimit
    {D : Type*} [Category D] [HasZeroMorphisms D] {J : Type*} {f : J → D}
    (c : Cofan f) (hc : IsColimit c) (s : J → Prop)
    (hz : ∀ j, ¬s j → IsZero (f j)) :
    IsColimit (Cofan.mk c.pt (fun j : Subtype s ↦ c.inj j.val)) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun t ↦ Cofan.IsColimit.desc hc
      (fun j ↦ if hj : s j then t.inj ⟨j, hj⟩ else 0)) ?_ ?_
  · intro t j
    change c.inj j.val ≫ _ = t.inj j
    simpa only [dite_eq_left j.property] using
      Cofan.IsColimit.fac hc
        (fun j ↦ if hj : s j then t.inj ⟨j, hj⟩ else 0) j.val
  · intro t m hm
    apply Cofan.IsColimit.hom_ext hc
    intro j
    rw [Cofan.IsColimit.fac]
    by_cases hj : s j
    · rw [dite_eq_left hj]
      exact hm ⟨j, hj⟩
    · exact (hz j hj).eq_of_src _ _

private noncomputable def extendCofanIsColimitOfZeroOutside
    {D : Type*} [Category D] [HasZeroMorphisms D] {J : Type*} {f : J → D}
    (c : Cofan f) (s : J → Prop)
    (hc : IsColimit (Cofan.mk c.pt (fun j : Subtype s ↦ c.inj j.val)))
    (hz : ∀ j, ¬s j → IsZero (f j)) : IsColimit c := by
  refine Cofan.IsColimit.mk _
    (fun t ↦ Cofan.IsColimit.desc hc (fun j ↦ t.inj j.val)) ?_ ?_
  · intro t j
    by_cases hj : s j
    · exact Cofan.IsColimit.fac hc (fun j ↦ t.inj j.val) ⟨j, hj⟩
    · exact (hz j hj).eq_of_src _ _
  · intro t m hm
    apply Cofan.IsColimit.hom_ext hc
    intro j
    rw [Cofan.IsColimit.fac]
    exact hm j.val

private lemma isIso_of_cofans
    {D : Type*} [Category D] {J : Type*} {X Y : J → D}
    (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
    (t : c.pt ⟶ d.pt) (a : ∀ j, X j ⟶ Y j) [∀ j, IsIso (a j)]
    (ht : ∀ j, c.inj j ≫ t = a j ≫ d.inj j) : IsIso t := by
  let s := Cofan.IsColimit.desc hd (fun j ↦ inv (a j) ≫ c.inj j)
  have hs (j : J) : d.inj j ≫ s = inv (a j) ≫ c.inj j :=
    Cofan.IsColimit.fac hd _ j
  refine ⟨s, Cofan.IsColimit.hom_ext hc _ _ (fun j ↦ ?_),
    Cofan.IsColimit.hom_ext hd _ _ (fun j ↦ ?_)⟩
  · rw [← Category.assoc, ht, Category.assoc, hs,
      IsIso.hom_inv_id_assoc, Category.comp_id]
  · rw [← Category.assoc, hs, Category.assoc, ht,
      IsIso.inv_hom_id_assoc, Category.comp_id]

private noncomputable def mapCofanIsColimit_finiteSupport
    {D E : Type*} [Category D] [Abelian D] [Category E] [Abelian E]
    {J : Type*} {f : J → D} (V : D ⥤ E) [V.Additive]
    (c : Cofan f) (hc : IsColimit c) (s : J → Prop) [Finite (Subtype s)]
    (hz : ∀ j, ¬s j → IsZero (f j)) :
    IsColimit (Cofan.mk (V.obj c.pt) (fun j ↦ V.map (c.inj j))) := by
  let hr := restrictCofanIsColimit c hc s hz
  let hv := isColimitCofanMkObjOfIsColimit V _ _ hr
  exact extendCofanIsColimitOfZeroOutside _ s hv (fun j hj ↦ V.map_isZero (hz j hj))

set_option backward.isDefEq.respectTransparency false in
private lemma tensorAdjunctionTotal_summand
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ)
    (a r n : ℤ) (h : a + r = n) :
    CochainComplex.ιMapBifunctor
        ((V.mapHomologicalComplex (.up ℤ)).obj I) F (curriedTensor A) a r n h ≫
        (tensorAdjunctionTotal L V adj e he I F).f n =
      tensorAdjunctionMate L V adj e (I.X a) (F.X r) ≫
        V.map (CochainComplex.ιMapBifunctor I
          ((L.mapHomologicalComplex (.up ℤ)).obj F) (curriedTensor B) a r n h) := by
  let P := (V.mapHomologicalComplex (.up ℤ)).obj I
  let LF := (L.mapHomologicalComplex (.up ℤ)).obj F
  let LP := (L.mapHomologicalComplex (.up ℤ)).obj P
  let β := tensorPullbackTotal L e he P F
  let := tensorPullbackTotal_isIso L e he V adj P F
  have hb : L.map (CochainComplex.ιMapBifunctor P F (curriedTensor A) a r n h) ≫
      (inv β).f n = (e (P.X a) (F.X r)).hom ≫
        CochainComplex.ιMapBifunctor LP LF (curriedTensor B) a r n h := by
    apply (cancel_mono (β.f n)).1
    simp only [Category.assoc, ← HomologicalComplex.comp_f, IsIso.inv_hom_id,
      HomologicalComplex.id_f]
    change _ = _ ≫ _ ≫ tensorPullbackTotalComponent L e P F n
    simp only [tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc,
      Iso.hom_inv_id_assoc]
    exact Category.comp_id _
  change _ ≫ adj.homEquiv _ _ ((inv β).f n ≫
    (HomologicalComplex.mapBifunctorMap
      ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) (𝟙 LF)
        (curriedTensor B) (.up ℤ)).f n) = _
  unfold tensorAdjunctionMate
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  rw [← Category.assoc, hb, Category.assoc]
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, Adjunction.mapHomologicalComplex_counit_app_f,
    curriedTensor_map_app, curriedTensor_obj_map, Category.assoc, tensorHom_def]
  rfl

attribute [local irreducible] tensorAdjunctionTotal

/-- Bounded split-free coefficients make the total mate an isomorphism of complexes.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: in bidegree (a,r) the splitting formula is inverse to t. The two identities
follow by naturality of t at i_r,p_r, their splitting relation, and the inverse
identities of q. Multiplying naturality by these inverses proves compatibility
with each differential; their indices agree and so do the signs (-1)^a.
There are finitely many nonzero summands in each degree. The right adjoint preserves
these finite sums, so the degree maps of the total mate are invertible. -/
theorem tensorAdjunctionTotal_isIso
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (N : ℤ → ℕ) (i : ∀ r, F.X r ⟶ ∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)
    (p : ∀ r, (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A) ⟶ F.X r)
    (hsplit : ∀ r, i r ≫ p r = 𝟙 (F.X r)) :
    IsIso (tensorAdjunctionTotal L V adj e he I F) := by
  classical
  let LF := (L.mapHomologicalComplex (.up ℤ)).obj F
  let P := (V.mapHomologicalComplex (.up ℤ)).obj I
  let C := CochainComplex.mapBifunctor P F (curriedTensor A)
  let D := CochainComplex.mapBifunctor I LF (curriedTensor B)
  let t := tensorAdjunctionTotal L V adj e he I F
  obtain ⟨lo, hi, hF⟩ := hbounded
  have hv (n : ℤ) : IsColimit (Cofan.mk (V.obj (D.X n))
      (fun x : {x : ℤ × ℤ // x.1 + x.2 = n} ↦
        V.map (CochainComplex.ιMapBifunctor I LF (curriedTensor B)
          x.val.1 x.val.2 n x.property))) := by
    let s : {x : ℤ × ℤ // x.1 + x.2 = n} → Prop :=
      fun x ↦ lo ≤ x.val.2 ∧ x.val.2 ≤ hi
    have : Finite (Subtype s) := by
      apply Finite.of_injective
        (fun x : Subtype s ↦ (⟨x.val.val.2, x.property⟩ : Set.Icc lo hi))
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · have h := congrArg Subtype.val hxy
        have hx := x.val.property
        have hy := y.val.property
        dsimp at h hx hy ⊢
        omega
      · exact congrArg Subtype.val hxy
    apply mapCofanIsColimit_finiteSupport V _
      (GradedObject.isColimitCofanMapObj
        ((((curriedTensor B).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj I).obj
          LF).toGradedObject _ n) s
    intro x hx
    have hz : IsZero (F.X x.val.2) := hF _ (by
      dsimp [s] at hx
      omega)
    exact (tensorLeft (I.X x.val.1)).map_isZero (L.map_isZero hz)
  have (n : ℤ) : IsIso (t.f n) := by
    let a (x : {x : ℤ × ℤ // x.1 + x.2 = n}) :=
      tensorAdjunctionMate L V adj e (I.X x.val.1) (F.X x.val.2)
    have (x : {x : ℤ × ℤ // x.1 + x.2 = n}) : IsIso (a x) := by
      let q := tensorAdjunctionRetractInverse L V adj e he j hj
        (I.X x.val.1) (F.X x.val.2) (N x.val.2) (i x.val.2) (p x.val.2)
      obtain ⟨h₁, h₂⟩ := tensorAdjunctionRetractInverse_identities L V adj e he j hj
        (I.X x.val.1) (F.X x.val.2) (N x.val.2) (i x.val.2) (p x.val.2)
        (hsplit x.val.2)
      exact ⟨q, h₁, h₂⟩
    apply isIso_of_cofans _
      (GradedObject.isColimitCofanMapObj
        ((((curriedTensor A).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P).obj
          F).toGradedObject _ n) _ (hv n) (t.f n) a
    intro x
    exact tensorAdjunctionTotal_summand L V adj e he I F x.val.1 x.val.2 n x.property
  exact HomologicalComplex.Hom.isIso_of_components t

/-- The finite-total chain inverse, determined uniquely by the forward chain map.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows). -/
noncomputable def tensorAdjunctionTotalInverse
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X : A, (e X (𝟙_ A)).hom ≫ (𝟙 (L.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj X)).hom = L.map (ρ_ X).hom)
    (I : CochainComplex B ℤ) (F : CochainComplex A ℤ)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (N : ℤ → ℕ) (i : ∀ r, F.X r ⟶ ∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)
    (p : ∀ r, (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A) ⟶ F.X r)
    (hsplit : ∀ r, i r ≫ p r = 𝟙 (F.X r)) :=
  @inv _ _ _ _ (tensorAdjunctionTotal L V adj e he I F)
    (tensorAdjunctionTotal_isIso L V adj e he j hj I F hbounded N i p hsplit)

attribute [local irreducible] tensorAdjunctionTotalInverse

set_option linter.unusedSectionVars false in
/-- The target tensor total is K-injective for the specified bounded split-free package.
Source: definition 1264 (blueprint: def-weil-pbc-projection-formula-arrows).
Proof: additivity transports the bounded support and each splitting through L.
The unit isomorphism j and finite-sum preservation identify L of a finite free
object with a finite free object. Hence L(F) is bounded split-free. Dualize its
finite free retracts termwise: evaluation identifies tensoring with L(F) with
Hom from its bounded dual, with the usual signed differential. That dual is
K-flat. Hom from a K-flat complex into K is K-injective, yielding the claim
(lem-weil-pbc-split-perfect-tensor-kinjective). -/
theorem tensorAdjunctionTotal_target_isKInjective
    (j : L.obj (𝟙_ A) ≅ 𝟙_ B)
    (K : CochainComplex B ℤ) (hK : K.IsKInjective) (F : CochainComplex A ℤ)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (N : ℤ → ℕ) (i : ∀ r, F.X r ⟶ ∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)
    (p : ∀ r, (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A) ⟶ F.X r)
    (hsplit : ∀ r, i r ≫ p r = 𝟙 (F.X r)) :
    (CochainComplex.mapBifunctor K
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) (curriedTensor B)).IsKInjective  := by
  classical
  let Q := HomotopyCategory.quotient B (.up ℤ)
  let T := ((curriedTensor B).bifunctorMapHomotopyCategory
    (.up ℤ) (.up ℤ) (.up ℤ)).obj (Q.obj K)
  let O := (HomotopyCategory.subcategoryAcyclic B).rightOrthogonal
  let H := HomotopyCategory.singleFunctor B 0 ⋙ T
  have hunit : O (H.obj (𝟙_ B)) := by
    let e : H.obj (𝟙_ B) ≅ Q.obj K :=
      Q.mapIso (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor B) (𝟙_ B) K ≪≫
        (NatIso.mapHomologicalComplex (rightUnitorNatIso B) (.up ℤ)).app K ≪≫
        (Functor.mapHomologicalComplexIdIso B (.up ℤ)).app K)
    exact O.prop_of_iso e.symm ((CochainComplex.isKInjective_iff_rightOrthogonal K).1 hK)
  have hterm (r : ℤ) : O (H.obj (L.obj (F.X r))) := by
    let G := L ⋙ H
    have hG : O (G.obj (𝟙_ A)) :=
      O.prop_of_iso (H.mapIso j).symm hunit
    have hfree : O (G.obj (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)) := by
      intro X f hX
      apply (cancel_mono (piComparison G (fun _ : Fin (N r) ↦ 𝟙_ A))).1
      apply Pi.hom_ext
      intro k
      simp only [Category.assoc, piComparison_comp_π, zero_comp]
      exact hG _ hX
    let ri : Retract (G.obj (F.X r))
        (G.obj (∏ᶜ fun _ : Fin (N r) ↦ 𝟙_ A)) :=
      (⟨i r, p r, hsplit r⟩ : Retract _ _).map G
    intro X f hX
    calc
      f = (f ≫ ri.i) ≫ ri.r := by
        rw [Category.assoc, ri.retract]
        exact (Category.comp_id f).symm
      _ = 0 := by
        have hf : f ≫ ri.i = 0 := hfree (f ≫ ri.i) hX
        rw [hf, zero_comp]
  let LF : CochainComplex B ℤ := (L.mapHomologicalComplex (.up ℤ)).obj F
  obtain ⟨a, b, hb⟩ := hbounded
  have : LF.IsStrictlyGE a := (LF.isStrictlyGE_iff a).2
    (fun n hn ↦ L.map_isZero (hb n (Or.inl hn)))
  have : LF.IsStrictlyLE b := (LF.isStrictlyLE_iff b).2
    (fun n hn ↦ L.map_isZero (hb n (Or.inr hn)))
  have hh := HomotopyCategory.mem_subcategory_of_strictly_bounded
    (O.inverseImage T) LF a b (fun n _ _ ↦ hterm n)
  exact (CochainComplex.isKInjective_iff_rightOrthogonal _).2 hh

end CategoryTheory

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]


end CategoryTheory

attribute [local irreducible] HomologicalComplex₂.total HomologicalComplex.mapBifunctorMap

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency true

set_option synthInstance.maxSize 2048

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
  (PR : ObjectProperty (CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ))
  (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
  (TR : DerivedCategory (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) × DerivedCategory (SheafOfModules.{u} ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
  (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
    ((@curriedTensor (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) _ (monoidalCategory R)).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
        ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)

end SheafOfModules

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

-- The definition keeps all ordinary and derived representative identifications explicit.
end SheafOfModules

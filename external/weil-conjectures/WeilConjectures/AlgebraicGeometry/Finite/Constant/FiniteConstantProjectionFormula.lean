/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeConstantProjection
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.FiniteFreeApproximationTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.ProjectionApproximation
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# The projection formula with a finitely presented constant module

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
lemma proposition-open-direct-image-preserves-finite--1 (blueprint:
proposition-open-direct-image-preserves-finite--1). The ordinary, uncompleted tensor and K-injective
direct image are those of the recorded unbounded etale framework. The constant inverse-image
comparison identifies the target with `Rf_*(K ⊗^L M_X)`. No properness or torsion hypothesis is
imposed.
-/

@[expose] public section

universe u u'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] Sheaf.monoidalCategory in
private theorem isLE_derivedTensor_obj
    (B : Type u') [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (Z : Scheme.{u})
    (U V : DerivedCategory (Sheaf Z.smallEtaleTopology B)) (b c : ℤ)
    [U.IsLE b] [V.IsLE c] :
    (((derivedTensor B Z).obj U).obj V).IsLE (b + c) :=
  _root_.DerivedCategory.isLE_tensor U V b c

/-- The canonical projection map for a constant module, as a natural transformation in
that module. Its source is `Rf_*K ⊗^L M_Y` and its target is `Rf_*(K ⊗^L M_X)`.
It is the recorded adjunction-mate projection map, followed by the canonical identification
of the derived inverse image of the constant sheaf with the constant sheaf on the source.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
lemma proposition-open-direct-image-preserves-finite--1, first proof paragraph
(blueprint: proposition-open-direct-image-preserves-finite--1). -/
noncomputable def finiteConstantProjectionMap
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategoryModule A X) :
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      _root_.DerivedCategory.singleFunctor _ 0) ⋙
        (derivedTensor (ModuleCat.{u + 1} A) Y).obj
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K) ⟶
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      _root_.DerivedCategory.singleFunctor _ 0) ⋙
        (derivedTensor (ModuleCat.{u + 1} A) X).obj K ⋙
          (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor := by
  let C_Y := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  let C_X := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let S_Y := _root_.DerivedCategory.singleFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) 0
  let S_X := _root_.DerivedCategory.singleFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0
  let R := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
  let L := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  let T_X := (derivedTensor (ModuleCat.{u + 1} A) X).obj K
  let T_Y := (derivedTensor (ModuleCat.{u + 1} A) Y).obj (R.obj K)
  let π : (C_Y ⋙ S_Y) ⋙ T_Y ⟶ (C_Y ⋙ S_Y) ⋙ L ⋙ T_X ⋙ R :=
    Functor.whiskerLeft (C_Y ⋙ S_Y)
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K)
  let α : C_Y ⋙ S_Y ⋙ L ⟶ C_Y ⋙ upperStar (ModuleCat.{u + 1} A) f ⋙ S_X :=
    Functor.whiskerLeft C_Y
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).hom
  let β : (C_Y ⋙ upperStar (ModuleCat.{u + 1} A) f) ⋙ S_X ⟶ C_X ⋙ S_X :=
    Functor.whiskerRight (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom
      S_X
  -- Explicit reassociation keeps kernel checking from unfolding the derived functors.
  exact π ≫
    (Functor.associator (C_Y ⋙ S_Y) L (T_X ⋙ R)).inv ≫
    Functor.whiskerRight (Functor.associator C_Y S_Y L).hom (T_X ⋙ R) ≫
    Functor.whiskerRight α (T_X ⋙ R) ≫
    Functor.whiskerRight
      (Functor.associator C_Y (upperStar (ModuleCat.{u + 1} A) f) S_X).inv (T_X ⋙ R) ≫
    Functor.whiskerRight β (T_X ⋙ R)

/-- The projection component before the constant-pullback identification.
Source: the proof of the finite-constant projection theorem immediately below
(blueprint: proposition-open-direct-image-preserves-finite--1).
This is the existing proof's intermediate `hα`, named so proof consumers can use the
projection component without unfolding `finiteConstantProjectionMap`. The same
finite-free approximation argument proves it; the public theorem then composes it
with the constant-pullback isomorphisms. -/
private theorem finiteConstantProjectionComponent_isIso
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ)
    (hcd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ),
      N < q → IsZero ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))
    (K : DerivedCategoryModule A X)
    (hK : ∃ b : ℤ, ∀ q : ℤ, b < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K))
    (M : ModuleCat.{u + 1} A) [Module.FinitePresentation A M] :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M))) := by
  classical
  let C := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  let R := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
  let L := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  let F := (derivedTensor (ModuleCat.{u + 1} A) Y).obj (R.obj K)
  let G := L ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj K ⋙ R
  let α : F ⟶ G := (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K
  let hFs : F.CommShift ℤ := commShiftDerivedTensorObj _ (R.obj K)
  let hLs : L.CommShift ℤ := commShiftLeftDerivedUpperStar _ f
  let hRs : R.CommShift ℤ := commShiftRightDerivedLowerStar _ f
  let hGs : G.CommShift ℤ :=
    Functor.CommShift.comp (A := ℤ) L ((derivedTensor (ModuleCat.{u + 1} A) X).obj K ⋙ R)
  have hFtri : F.IsTriangulated := isTriangulated_derivedTensor_obj _ _
  have hLtri : L.IsTriangulated := isTriangulated_leftDerivedUpperStar _ f
  have hRtri : R.IsTriangulated := isTriangulated_rightDerivedLowerStar _ f
  have hTX : ((derivedTensor (ModuleCat.{u + 1} A) X).obj K).IsTriangulated :=
    isTriangulated_derivedTensor_obj _ K
  have hGtri : G.IsTriangulated :=
    (inferInstance : (L ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj K ⋙ R).IsTriangulated)
  let τ := Functor.whiskerLeft C.mapDerivedCategory α
  obtain ⟨b, hb⟩ := hK
  have hKb : K.IsLE b := (_root_.DerivedCategory.isLE_iff K b).2 hb
  have hdim (E : DerivedCategoryModule A X) (c : ℤ) (hE : E.IsLE c) :
      (R.obj E).IsLE (c + N) :=
    (lowerStar (ModuleCat.{u + 1} A) f).isLE_rightDerivedFunctor_obj_of_dimension N
      (fun V q hq ↦ Functor.isZero_rightDerived_of_isZero_homology
        (lowerStar (ModuleCat.{u + 1} A) f) V q (hcd V q hq)) E c hE
  have hRK : (R.obj K).IsLE (b + N) := hdim K b hKb
  have hFB (E : _root_.DerivedCategory (ModuleCat.{u + 1} A)) (c : ℤ)
      (hE : E.IsLE c) : ((C.mapDerivedCategory ⋙ F).obj E).IsLE (c + (b + N)) := by
    have hCE := C.isLE_mapDerivedCategory_obj E c
    have h := isLE_derivedTensor_obj (ModuleCat.{u + 1} A) Y (R.obj K)
      (C.mapDerivedCategory.obj E) (b + N) c
    rw [Int.add_comm c (b + (N : ℤ))]
    exact h
  have hGB (E : _root_.DerivedCategory (ModuleCat.{u + 1} A)) (c : ℤ)
      (hE : E.IsLE c) : ((C.mapDerivedCategory ⋙ G).obj E).IsLE (c + (b + N)) := by
    have hCE := C.isLE_mapDerivedCategory_obj E c
    have hU := Functor.isLE_mapDerivedCategory_obj
      (upperStar (ModuleCat.{u + 1} A) f) (C.mapDerivedCategory.obj E) c
    have hLE : (L.obj (C.mapDerivedCategory.obj E)).IsLE c :=
      _root_.DerivedCategory.TStructure.t.isLE_of_iso
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm.app
          (C.mapDerivedCategory.obj E)) c
    have ht := isLE_derivedTensor_obj (ModuleCat.{u + 1} A) X K
      (L.obj (C.mapDerivedCategory.obj E)) b c
    have h := hdim (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj
      (L.obj (C.mapDerivedCategory.obj E))) (b + c) ht
    have heq : c + (b + (N : ℤ)) = b + c + N := by omega
    rw [heq]
    exact h
  have hτ : IsIso (τ.app ((_root_.DerivedCategory.singleFunctor _ 0).obj M)) := by
    apply _root_.DerivedCategory.isIso_app_of_approximations
      (C.mapDerivedCategory ⋙ F) (C.mapDerivedCategory ⋙ G) τ _ (b + N) hFB hGB
    intro c
    obtain ⟨P, a, z, T, ha, hz, hfree, hT, h₁, h₂, hcone⟩ :=
      _root_.DerivedCategory.exists_finiteFree_approximation_triangle A M c
    refine ⟨T, hT, h₂, hcone, ?_⟩
    rw [h₁]
    have := ha
    have := hz
    dsimp only [τ, Functor.whiskerLeft_app]
    have hf := isIso_projectionMap_bounded_finiteFree_constant A f K P a z hfree
    exact hf
  have hα : IsIso (α.app ((_root_.DerivedCategory.singleFunctor _ 0).obj (C.obj M))) := by
    let e := (C.mapDerivedCategorySingleFunctor 0).app M
    exact (NatTrans.isIso_app_iff_of_iso (F := F) (G := G) α e).1 hτ
  dsimp only [α, C] at hα
  exact hα

/-- With a uniform all-sheaf cohomological-dimension bound and Noetherian coefficients,
the canonical projection map is an isomorphism for a bounded-above complex and a finitely
presented constant module. Naturality in `M` is built into `finiteConstantProjectionMap`.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
lemma proposition-open-direct-image-preserves-finite--1
(blueprint: proposition-open-direct-image-preserves-finite--1).

Proof plan:
1. Constant sheaves are exact by exact sheafification
   (lem-weil-pbc-site-r-module-presheaf-sheafification-exact). The constant inverse-image
   isomorphism respects addition and scalars (lem-weil-pbc-sets-etale-inverse-image-constant-sheaf);
   inverse image is exact (situation-conventions). Thus the mate is natural
   on constant complexes and its value on `M[0]` is the displayed map.
2. The projection mate is compatible with distinguished triangles and is the identity at
   the tensor unit (lem-weil-pbc-ringed-projection-mate-exact). Finite sums and shifts give
   the assertion for finite free modules. Brutal truncations, the cohomology long exact
   sequence (lem-sf-derived-homology-long-exact), the five lemma (lem-weil-pbc-five-lemma),
   and cohomological detection of isomorphisms (lem-weil-pbc-unbounded-derived-iso-cohomology)
   extend it to bounded finite free complexes.
3. Resolve `M` by finite free modules in nonpositive degrees. Noetherian submodules are
   finite (lem-weil-pbc-noetherian-submodule-finite), so all syzygies can be covered by finite
   free modules. For `P_m = σ_{≥-m} P`, the cone of `P_m → M` has cohomology at most `-m-1`:
   its degree zero cohomology vanishes by surjectivity, also for `m = 0`, and exactness
   kills degrees `-m` through `-1` for `m > 0`. Only the bottom kernel can survive.
4. Direct image is additive and left exact (lem-weil-pbc-module-direct-image-left-exact),
   and module sheaves have enough injectives (lem-weil-pbc-module-sheaves-enough-injectives).
   The uniform bound and lem-sf-finite-cd-derived-upper-bound (Stacks 07K7, (4)(c)) give
   `Rf_* D^{≤t} ⊆ D^{≤t+N}`, in particular `Rf_*K ∈ D^{≤b+N}` for an upper bound `b` of `K`.
5. Bounded-above flat replacements (proposition-open-direct-image-preserves-finite) are K-flat
   (lem-kun-kflat-criteria). Their total tensor has no summand above the sum of the upper
   term bounds. Exactness of constant sheaves and Step 4 put both error terms with the
   constant cone in `D^{≤b+N-m-1}`.
6. For a fixed `r`, choose `m ≥ 0` with `b+N-m-1 < r-1`. The long exact sequences show
   that replacing `M` by `P_m` changes neither side's degree `r` cohomology. Naturality
   gives a square whose other three sides are invertible, so the map for `M` is invertible
   on degree `r` cohomology. Do this for every `r` and use cohomological detection of
   isomorphisms. Naturality requires no natural choice of the free resolution. -/
theorem isIso_finiteConstantProjectionMap
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ)
    (hcd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ),
      N < q → IsZero ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))
    (K : DerivedCategoryModule A X)
    (hK : ∃ b : ℤ, ∀ q : ℤ, b < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K))
    (M : ModuleCat.{u + 1} A) [Module.FinitePresentation A M] :
    IsIso ((finiteConstantProjectionMap A f K).app M) := by
  have hα := finiteConstantProjectionComponent_isIso A f N hcd K hK M
  dsimp only [finiteConstantProjectionMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  refine IsIso.comp_isIso' ?_ ?_
  · exact hα
  · infer_instance

end AlgebraicGeometry.Etale

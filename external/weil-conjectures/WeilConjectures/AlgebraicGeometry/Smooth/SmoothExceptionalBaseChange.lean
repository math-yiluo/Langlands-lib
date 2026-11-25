/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality

import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothDualityBaseChangeCompat

/-! # Arbitrary base change for smooth ambient duality

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/prop-asd-smooth-base-change.md
(blueprint: proposition-exceptional-inverse-image-smooth-morphism--6).

The exceptional comparison is the transpose of the inverse compact-support exchange
followed by the pulled-back counit. The coefficient-unit and tensor comparisons below
are the canonical ones; no orientation or arbitrary comparison is chosen.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

-- Fix the canonical universe model before elaborating the derived functors.
attribute [local instance] Scheme.Etale.essentiallySmall

attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory

/-- The canonical exceptional base-change morphism, obtained by transposing the pulled-back
counit through the inverse compact-support exchange. Source: blueprint
sec-smooth-purity/sk-prop-sf-cbc/prop-asd-smooth-base-change.md, first proof paragraph
(blueprint: proposition-exceptional-inverse-image-smooth-morphism--6). All functors act on ordinary
unbounded categories. The occurrence of the left derived inverse image is canonically identified
with the exact degreewise inverse image by `leftDerivedUpperStarIsoMapDerivedCategory`. -/
noncomputable def smoothExceptionalBaseChangeMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] [QuasiCompact f]
    (g : S' ⟶ S) (K : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
      ((rightDerivedUpperShriek A f).obj K) ⟶
    (rightDerivedUpperShriek A (pullback.snd f g)).obj
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) := by
  letI := isIso_rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g)
  exact (rightDerivedUpperShriekAdjunction A
    (pullback.snd f g)).homEquiv _ _
    (inv ((rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app
      ((rightDerivedUpperShriek A f).obj K)) ≫
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
        ((rightDerivedUpperShriekAdjunction A f).counit.app K))

/-- The base-change morphism on relative dualizing complexes: the exceptional comparison at
the coefficient unit, followed by the canonical inverse-image identification of that unit.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/prop-asd-smooth-base-change.md,
clause at `K = A_S` (blueprint: proposition-exceptional-inverse-image-smooth-morphism--6). -/
noncomputable def smoothDualizingBaseChangeMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] [QuasiCompact f]
    (g : S' ⟶ S) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
      (dualizingComplex A f) ⟶
    dualizingComplex A (pullback.snd f g) :=
  smoothExceptionalBaseChangeMap A f g (𝟙_ _) ≫
    (rightDerivedUpperShriek A (pullback.snd f g)).map
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom

/-- The canonical identification `g'^* f^* K ≅ f'^* g^* K`, formed from the inverse-image
composition isomorphisms and the equality of the two maps around the pullback square.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/prop-asd-smooth-base-change.md,
tensor-compatibility identification (blueprint:
proposition-exceptional-inverse-image-smooth-morphism--6). -/
noncomputable def smoothSquarePullbackIso
    (A : Type (u + 1)) [CommRing A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (K : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K) ≅
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (pullback.fst f g) f).symm.app K ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (pullback.snd f g) g
      (pullback.fst f g ≫ f) (pullback.condition)).app K

/-- The tensor-domain identification in the smooth-duality square. Its first factor is the
canonical K-flat derived tensor-pullback comparison; the second is inverse-image composition.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/prop-asd-smooth-base-change.md,
last sentence (blueprint: proposition-exceptional-inverse-image-smooth-morphism--6). -/
noncomputable def smoothDualityTensorBaseChangeIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (g : S' ⟶ S) (K : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj
          (dualizingComplex A f)) ≅
    ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
      ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))).obj
      ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
        (dualizingComplex A f)) :=
  leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (pullback.fst f g)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)
      (dualizingComplex A f) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).mapIso
      (smoothSquarePullbackIso A f g K)).app
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
          (dualizingComplex A f))

private lemma braided_tensor_mate
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (P W : C) (K Q : D)
    (π : F.obj (W ⊗ P) ⟶ Q ⊗ K) (ε : Q ⟶ 𝟙_ D) :
    adj.homEquiv _ _ (F.map (β_ P W).hom ≫ π ≫
        (β_ Q K).hom ≫ (K ◁ ε) ≫ (ρ_ K).hom) =
      (β_ P W).hom ≫ (adj.homEquiv _ _ (π ≫ (ε ▷ K)) ≫ G.map (λ_ K).hom) := by
  rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left]
  apply congrArg (adj.homEquiv _ _)
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor]

private lemma smooth_tensor_map_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [hPF : IsIso (projectionMap (ModuleCat.{u + 1} Λ) f)]
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    let := derivedBraidedCategory Λ X
    smoothTensorDualityMap Λ f hPF K =
      (β_ ((upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)
        (dualizingComplex Λ f)).hom ≫ dualizingComplexTensorMap Λ f K := by
  let := derivedBraidedCategory Λ X
  let := derivedBraidedCategory Λ S
  exact braided_tensor_mate (rightDerivedUpperShriekAdjunction Λ f)
    _ _ K _ (inv (((projectionMap (ModuleCat.{u + 1} Λ) f).app _).app K))
    ((rightDerivedUpperShriekAdjunction Λ f).counit.app (𝟙_ _))

private lemma mate_app_eq
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : C ⥤ C'} {H : D ⥤ D'}
    (ξ : TwoSquare G L L' H) (M : D) :
    (mateEquiv adj adj' ξ).app M =
      (adj'.homEquiv _ _) (ξ.app (R.obj M) ≫ H.map (adj.counit.app M)) := by
  apply (adj'.homEquiv _ _).symm.injective
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact mateEquiv_counit adj adj' ξ M

private lemma braided_tensor_square
    {C C' : Type*} [Category* C] [Category* C']
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory C'] [BraidedCategory C']
    (G : C ⥤ C') (P W Z : C) (P' W' Z' : C')
    (a : W ⊗ P ⟶ Z) (a' : W' ⊗ P' ⟶ Z') (b : G.obj W ⟶ W')
    (κ : G.obj P ⟶ P') (β : G.obj Z ⟶ Z')
    (δ : ∀ M N : C, G.obj (M ⊗ N) ⟶ G.obj M ⊗ G.obj N)
    (ha : G.map a ≫ β = δ W P ≫ b ▷ G.obj P ≫ W' ◁ κ ≫ a')
    (hδ : G.map (β_ P W).hom ≫ δ W P =
      δ P W ≫ (β_ (G.obj P) (G.obj W)).hom) :
    G.map ((β_ P W).hom ≫ a) ≫ β =
      δ P W ≫ κ ▷ G.obj W ≫ P' ◁ b ≫ (β_ P' W').hom ≫ a' := by
  rw [G.map_comp, Category.assoc, ha]
  rw [reassoc_of% hδ]
  simp only [← MonoidalCategory.tensorHom_def_assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]

private lemma unit_tensor_base_change
    {Cx Cy Cx' Cy' : Type*} [Category* Cx] [Category* Cy]
    [Category* Cx'] [Category* Cy']
    [MonoidalCategory Cx] [MonoidalCategory Cy]
    [MonoidalCategory Cx'] [MonoidalCategory Cy']
    (F R : Cy ⥤ Cx) (F' R' : Cy' ⥤ Cx') (Ga : Cx ⥤ Cx') (Gb : Cy ⥤ Cy')
    (τ : ∀ M N : Cy, R.obj M ⊗ F.obj N ⟶ R.obj (M ⊗ N))
    (τ' : ∀ M N : Cy', R'.obj M ⊗ F'.obj N ⟶ R'.obj (M ⊗ N))
    (β : R ⋙ Ga ⟶ Gb ⋙ R')
    (δa : ∀ M N : Cx, Ga.obj (M ⊗ N) ⟶ Ga.obj M ⊗ Ga.obj N)
    (δb : ∀ M N : Cy, Gb.obj (M ⊗ N) ⟶ Gb.obj M ⊗ Gb.obj N)
    (κ : ∀ N : Cy, Ga.obj (F.obj N) ⟶ F'.obj (Gb.obj N))
    (e : Gb.obj (𝟙_ Cy) ⟶ 𝟙_ Cy')
    (hτ : ∀ M N : Cy,
      Ga.map (τ M N) ≫ β.app (M ⊗ N) ≫ R'.map (δb M N) =
        δa (R.obj M) (F.obj N) ≫ β.app M ▷ Ga.obj (F.obj N) ≫
          R'.obj (Gb.obj M) ◁ κ N ≫ τ' (Gb.obj M) (Gb.obj N))
    (hτ' : ∀ {M M' : Cy'} (φ : M ⟶ M') (N : Cy'),
      R'.map φ ▷ F'.obj N ≫ τ' M' N = τ' M N ≫ R'.map (φ ▷ N))
    (he : ∀ N : Cy, δb (𝟙_ Cy) N ≫ e ▷ Gb.obj N ≫ (λ_ (Gb.obj N)).hom =
      Gb.map (λ_ N).hom) (N : Cy) :
    Ga.map (τ (𝟙_ Cy) N ≫ R.map (λ_ N).hom) ≫ β.app N =
      δa (R.obj (𝟙_ Cy)) (F.obj N) ≫
        (β.app (𝟙_ Cy) ≫ R'.map e) ▷ Ga.obj (F.obj N) ≫
        R'.obj (𝟙_ Cy') ◁ κ N ≫ τ' (𝟙_ Cy') (Gb.obj N) ≫
        R'.map (λ_ (Gb.obj N)).hom := by
  rw [Ga.map_comp, Category.assoc]
  erw [β.naturality]
  change Ga.map (τ (𝟙_ Cy) N) ≫ β.app (𝟙_ Cy ⊗ N) ≫
    R'.map (Gb.map (λ_ N).hom) = _
  rw [← he, R'.map_comp, R'.map_comp]
  rw [reassoc_of% (hτ (𝟙_ Cy) N)]
  rw [← reassoc_of% (hτ' e (Gb.obj N))]
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, whisker_exchange_assoc]

private lemma exceptional_tensor_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] [QuasiCompact f]
    (g : S' ⟶ S) (M N : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map
        (rightDerivedUpperShriekTensorMap f M N) ≫
      (rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app
        (M ⊗ N) ≫
      (rightDerivedUpperShriek A (pullback.snd f g)).map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g M N).hom =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (pullback.fst f g)
      ((rightDerivedUpperShriek A f).obj M)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj N)).hom ≫
      (rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app M ▷
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj N)) ≫
      ((rightDerivedUpperShriek A (pullback.snd f g)).obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M)) ◁
          (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
            (IsPullback.of_hasPullback f g).toCommSq N) ≫
      rightDerivedUpperShriekTensorMap (pullback.snd f g)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj N) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g)
  have hlib := projectionMap_rightDerivedLowerShriekBaseChangeMap A
    (IsPullback.of_hasPullback f g)
  simp only [← leftDerivedUpperStarTensorIso_hom] at hlib
  exact Adjunction.projectionTensorMap_mateEquiv
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A (pullback.snd f g))
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} A) f).app M).app N)
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} A) (pullback.snd f g)).app M).app N)
    (fun φ N ↦ NatTrans.congr_app
      ((projectionMap (ModuleCat.{u + 1} A) (pullback.snd f g)).naturality φ) N)
    (fun M M' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
      (pullback.fst f g) M M').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g N N').hom)
    (fun φ N'' ↦ leftDerivedUpperStarTensorIso_hom_naturality_left g φ N'')
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback f g).toCommSq N)
    (rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g))
    (inv (rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g)))
    (fun M ↦ by simp [NatIso.isIso_inv_app]) hlib M N

private lemma dualizing_tensor_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] [QuasiCompact f]
    (g : S' ⟶ S) (K : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map
        (dualizingComplexTensorMap A f K) ≫
      (rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app K =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (pullback.fst f g)
      (dualizingComplex A f)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).hom ≫
      (dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f g)) ▷
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) ≫
      (dualizingComplex A (pullback.snd f g)) ◁
        (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback f g).toCommSq K) ≫
      dualizingComplexTensorMap A (pullback.snd f g)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) := by
  exact unit_tensor_base_change
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
    (rightDerivedUpperShriek A f)
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor
    (rightDerivedUpperShriek A (pullback.snd f g))
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor
    (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
    (rightDerivedUpperShriekTensorMap f)
    (rightDerivedUpperShriekTensorMap (pullback.snd f g))
    (rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g))
    (fun M N ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
      (pullback.fst f g) M N).hom)
    (fun M N ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g M N).hom)
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback f g).toCommSq N)
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom
    (exceptional_tensor_base_change A f g)
    (Adjunction.projectionTensorMap_naturality_left
      (rightDerivedUpperShriekAdjunction A (pullback.snd f g))
      (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} A) (pullback.snd f g)).app M).app N)
      (fun φ N ↦ NatTrans.congr_app
      ((projectionMap (ModuleCat.{u + 1} A) (pullback.snd f g)).naturality φ) N))
    (leftDerivedUpperStarTensorComparison_leftUnitor_hom (ModuleCat.{u + 1} A) g) K

/-- Arbitrary base change for smooth ambient duality on ordinary unbounded etale
module derived categories, including the dualizing-complex and tensor compatibilities.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/prop-asd-smooth-base-change.md
(blueprint: proposition-exceptional-inverse-image-smooth-morphism--6).

Proof:
1. First supply the missing unbounded refinement argument, rather than invoke the bounded-below
compactification-comparison lemma, whose source explicitly proves only the bounded-below case.
Work throughout with the fixed finite torsion ring $A$ and the unbounded candidates of
[proposition-construction-independence-rf-shriek]. First derive ordinary direct-image composition
without an invertible-prime assumption. The derived adjunctions of
[definition-derived-base-change-map] give, for composable $a,b$, natural bijections $
\operatorname{Hom}(L,Rb_*Ra_*K)= \operatorname{Hom}(b^*L,Ra_*K)= \operatorname{Hom}(a^*b^*L,K)=
\operatorname{Hom}((ba)^*L,K)= \operatorname{Hom}(L,R(ba)_*K)$, using the canonical inverse-image
composition comparison. Yoneda gives the counit-preserving isomorphism $Rb_*Ra_* \cong R(ba)_*$. For
three maps both hom-bijection composites apply the three adjunctions in the same order;
associativity of inverse-image composition makes them equal. Identity maps give the identity
bijection. These composition comparisons require no invertibility condition and are the ones used in
this proof. For a proper refinement $u:T_1 \to T_2$ with $uj_1=j_2$, let $V=T_1 \times_{T_2}X$, $b:V
\hookrightarrow T_1$, $p:V \to X$, and $s:X \hookrightarrow V$. By
[proposition-construction-independence-rf-shriek--7], $s$ identifies $X$ with an open-and-closed
subscheme of $V$ and $ps=1$. Thus $s_!=s_*$ on sheaves (both are the original sheaf on that
component and zero on its complement) and this functor is exact. Extension by zero for nested opens
composes degreewise: inside $X$ both stalks are the stalk of $K$, and elsewhere both are zero. Open
base change from [lem-weil-pbc-etale-shriek-base-change-modules] consequently gives
$b^*j_{1!}K=s_!K$. Proper base change [lem-kun-proper-base-change-torsion-ring] and the
direct-image composition just derived, give the canonical isomorphism $j_2^*Ru_*j_{1!}K \cong
Rp_*s_!K \cong K$ for every unbounded $K$. Define $ \alpha_{u,K}:j_{2!}K \to Ru_*j_{1!}K$ by the
open adjunction of [lemma-affine-space-etale-localization--4], transposing the inverse of this
isomorphism. Over $X$ it is the identity under the displayed comparison. At a geometric point of
$T_2 \setminus X$, proper base change identifies the target with derived direct image on the
fibre of the pullback of $j_{1!}K$. That pullback is zero: the fibre does not meet $j_1(X)$, so
each of its stalk complexes is zero by [lem-weil-pbc-extension-by-zero-stalks] and exact inverse
image. The source stalk is also zero. Exact geometric stalks
[lem-weil-pbc-geometric-point-pullback-stalk], geometric conservativity
[lemma-weil-pbc-geometric-stalk-conservative], and
[lem-weil-pbc-unbounded-derived-iso-cohomology] now prove that $ \alpha_u$ is invertible on all
of $D(X_{ \mathrm{et}},A)$. This tests isomorphisms degree by degree, not equality of derived
morphisms by stalks. For refinements $u,v$, transpose both $ \alpha_{vu}$ and $(Rv_* \alpha_u)
\alpha_v$ under $j_{3!} \dashv j_3^*$: proper-exchange pasting [lem-weil-pbc-mate-pasting]
identifies both restrictions with the inverse of $j_3^*R(vu)_*j_{1!}K \cong K$. The adjunction
bijection proves their equality; the identity case is the same calculation. For base change,
write $g_i:T_i' \to T_i$, $h:X' \to X$, and $z_i:g_i^*j_{i!} \xrightarrow{ \sim}j'_{i!}h^*$ for
the open comparisons, with primes on all pulled-back morphisms understood. The required equation
is $Ru'_*z_1 \circ \operatorname{Ex}_u \circ g_2^* \alpha_u= \alpha_{u'} \circ z_2$. Precompose
with $z_2^{-1}$ and transpose under $j'_{2!} \dashv j_2'{}^*$. The restriction of the left side
is the inverse open restriction of proper exchange for $u'$: the extra exchange for $u$ cancels
its inverse in the definition of $ \alpha_u$, by proper-exchange pasting. This is the
restriction defining the right side. The mate-pasting statement and the adjunction bijection
prove the equation. Finally [remark-base-change-compactification--1] supplies common refinements
and equalizers over an arbitrary Noetherian base (not just over a field), and preserves
refinements under arbitrary base change. Apply $Rr_{2*}$ to $ \alpha_u$ and the same
direct-image composition to compare $Rr_{1*}j_{1!}$ with $Rr_{2*}j_{2!}$. The identity and
composition equations just proved, followed by a common equalizing refinement, make comparisons
independent of choices and give the cocycle law. These are the unbounded, base-change-compatible
comparisons used below. Uses: proposition-construction-independence-rf-shriek,
proposition-construction-independence-rf-shriek--7, lem-weil-pbc-etale-shriek-base-change-modules,
lem-kun-proper-base-change-torsion-ring, lemma-affine-space-etale-localization--4,
lem-weil-pbc-extension-by-zero-stalks, situation-conventions,
lem-weil-pbc-geometric-point-pullback-stalk, lemma-weil-pbc-geometric-stalk-conservative,
lem-weil-pbc-unbounded-derived-iso-cohomology, lem-weil-pbc-mate-pasting,
remark-base-change-compactification--1, definition-derived-base-change-map.

2. Next prove unbounded composition on the same candidates. In a Cartesian square with proper
$p: \overline X \to \overline Y$ and open $v:Y \hookrightarrow \overline Y$, write $V= \overline
X \times_{ \overline Y}Y$, $b:V \hookrightarrow \overline X$ and $p_Y:V \to Y$. The restriction
$p_Y$ is proper by [lem-weil-pbc-proper-fp-permanence](b). For any unbounded $N$ on $V$, define
$ \lambda_{p,v,N}:v_!Rp_{Y*}N \to Rp_*b_!N$ by $v_! \dashv v^*$, transposing the inverse of
proper exchange $v^*Rp_*b_!N \cong Rp_{Y*}b^*b_!N=Rp_{Y*}N$. Over $Y$ this is the identity;
outside $Y$, proper base change [lem-kun-proper-base-change-torsion-ring] makes the target zero,
since the fibre misses $V$ and the pulled-back extension is zero by
[lem-weil-pbc-extension-by-zero-stalks]. The exactness and cohomology detection nodes of Step 1
show $ \lambda$ is invertible for arbitrary $N$, without any truncation. For $X \xrightarrow{f}Y
\xrightarrow{h}S$, choose a compactification $Y \xrightarrow{v} \overline Y \xrightarrow{ \bar
h}S$, and compactify $vf$ as $X \xrightarrow{a} \overline X \xrightarrow{p} \overline Y$, using
[theorem-nagata-s-compactification-theorem--1]. The factorization $X \hookrightarrow V
\xrightarrow{p_Y}Y$ is a compactification of $f$. Substitute $N=(X \hookrightarrow V)_!M$ into $
\lambda$ and apply $R \bar h_*$; nested open extensions compose degreewise and the adjunction-based
direct-image composition in Step 1 identifies the proper factors. This constructs $Rh_!Rf_! \cong
R(hf)_!$. The interchanger $ \lambda$ is the mate, under the open adjunctions, of the inverse
proper-exchange isomorphism just displayed. Therefore its equations for consecutive proper maps,
consecutive open maps, and change of base are respectively the two pasting equations and the
change-of-adjunction equation of [lem-weil-pbc-mate-pasting]; proper-exchange pasting itself
follows by applying that statement to the inverse-image composition comparison of
[definition-derived-base-change-map]. This verifies coherence of the actual maps: after
transposition, each equation is the equality of the pasted inverse-image comparison with the
comparison for the outer rectangle, rather than an inference from invertibility or stalkwise
equality. Explicitly, for consecutive proper maps $P \xrightarrow{p}Q \xrightarrow{q}R$ and an open
$v:W \hookrightarrow R$, write $b_Q:Q_W \hookrightarrow Q$ and $b_P:P_W \hookrightarrow P$ for the
pulled-back opens, and $p_W,q_W$ for the proper restrictions. Under direct-image composition the
interchanger identity is $ \lambda_{qp,v,N}=Rq_* \lambda_{p,b_Q,N} \circ
\lambda_{q,v,Rp_{W*}N}$. For consecutive opens $U \xrightarrow{w}W \xrightarrow{v}R$ and a
proper $p:P \to R$, let $p_W:P_W \to W$ and $c:P_U \hookrightarrow P_W$. The other identity is $
\lambda_{p,vw,N}= \lambda_{p,v,c_!N} \circ v_! \lambda_{p_W,w,N}$. Transposing these displayed
composites under $(vw)_! \dashv(vw)^*$ or $v_! \dashv v^*$ gives, in each case, the inverse of
the proper exchange for the outer rectangle; clauses (1) and (2) of the mate-pasting lemma give
precisely these inverses. For compatibility with $ \alpha_u$, first insert the base-change
equation displayed in Step 1 and then transpose under the remaining open adjunction: both paths
are the inverse proper exchange on the restricted complex $N$. Clause (3) gives equality before
transposition. This also verifies compatibility with a further change of base, using the same
displayed refinement equation and the pasted proper-exchange equality. For three morphisms
expand all candidates into proper and open factors. The two orders of moving open factors past
proper factors use exactly those interchanger equations; the remaining proper reassociations
agree by the hom-bijection associativity checked in Step 1, and the open reassociations are
degreewise identities. Hence both parenthesizations give the same composition map. Changing
compactifications gives the same map by the refinement equation and common refinements of Step
1. This proves the composition and base-change coherence on the unbounded category needed in
Steps 3, 6 and 7, without citing the bounded-below compactification-comparison assertion. Uses:
lemma-affine-space-etale-localization--4, lem-kun-proper-base-change-torsion-ring,
lem-weil-pbc-extension-by-zero-stalks, lem-weil-pbc-geometric-point-pullback-stalk,
situation-conventions, lemma-weil-pbc-geometric-stalk-conservative,
lem-weil-pbc-unbounded-derived-iso-cohomology, theorem-nagata-s-compactification-theorem--1,
lem-weil-pbc-mate-pasting, definition-derived-base-change-map, lem-weil-pbc-proper-fp-permanence.

3. Choose a compactification $f=rj$. Its pullback $f'=r'j'$ is again a compactification. Put
$C_{f,g}:g^*Rf_! \to Rf'_!g'^*$ equal to proper exchange for $r$, followed by $Rr'_*$ of the
inverse of the extension-by-zero comparison. Proper exchange is invertible on every unbounded
$A$-complex by [lem-kun-proper-base-change-torsion-ring]; extension-by-zero base change is
invertible by [lem-weil-pbc-etale-shriek-base-change-modules]. The latter descends degreewise
because inverse image and open extension by zero are exact. Thus $C$ is invertible on the entire
category, without a bounded-below reduction. The unbounded refinement comparisons proved in Step
1 identify the compact-support candidates. Define $ \beta_{f,g,K}$ to be the adjunct under
$Rf'_! \dashv f'^ \times$ of $g^* \epsilon_{f,K} \circ C_{f,g,f^ \times K}^{-1}$. In symbols,
its defining equation is $ \epsilon_{f',g^*K}\,Rf'_!( \beta_{f,g,K})=g^*
\epsilon_{f,K}\,C_{f,g,f^ \times K}^{-1}$. The comparisons used below obey pasting on these same
unbounded categories: proper exchange is the mate of inverse-image composition, so its pasting
follows from [lem-weil-pbc-mate-pasting]; the etale extension comparison is the conjugate
specified in [def-weil-pbc-etale-shriek-base-change-map], so its pasting follows from that same
lemma. For a composite $hv$, expanding $Rf_!$ into proper direct image and open extension, the
two pasted factors are therefore the proper exchange for the composite square and the open
comparison for the composite square. Reassociate the proper factors and use the refinement
comparisons of Step 1 and the composition construction of Step 2; this gives
$C_{hv,g}=C_{h,g}Rv_!$ followed by $Rh'_!C_{v,g_h}$, with the pullback composition
identifications inserted. Horizontal pasting gives $C_{f,gh}=C_{f',h} \circ h^*C_{f,g}$, again
with the inverse-image composition inserted. These are equalities of the canonical comparisons,
not deductions from their invertibility. Uses: proposition-construction-independence-rf-shriek,
lem-kun-proper-base-change-torsion-ring, lem-weil-pbc-etale-shriek-base-change-modules,
lemma-acyclicity-pulled-back-injectives, theorem-existence-exceptional-inverse-image--1,
situation-conventions, lem-weil-pbc-mate-pasting,
def-weil-pbc-etale-shriek-base-change-map, definition-derived-base-change-map,
remark-base-change-compactification--1.

4. Apply the current statement of [lemma-cohomology-projective-line-trace] with its coefficient
ring equal to the given finite commutative ring $A$, $V= \overline X$, $T=S$, $L=j_!M$ and
$K=N$. The compactification has $r$ proper of finite type; its source is Noetherian because it
is finite type over the Noetherian base $S$. Both $M$ and $N$ are arbitrary unbounded ordinary
small-etale complexes, exactly as required by that statement. Its specified ordered projection
map is $Rr_*( \sigma) \circ \mathrm{PF}_r(j_!M,N) \circ \sigma$, from $N \otimes^LRr_*j_!M$ to
$Rr_*(r^*N \otimes^Lj_!M)$; all three factors are isomorphisms. Use the open comparison
$j_!(j^*r^*N \otimes^LM) \cong r^*N \otimes^Lj_!M$ to obtain the canonical compact-support map
$N \otimes^LRf_!M \to Rf_!(f^*N \otimes^LM)$. Thus its inverse has precisely the order used by
the tensor-map counit in Steps 5 and 9. The open comparison can equivalently be written $j_!(M
\otimes^Lj^*N) \cong j_!M \otimes^LN$, with $N$ here a complex on the ambient scheme; the two
orders are related by the signed tensor symmetries specified in the cited proper projection
statement. The underived comparison $j_!(M \otimes j^*N) \to j_!M \otimes N$ is defined by the
open adjunction [lemma-affine-space-etale-localization--4]: its restriction is the identity on $M
\otimes j^*N$. Applying it termwise gives the tensor-complex comparison. For its derived form use
flat K-flat representatives [lem-pc-kflat-resolution]; by [lem-weil-pbc-extension-by-zero-stalks],
at a geometric stalk inside the open it is identity on the total tensor complex, and outside it
both sides are zero. The stalk tensor isomorphism [lem-pod-etale-stalk-tensor-scalar] and
exactness of geometric stalks [lem-weil-pbc-geometric-point-pullback-stalk] show that these
degreewise identifications give the derived comparison; [lem-kun-inverse-image-monoidal]
supplies its restriction inside the open. For precision, check the open base-change square
before passing to the derived category: choose flat K-flat representatives, whose inverse images
remain flat K-flat by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Open extension
preserves flatness and K-flatness: its stalks are the original flat modules or zero, and
tensoring its extended complex with an acyclic complex is the extension of the tensor with the
restricted acyclic complex, which is acyclic by exactness of restriction and extension. In each
degree both composites in the square send a tensor of germs inside the open to that same tensor
of pulled-back germs; outside the open both are zero. Faithfulness of geometric stalks on maps
of sheaves gives equality of these chain maps degree by degree (the image of their difference
has zero stalks, so conservativity applied to its map to zero makes that image zero).
Consequently the square commutes after localization at quasi-isomorphisms. No faithfulness of
stalk functors on derived morphisms is asserted. For $r$,
[lem-weil-pbc-ringed-exchange-tensor-coherence], applied to constant $A$-ringed etale topoi,
gives the projection/base-change square for $ \mathrm{PF}_r(j_!M,N)$ in the order $(j_!M,N)$.
Conjugating this square by the two canonical tensor symmetries gives the square for the ordered
map of [lemma-cohomology-projective-line-trace]. Indeed on K-flat tensor complexes each symmetry
sends a homogeneous tensor of degrees $(p,q)$ to $(-1)^{pq}$ times the swapped tensor. Exact
pullback preserves those degrees and that scalar, so its tensor comparison commutes with the
signed swaps as a chain-map equality. Naturality of symmetry with respect to the exchange map
gives the other side of the conjugated square. Pasting this square with the open one proves that
the compact-support projection formula commutes with $C_{f,g}$, on arbitrary complexes. Uses:
lemma-cohomology-projective-line-trace, lem-pc-kflat-resolution,
lem-pod-etale-stalk-tensor-scalar, lem-kun-inverse-image-monoidal,
lemma-acyclicity-pulled-back-injectives, lem-weil-pbc-ringed-exchange-tensor-coherence,
lemma-weil-pbc-geometric-stalk-conservative, lem-weil-pbc-extension-by-zero-stalks,
lem-weil-pbc-geometric-point-pullback-stalk, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lemma-affine-space-etale-localization--4.

5. For $q: \mathbf P^1_S \to S$, apply [lem-asd-ordinary-finite-p1-adjunction] with the given
finite commutative ring $A$ and integer $N$: $NA=0$ and $N$ is invertible on $S$. This input
explicitly states an adjunction on the ordinary unbounded small-etale categories, using $L_P(1)=
\mu_{N,P} \otimes_{ \mathbf Z/N}A$ and its Kummer-normalized trace $t_q=
\operatorname{pr}_2b_q^{-1}$. No pro-etale inverse-limit coefficient object is substituted.
Choose the compactification $(1,q)$; thus $Rq_!=Rq_*$. Compare its supplied right adjoint
$G_q=q^*(-) \otimes^LL_P(1)[2]$ with $q^ \times$ by the unique adjunction-preserving
isomorphism, so the counit is exactly $ \epsilon_{q,K}=(1_K \otimes t_q) \mathrm{PF}^{-1}$. Use
the same counit-preserving comparison on the pulled-back projective line. The finite-twist
pullback of [lem-asd-etale-finite-twist-pullback] supplies $ \rho:g_P^*L_P(1) \cong L_{P'}(1)$.
Let $B=Rq'_*( \rho[2]) \operatorname{Ex}_{q,L_P(1)[2]}$. The ordinary finite P1 input states
compatibility of its decomposition and trace with this canonical exchange. More explicitly that
decomposition compatibility reads $B\,g^*b_q=b_{q'}( \rho_S[2] \oplus1)$, where $
\rho_S:g^*L_S(1) \cong L_{S'}(1)$. Multiply by the inverse decomposition and project to the
second summand: $t_{q'}B= \operatorname{pr}_2( \rho_S[2] \oplus1)(g^*b_q)^{-1}=g^*(
\operatorname{pr}_2b_q^{-1})=g^*t_q$. Thus this is an equality of the specified coefficient
traces and canonical maps, not an existence-only identification of objects. Inverse-image
composition, tensor and $ \rho$ give an isomorphism $a:g_P^*G_qK \cong G_{q'}g^*K$. Substitute
the specified counit formulas. Step 4 identifies the projection factors, and the displayed
coefficient-trace equality identifies the last factors, giving $ \epsilon_{q',g^*K}Rq'_!(a)=g^*
\epsilon_{q,K}C_{q,g,G_qK}^{-1}$. Step 3 defines $ \beta$ by exactly this equation. The
adjunction bijection identifies $a$ with $ \beta_{q,g,K}$ under the counit-preserving
right-adjoint comparisons. Consequently this canonical mate is invertible. Uses:
lem-asd-ordinary-finite-p1-adjunction, lem-asd-etale-finite-twist-pullback,
theorem-existence-exceptional-inverse-image--1.

6. Use the exact etale compact-support and exchange normalization of
[lem-asd-etale-compact-support-normalization]. Let $j: \mathbf A^1_S \hookrightarrow \mathbf
P^1_S$. Compose $j_! \dashv j^*$ with the projective-line adjunction. The open comparison is the
comparison of left adjoints specified in [def-weil-pbc-etale-shriek-base-change-map]; its mate
is ordinary restriction comparison. Thus its counit commutes with the pullback square. The
pasting identity along adjunctions [lem-weil-pbc-mate-pasting] identifies the mate for $p_1=qj$
with the composite of this restriction comparison and the isomorphism in Step 5. The resulting
right adjoint is $p_1^*(1)[2]$. For $d=0$ use the identity adjunction. For $d+1$ factor
$p_{d+1}$ as an affine-line projection followed by $p_d$; Step 2 identifies the composite left
adjoint, and the same mate-pasting identity identifies its exchange with the composite of the
already invertible exchanges. The twist/pullback and tensor identifications of
[lem-asd-etale-finite-twist-pullback] give $p_{d+1}^*(d+1)[2d+2]$. This induction uses the
explicit composite adjunction, and compares its right adjoint directly with the ambient right
adjoint of [theorem-existence-exceptional-inverse-image--1] by the unique counit-preserving
comparison. The imported affine-space adjunction with its pro-etale twist dependency is not used.
Uses: lemma-affine-space-etale-localization--4, def-weil-pbc-etale-shriek-base-change-map,
lem-weil-pbc-mate-pasting, lem-asd-etale-finite-twist-pullback,
theorem-existence-exceptional-inverse-image--1, lem-asd-etale-compact-support-normalization.

7. Fix the etale normalization before applying locality. Apply
[lem-asd-etale-compact-support-normalization] to every separated finite-type etale map $u$. It
identifies the compactification-defined $Ru_!$ with the degreewise exact sum-extension functor,
preserves its evaluation counit, and states the equation $(c_{u'}h^*)C_{u,g}=C^
\Sigma_{u,g}(g^*c_u)$ for precisely the proper/open comparison used in Step 3. Thus in the exact
etale realization $C_{u,g}$ is the inverse of the sheaf comparison of
[def-weil-pbc-etale-shriek-base-change-map], including the normalization of the map, not just
its endpoints. Transport the adjunctions by their counit-preserving comparisons. For a separated
finite-type etale map $u:U \to X$, the exact adjunction $u_! \dashv u^*$ in
[lemma-affine-space-etale-localization--4] and the comparison
[lem-weil-pbc-etale-shriek-base-change-modules] have mate the canonical inverse-image
composition isomorphism. Indeed the comparison is defined by conjugating the ordinary
inverse-image/direct-image exchange [def-weil-pbc-etale-shriek-base-change-map]; its defining
counit equation is exactly the equation of Step 3 after transposition. Pasting along the two
adjunctions [lem-weil-pbc-mate-pasting] proves that under $u^*f^ \times \cong(fu)^ \times$ and
its primed analogue, $u'^* \beta_{f,g,K}$ is the mate for the pasted square $(fu,g)$, with the
canonical pullback composition inserted. This proves locality of the actual map, rather than
merely locality of its endpoints. For base restriction, write $a:S_0 \hookrightarrow S$,
$a_X:X_0 \hookrightarrow X$, $a':S'_0 \hookrightarrow S'$ and $a'_X:X'_0 \hookrightarrow X'$.
Here $fa_X=af_0$. Compose the exact etale adjunctions with the compact-support adjunctions: both
left adjoints are identified by $Rf_!a_{X!}=Ra_!Rf_{0!}$ from the unbounded compact-support
composition proved in Step 2. Their right adjoints consequently identify $a_X^*f^ \times$ with
$f_0^ \times a^*$, and the primed equality gives the other restriction comparison. Pasting their
counit equations identifies these comparisons with the mates for base changes $a$ and $a'$: the
left-adjoint equality is the extension-by-zero comparison from Step 3 with the open base
restriction inserted. Horizontal pasting from Step 3 reads $C_{f,ga'}=C_{f',a'}\,a'{}^*C_{f,g}$
and also $C_{f,ag_0}=C_{f_0,g_0}\,g_0^*C_{f,a}$. Since $ga'=ag_0$, apply part (1) of the
mate-pasting lemma to their inverses. The first mate is the etale restriction comparison
composed with $a'_X{}^* \beta_{f,g,K}$; the second is $ \beta_{f_0,g_0,a^*K}$ composed with the
unprimed restriction comparison. Their equality identifies the restricted canonical map with the
chart map, as required. Uses: lemma-affine-space-etale-localization--4,
lem-weil-pbc-etale-shriek-base-change-modules, def-weil-pbc-etale-shriek-base-change-map,
lem-weil-pbc-mate-pasting, lem-asd-etale-compact-support-normalization.

8. Apply [proposition-exceptional-inverse-image-smooth-morphism] at each point of $X$. After an
affine open restriction in the base, choose an affine open $U \subseteq X$ and an etale $e:U \to
\mathbf A^d_{S_0}$ with $fu=p_de$. The relative dimension is $d$, since the etale factor has
relative dimension zero and $f$ has pure relative dimension $d$. The chart inclusion $u$ is
separated and of finite type: it is an open immersion, and it is quasi-compact because $X$ is
Noetherian. The map $e$ is separated since $U$ and $ \mathbf A^d_{S_0}$ are affine: on rings its
diagonal is given by the surjection $B \otimes_R B \to B$, $b \otimes b' \mapsto bb'$. It is locally
of finite presentation since it is etale, and quasi-compact by
[lem-weil-pbc-qcqs-morphism-permanence](1), since $U$ is affine and $ \mathbf A^d_{S_0}$ is
quasi-separated. Hence $e$ is of finite type. They are compactifiable, as are their composites,
by [theorem-nagata-s-compactification-theorem--1]. After arbitrary base change the corresponding
charts still cover $X'$. Steps 6 and 7 identify the restriction of $ \beta_{f,g,K}$ on each chart
with etale inverse image of the affine-space isomorphism. Thus it is an isomorphism on every chart.
Exact inverse image [situation-conventions] commutes with cohomology; the kernel
and cokernel of each cohomology map vanish on that etale covering, so their sections vanish by
the sheaf axiom. Equivalently this is [lem-weil-pbc-etale-cover-detects-iso] applied to the
underlying abelian cohomology sheaves. Hence every cohomology map is invertible globally, and
[lem-weil-pbc-unbounded-derived-iso-cohomology] proves that $ \beta_{f,g,K}$ is invertible in
the unbounded derived category. Uses: proposition-exceptional-inverse-image-smooth-morphism,
theorem-nagata-s-compactification-theorem--1, lemma-affine-space-etale-localization--4,
lem-weil-pbc-unbounded-derived-iso-cohomology, situation-conventions,
lem-weil-pbc-etale-cover-detects-iso, lem-weil-pbc-qcqs-morphism-permanence.

9. At $K=A_S$, exact inverse image preserves the constant coefficient unit, so Step 8 gives
$b:g'^* \omega_f \cong \omega_{f'}$. To check the tensor square, recall the meaning of the
canonical tensor morphism: it is the transpose of $Rf_!(f^*K \otimes^L \omega_f) \xrightarrow{
\mathrm{PF}^{-1}}K \otimes^LRf_! \omega_f \xrightarrow{1 \otimes \epsilon_{f,A}}K$. Transpose
both proposed paths under $Rf'_! \dashv f'^ \times$. The transpose of the upper path is the
pullback of this displayed composite preceded by $C^{-1}$. The transpose of the lower path is
the primed projection inverse followed by $1 \otimes Rf'_!b$ and $1 \otimes \epsilon_{f',A}$.
Step 4 identifies their projection-formula factors; the defining equation of $b$ from Step 3
identifies their final factors, since $ \epsilon_{f',A}Rf'_!b=g^* \epsilon_{f,A}C^{-1}$.
Naturality of $C$ and tensor lets these substitutions be made in the composite. The transposes
are equal, so the adjunction bijection proves the displayed tensor compatibility.
[proposition-exceptional-inverse-image-smooth-morphism] ensures these canonical tensor maps are the
claimed isomorphisms. Uses: proposition-exceptional-inverse-image-smooth-morphism,
theorem-existence-exceptional-inverse-image--1, lem-kun-inverse-image-monoidal,
situation-conventions.
-/
theorem smooth_exceptional_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X S S' : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] [IsNoetherian S']
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
    (f : X ⟶ S) [IsSeparated f] [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (g : S' ⟶ S) :
    (∀ K : DerivedCategoryModule A S, IsIso (smoothExceptionalBaseChangeMap A f g K)) ∧
    IsIso (smoothDualizingBaseChangeMap A f g) ∧
    ∀ K : DerivedCategoryModule A S,
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map
          (smoothTensorDualityMap A f
            (isIso_projectionMap_of_finite A f) K) ≫
        smoothExceptionalBaseChangeMap A f g K =
      (smoothDualityTensorBaseChangeIso A f g K).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
          ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj
            ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))).map
          (smoothDualizingBaseChangeMap A f g) ≫
        smoothTensorDualityMap A (pullback.snd f g)
          (isIso_projectionMap_of_finite A (pullback.snd f g))
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) := by
  have hNS : IsUnit (N : Γ(S, ⊤)) := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro s hs
    simpa only [map_natCast] using hInvertible s
  have : HasInvertibleExponent A S := ⟨N, hN, hA, hNS⟩
  have : HasInvertibleExponent A X := HasInvertibleExponent.of_hom f
  have hBC := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    A f d (IsPullback.of_hasPullback f g)
  have := isIso_rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g)
  have hMap (K : DerivedCategoryModule A S) :
      smoothExceptionalBaseChangeMap A f g K =
        (rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app K := by
    symm
    simpa only [smoothExceptionalBaseChangeMap, rightDerivedUpperShriekBaseChangeMap,
      NatIso.isIso_inv_app, Functor.id_obj, Functor.comp_obj] using
      mate_app_eq
      (rightDerivedUpperShriekAdjunction A f)
      (rightDerivedUpperShriekAdjunction A (pullback.snd f g))
      (inv (rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f g))) K
  refine ⟨?_, ?_, ?_⟩
  · intro K
    rw [hMap]
    infer_instance
  · unfold smoothDualizingBaseChangeMap
    rw [hMap]
    infer_instance
  · intro K
    let := derivedBraidedCategory A X
    let := derivedBraidedCategory A (pullback f g)
    have hδ := leftDerivedUpperStar_map_braiding_hom_δ (ModuleCat.{u + 1} A)
      (pullback.fst f g)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)
      (dualizingComplex A f)
    have ht := braided_tensor_square
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)
      (dualizingComplex A f)
      ((rightDerivedUpperShriek A f).obj K)
      ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
      (dualizingComplex A (pullback.snd f g))
      ((rightDerivedUpperShriek A (pullback.snd f g)).obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
      (dualizingComplexTensorMap A f K)
      (dualizingComplexTensorMap A (pullback.snd f g)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
      (dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f g))
      (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback f g).toCommSq K)
      ((rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app K)
      (fun M N ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
        (pullback.fst f g) M N).hom)
      (dualizing_tensor_base_change A f g K) hδ
    have hφ := smooth_tensor_map_eq A f K
    have hφ' := smooth_tensor_map_eq A (pullback.snd f g)
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)
    simpa only [hφ, hφ', dualizingComplexTensorMap,
      smoothDualityTensorBaseChangeIso, smoothSquarePullbackIso,
      smoothDualizingBaseChangeMap, hMap, dualizingComplexBaseChangeMap,
      derivedSquareUpperStarIsoInvApp, derivedSquareUpperStarIso,
      Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, NatTrans.comp_app, Iso.app_hom,
      derivedTensor, curriedTensor,
      Functor.mapIso_hom, Category.assoc] using ht

end AlgebraicGeometry.Etale

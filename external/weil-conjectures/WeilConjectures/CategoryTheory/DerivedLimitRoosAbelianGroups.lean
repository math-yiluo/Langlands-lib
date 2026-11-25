/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RoosAcyclicResolution
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.CategoryTheory.InjectiveTowerEmbedding
import WeilConjectures.CategoryTheory.InjectiveSplitTower

/-!
# Roos computation of derived limits of abelian groups

Source: Stacks Project, More on Algebra, Lemma 15.88.1, Tag 07KW
(blueprint: lem-pc-derived-limit-roos-abelian-groups).

## Main statements

- `roosTowerEnoughInjectives`: the tower category has enough injectives.
- `roosLimitAdditive`: inverse limit is additive.
- `derivedLimitRoosAbelianGroups`: inverse limit is left exact, naturally the kernel of
  the Roos map; its first right derived functor is naturally the cokernel and higher
  right derived functors vanish.

We use the Mathlib functor category for towers, reindexing positive integers by `n + 1`.
All groups lie in an arbitrary universe `u`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The displayed map `1 - s` of Stacks Project, Tag 07KW, Lemma 15.88.1:
the transition endomorphism `towerTransitionEndomorphism` (Tag 08TC) of the tower `A`,
whose `n`th coordinate is `x n - f n (x (n + 1))`, with `f n` the transition of `A`
(blueprint: lem-pc-derived-limit-roos-abelian-groups). -/
noncomputable abbrev roosMap (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (∏ᶜ fun n : ℕ => A.obj (Opposite.op n)) ⟶
      (∏ᶜ fun n : ℕ => A.obj (Opposite.op n)) :=
  towerTransitionEndomorphism (K := fun n : ℕ => A.obj (Opposite.op n))
    (fun n => A.map (homOfLE (Nat.le_succ n)).op)

/-- The enough-injectives clause of Stacks Project, Tag 07KW, Lemma 15.88.1 setup
(blueprint: lem-pc-derived-limit-roos-abelian-groups).

Proof (node step 1): apply `lem-pc-tower-enough-injectives` to the abelian tower
category of `lem-pc-tower-abelian`. Every tower embeds in a tower of injective
abelian groups with split-surjective transitions; compatible lifts are constructed
successively, extending at each stage into the injective kernel of the transition.
Thus every tower admits a monomorphism to an injective tower. 
(blueprint: lem-pc-tower-enough-injectives)
-/
theorem roosTowerEnoughInjectives : EnoughInjectives (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) := by
  constructor
  intro A
  obtain ⟨I, i, hi, hI, hp⟩ := tower_injective_embedding A
  exact ⟨⟨I, injective_of_injective_split_tower I hI hp, i, hi⟩⟩

attribute [local instance] roosTowerEnoughInjectives

/-- The additivity clause of Stacks Project, Tag 07KW, Lemma 15.88.1 setup
(blueprint: lem-pc-derived-limit-roos-abelian-groups).

Proof (node step 1): use `lem-pc-tower-limit-left-exact`. Finite biproducts of towers
are levelwise, and compatible tuples in a finite biproduct are pairs of compatible
tuples. Inverse limit therefore preserves finite biproducts, hence is additive. -/
theorem roosLimitAdditive :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive := by
  constructor
  intro A B f g
  apply limit.hom_ext
  intro n
  simp only [lim_map, limMap_π, Preadditive.add_comp, NatTrans.app_add,
    Preadditive.comp_add]

attribute [local instance] roosLimitAdditive

private theorem roos_natural {A B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : A ⟶ B) :
    roosMap A ≫ Limits.Pi.map (fun n : ℕ ↦ φ.app (Opposite.op n)) =
      Limits.Pi.map (fun n : ℕ ↦ φ.app (Opposite.op n)) ≫ roosMap B := by
  exact (towerTransitionEndomorphism_natural_backward _ _ _
    (fun n ↦ (φ.naturality (homOfLE (Nat.le_succ n)).op).symm)).symm

private noncomputable def roosInclusion (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    limit A ⟶ ∏ᶜ fun n : ℕ ↦ A.obj (Opposite.op n) :=
  Pi.lift (fun n ↦ limit.π A (Opposite.op n))

private theorem roosInclusion_zero (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    roosInclusion A ≫ roosMap A = 0 := by
  apply Pi.hom_ext
  intro n
  simp [roosInclusion, roosMap, towerTransitionEndomorphism, towerProductShift,
    Category.assoc]

private noncomputable def roosKernelCone (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : Cone A where
  pt := kernel (roosMap A)
  π := NatTrans.ofOpSequence
    (fun n ↦ kernel.ι (roosMap A) ≫ Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) n)
    (by
      intro n
      have h := congrArg
        (fun f ↦ f ≫ Pi.π (fun n : ℕ ↦ A.obj (Opposite.op n)) n)
        (kernel.condition (roosMap A))
      have h' : kernel.ι (roosMap A) ≫ Pi.π _ n -
          kernel.ι (roosMap A) ≫ Pi.π _ (n + 1) ≫
            A.map (homOfLE (Nat.le_succ n)).op = 0 := by
        simpa [roosMap, towerTransitionEndomorphism, towerProductShift,
          Category.assoc] using h
      simpa using (sub_eq_zero.mp h'))

private noncomputable def roosKernelIso (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    limit A ≅ kernel (roosMap A) where
  hom := kernel.lift (roosMap A) (roosInclusion A) (roosInclusion_zero A)
  inv := limit.lift A (roosKernelCone A)
  hom_inv_id := by
    apply limit.hom_ext
    intro n
    cases n using Opposite.rec
    simp [roosKernelCone, roosInclusion, Category.assoc]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι (roosMap A))).mp
    apply Pi.hom_ext
    intro n
    simp [roosKernelCone, roosInclusion, Category.assoc]

private theorem roosKernelIso_natural {A B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : A ⟶ B)
    (h : roosMap A ≫ Limits.Pi.map (fun n : ℕ ↦ φ.app (Opposite.op n)) =
      Limits.Pi.map (fun n : ℕ ↦ φ.app (Opposite.op n)) ≫ roosMap B) :
    limMap φ ≫ (roosKernelIso B).hom = (roosKernelIso A).hom ≫
      kernel.map (roosMap A) (roosMap B)
        (Limits.Pi.map (fun n : ℕ ↦ φ.app (Opposite.op n)))
        (Limits.Pi.map (fun n : ℕ ↦ φ.app (Opposite.op n))) h := by
  apply (cancel_mono (kernel.ι (roosMap B))).mp
  apply Pi.hom_ext
  intro n
  simp [roosKernelIso, roosInclusion, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Roos computation, naturally in the tower, of Stacks Project, Tag 07KW,
Lemma 15.88.1 (blueprint: lem-pc-derived-limit-roos-abelian-groups).

Proof, following the node:
1. The tower category is abelian (`lem-pc-tower-abelian`, here Mathlib's functor-category
instance), has enough injectives (`lem-pc-tower-enough-injectives`), and inverse limit
is additive and left exact (`lem-pc-tower-limit-left-exact`). Its right derived functors
are those of `def-sp-left-exact-additive`.
2. Compatible tuples are exactly the kernel of `1 - s`; this identification is natural.
3. Following Tag 07KW, form `B_n = A_n ⊕ ... ⊕ A_1` and
`C_n = A_{n-1} ⊕ ... ⊕ A_1`, with projection transitions and `C_1 = 0`.
The successive-transition embedding `A_n → B_n` and the difference map `B_n → C_n`
form a levelwise short exact sequence. Injectivity is checked at the first coordinate;
the kernel consists of successive-transition tuples; surjectivity follows by downward
recursion starting with `x_n = 0`. The levelwise universal properties give a short exact
sequence of towers. Both limits are the product of the `A_n`, and the induced map is
`1 - s`. Tower morphisms act componentwise on this construction.
4. The towers `B` and `C` have surjective transitions and so are limit-acyclic by
`lem-pc-tower-surjective-lim-acyclic`. Apply the long exact sequence of
`lem-weil-pbc-horseshoe-delta-functor`, using `R⁰ lim = lim` from
`def-sp-left-exact-additive`: its beginning identifies `R¹ lim A` with the cokernel
of `1 - s`, and its higher terms give `R^q lim A = 0` for `q ≥ 2`.
Naturality follows from the componentwise construction and natural connecting maps.

The witnesses `e₀` and `e₁` are chosen for all towers before the naturality condition.
The witness `h` is the commutative square defining the induced kernel/cokernel maps. -/
theorem derivedLimitRoosAbelianGroups :
    PreservesFiniteLimits
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) ∧
    ∃ (e₀ : ∀ A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}, limit A ≅ kernel (roosMap A))
      (e₁ : ∀ A : ℕᵒᵖ ⥤ AddCommGrpCat.{u},
        ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).obj A ≅
          cokernel (roosMap A)),
      (∀ (A B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (φ : A ⟶ B),
        ∃ h : roosMap A ≫ Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)) =
            Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)) ≫ roosMap B,
          limMap φ ≫ (e₀ B).hom = (e₀ A).hom ≫
            kernel.map (roosMap A) (roosMap B)
              (Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)))
              (Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n))) h ∧
          ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).map φ ≫
              (e₁ B).hom = (e₁ A).hom ≫
            cokernel.map (roosMap A) (roosMap B)
              (Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n)))
              (Limits.Pi.map (fun n : ℕ => φ.app (Opposite.op n))) h) ∧
      ∀ (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (q : ℕ), 2 ≤ q →
        IsZero (((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived q).obj A) := by
  classical
  let F := (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})
  obtain ⟨U, V, i, p, w, hS, eU, eV, hp, hac⟩ := exists_roos_acyclic_resolution.{u}
  let S (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    ShortComplex.mk (i.app A) (p.app A) (w A)
  obtain ⟨⟨G, hadd, δ, hmono, hmid, hright, hleft, hnat⟩, hG, _⟩ :=
    exists_horseshoe_rightDerived_deltaFunctor F
  dsimp only at hG
  subst G
  let eB (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
      (F.rightDerived 0).obj (U.obj A) ≅ roosProductFunctor.obj A :=
    F.rightDerivedZeroIsoSelf.app (U.obj A) ≪≫ eU.app A
  let eC (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
      (F.rightDerived 0).obj (V.obj A) ≅ roosProductFunctor.obj A :=
    F.rightDerivedZeroIsoSelf.app (V.obj A) ≪≫ eV.app A
  let d (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
      roosProductFunctor.obj A ⟶ (F.rightDerived 1).obj A :=
    (eC A).inv ≫ δ (S A) (hS A) 0
  have hb (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
      (F.rightDerived 0).map (p.app A) ≫ (eC A).hom =
        (eB A).hom ≫ roosMap A := by
    change (F.rightDerived 0).map (p.app A) ≫
      F.rightDerivedZeroIsoSelf.hom.app (V.obj A) ≫ eV.hom.app A =
        (F.rightDerivedZeroIsoSelf.hom.app (U.obj A) ≫ eU.hom.app A) ≫ roosMap A
    rw [← Category.assoc, F.rightDerivedZeroIsoSelf.hom.naturality]
    simpa only [F, roosMap, roosProductDifferential, Category.assoc] using
      congrArg (fun f ↦ F.rightDerivedZeroIsoSelf.hom.app (U.obj A) ≫ f) (hp A)
  have hd (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : roosMap A ≫ d A = 0 := by
    obtain ⟨hz, _⟩ := hright (S A) (hS A) 0
    dsimp only [d]
    rw [← cancel_epi (eB A).hom, ← Category.assoc, ← hb A]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, comp_zero] using hz
  have he (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
      (ShortComplex.mk (roosMap A) (d A) (hd A)).Exact := by
    obtain ⟨hz, hex⟩ := hright (S A) (hS A) 0
    let e : ShortComplex.mk ((F.rightDerived 0).map (p.app A))
        (δ (S A) (hS A) 0) hz ≅ ShortComplex.mk (roosMap A) (d A) (hd A) :=
      ShortComplex.isoMk (eB A) (eC A) (Iso.refl _)
        (hb A).symm (by simp [d])
    exact ShortComplex.exact_of_iso e hex
  have hepi (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : Epi (d A) := by
    obtain ⟨hz, hex⟩ := hleft (S A) (hS A) 0
    have hz' : (F.rightDerived 1).map (i.app A) = 0 :=
      (hac A 1 (by omega)).1.eq_of_tgt _ _
    have : Epi (δ (S A) (hS A) 0) := hex.epi_f hz'
    dsimp only [d]
    infer_instance
  let e₁ (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
      (F.rightDerived 1).obj A ≅ cokernel (roosMap A) := by
    haveI := hepi A
    let e := IsColimit.coconePointUniqueUpToIso (he A).gIsCokernel
      (cokernelIsCokernel (roosMap A))
    exact e
  have hde (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
      d A ≫ (e₁ A).hom = cokernel.π (roosMap A) := by
    have := hepi A
    exact IsColimit.comp_coconePointUniqueUpToIso_hom (he A).gIsCokernel
      (cokernelIsCokernel (roosMap A)) WalkingParallelPair.one
  refine ⟨inferInstance, roosKernelIso, e₁, ?_, ?_⟩
  · intro A B φ
    refine ⟨roos_natural φ, roosKernelIso_natural φ _, ?_⟩
    let t : S A ⟶ S B :=
      { τ₁ := φ
        τ₂ := U.map φ
        τ₃ := V.map φ
        comm₁₂ := i.naturality φ
        comm₂₃ := p.naturality φ }
    have hc : (F.rightDerived 0).map (V.map φ) ≫ (eC B).hom =
        (eC A).hom ≫ roosProductFunctor.map φ := by
      change (F.rightDerived 0).map (V.map φ) ≫
        F.rightDerivedZeroIsoSelf.hom.app (V.obj B) ≫ eV.hom.app B =
          (F.rightDerivedZeroIsoSelf.hom.app (V.obj A) ≫ eV.hom.app A) ≫
            roosProductFunctor.map φ
      rw [← Category.assoc, F.rightDerivedZeroIsoSelf.hom.naturality]
      simpa only [F, Functor.comp_map, Category.assoc] using
        congrArg (fun f ↦ F.rightDerivedZeroIsoSelf.hom.app (V.obj A) ≫ f)
          (eV.hom.naturality φ)
    have hn : d A ≫ (F.rightDerived 1).map φ = roosProductFunctor.map φ ≫ d B := by
      rw [← cancel_epi (eC A).hom]
      simp only [d, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← hc]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact hnat (S A) (S B) (hS A) (hS B) t 0
    have := hepi A
    apply (cancel_epi (d A)).mp
    change d A ≫ (F.rightDerived 1).map φ ≫ (e₁ B).hom = _
    rw [← Category.assoc, hn]
    simp only [Category.assoc, hde]
    rw [← Category.assoc, hde]
    simp [cokernel.map, roosProductFunctor]
  · intro A q hq
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    obtain ⟨hz, hex⟩ := hleft (S A) (hS A) n
    exact hex.isZero_X₂ ((hac A n (by omega)).2.eq_of_src _ _)
      ((hac A (n + 1) (by omega)).1.eq_of_tgt _ _)

end CategoryTheory

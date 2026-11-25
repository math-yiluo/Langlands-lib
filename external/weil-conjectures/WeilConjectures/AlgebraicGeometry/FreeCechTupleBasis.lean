/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import WeilConjectures.AlgebraicGeometry.PowerSetComplexContractible
public import Mathlib.LinearAlgebra.DFinsupp

/-! # Tuple generators of the evaluated free Čech object

Source: Stacks Project, Tags 03AT and 03F5, the degreewise direct-sum decomposition.
(blueprint: lem-weil-pbc-free-cech-tuple-basis)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite Simplicial

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (ι : Type u) (U₀ : X.Etale) (U : ι → X.Etale)
  (f : ∀ i : ι, U i ⟶ U₀) (O : X.Etaleᵒᵖ ⥤ RingCat.{u}) (W : X.Etale)

/-- The simplicial free presheaf module attached to the family.
Source: Stacks Project, Tag 03F5 (blueprint: lem-weil-pbc-free-cech-tuple-basis). -/
noncomputable abbrev freeCechModule : SimplicialObject (PresheafOfModules.{u} O) :=
  (FormalCoproduct.mk ι fun i ↦ Over.mk (f i)).cech ⋙
    (FormalCoproduct.eval (Over U₀) (PresheafOfModules.{u} O)).obj
      (Over.forget U₀ ⋙ yoneda ⋙ PresheafOfModules.free O)

/-- Lifts of a fixed map to the base, retaining their family indices.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-free-cech-tuple-basis). -/
abbrev freeCechLifts (φ : W ⟶ U₀) := Σ i : ι, {g : W ⟶ U i // g ≫ f i = φ}

/-- The generator associated to a tuple of lifts: map to their product in the over
category, take its free generator, and inject into the coproduct summand.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-free-cech-tuple-basis). -/
noncomputable def freeCechTupleGenerator (n : ℕ) (φ : W ⟶ U₀)
    (x : Fin (n + 1) → freeCechLifts X ι U₀ U f W φ) :
    ((freeCechModule X ι U₀ U f O).obj (op ⦋n⦌)).obj (op W) :=
  let i : Fin (n + 1) → ι := fun a ↦ (x a).1
  let g : Over.mk φ ⟶ ∏ᶜ (fun a ↦ Over.mk (f (i a))) :=
    Pi.lift (fun a ↦ Over.homMk (x a).2.1 (x a).2.2)
  ((Sigma.ι
    (fun j : Fin (n + 1) → ι ↦
      (PresheafOfModules.free O).obj
        (yoneda.obj ((∏ᶜ (fun a ↦ Over.mk (f (j a)))).left))) i).app (op W))
    (ModuleCat.freeMk g.left)

/-- Linear extension of the tuple generators, first within each block and then over
all maps to the base.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-free-cech-tuple-basis). -/
noncomputable def freeCechTupleMap (n : ℕ) :
    (Π₀ φ : W ⟶ U₀,
      Algebra.powerSetComplexObject (O.obj (op W)) (freeCechLifts X ι U₀ U f W φ) n) →ₗ[
        O.obj (op W)] ((freeCechModule X ι U₀ U f O).obj (op ⦋n⦌)).obj (op W) := by
  classical
  exact DFinsupp.lsum ℕ (fun φ ↦
    Finsupp.lift _ _ _ (freeCechTupleGenerator X ι U₀ U f O W n φ))

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the linear extension on one block generator.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-free-cech-tuple-basis). -/
@[simp]
theorem freeCechTupleMap_single [DecidableEq (W ⟶ U₀)] (n : ℕ) (φ : W ⟶ U₀)
    (x : Fin (n + 1) → freeCechLifts X ι U₀ U f W φ) (r : O.obj (op W)) :
    freeCechTupleMap X ι U₀ U f O W n (DFinsupp.single φ (Finsupp.single x r)) =
      r • freeCechTupleGenerator X ι U₀ U f O W n φ x := by
  classical
  calc
    _ = (Finsupp.lift _ _ _ (freeCechTupleGenerator X ι U₀ U f O W n φ))
        (Finsupp.single x r) := DFinsupp.lsum_single ℕ
          (fun ψ : W ⟶ U₀ ↦ Finsupp.lift _ _ _
            (freeCechTupleGenerator X ι U₀ U f O W n ψ)) φ (Finsupp.single x r)
    _ = _ := by simp [Finsupp.lift_apply]

/-- Lifts with equal base maps, indices and underlying morphisms agree heterogeneously. -/
private theorem lifts_heq {φ ψ : W ⟶ U₀} (h : φ = ψ)
    {x : freeCechLifts X ι U₀ U f W φ} {y : freeCechLifts X ι U₀ U f W ψ}
    (hi : x.1 = y.1) (hg : HEq x.2.1 y.2.1) : HEq x y := by
  cases h
  rcases x with ⟨i, gx, hx⟩
  rcases y with ⟨j, gy, hy⟩
  dsimp only at hi hg
  subst j
  have hg' : gx = gy := eq_of_heq hg
  subst gy
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The basis-index bijection: lift tuples give product maps, and product maps give
lift tuples by projection. Source: Stacks Project, Tags 03AT and 03F5. -/
private noncomputable def tupleIndexEquiv (n : ℕ) :
    (Σ φ : W ⟶ U₀, Fin (n + 1) → freeCechLifts X ι U₀ U f W φ) ≃
      (Σ i : Fin (n + 1) → ι,
        W ⟶ (∏ᶜ (fun a ↦ Over.mk (f (i a)))).left) where
  toFun x := ⟨fun a ↦ (x.2 a).1,
    (show Over.mk x.1 ⟶ ∏ᶜ (fun a ↦ Over.mk (f ((x.2 a).1))) from
      Pi.lift (fun a ↦ Over.homMk (x.2 a).2.1 (x.2 a).2.2)).left⟩
  invFun y := ⟨y.2 ≫ (∏ᶜ (fun a ↦ Over.mk (f (y.1 a)))).hom,
    fun a ↦ ⟨y.1 a, ⟨y.2 ≫ (Pi.π (fun a ↦ Over.mk (f (y.1 a))) a).left,
      by
        rw [Category.assoc]
        exact congrArg (y.2 ≫ ·) (Over.w (Pi.π (fun a ↦ Over.mk (f (y.1 a))) a))⟩⟩⟩
  left_inv x := by
    rcases x with ⟨φ, x⟩
    let g : Over.mk φ ⟶ ∏ᶜ (fun a ↦ Over.mk (f ((x a).1))) :=
      Pi.lift (fun a ↦ Over.homMk (x a).2.1 (x a).2.2)
    have hφ : g.left ≫ (∏ᶜ (fun a ↦ Over.mk (f ((x a).1)))).hom = φ :=
      Over.w g
    dsimp only
    apply Sigma.ext hφ
    change HEq (fun a ↦ (⟨(x a).1,
      ⟨g.left ≫ (Pi.π (fun a ↦ Over.mk (f ((x a).1))) a).left, _⟩⟩ :
        freeCechLifts X ι U₀ U f W
          (g.left ≫ (∏ᶜ (fun a ↦ Over.mk (f ((x a).1)))).hom))) x
    apply Function.hfunext rfl
    intro a b hab
    cases hab
    apply lifts_heq X ι U₀ U f W hφ rfl
    apply heq_of_eq
    change (g ≫ Pi.π (fun a ↦ Over.mk (f ((x a).1))) a).left = (x a).2.1
    simp [g]
  right_inv y := by
    rcases y with ⟨i, g⟩
    dsimp only
    refine Sigma.ext ?_ ?_
    · rfl
    apply heq_of_eq
    let h : Over.mk (g ≫ (∏ᶜ (fun a ↦ Over.mk (f (i a)))).hom) ⟶
        ∏ᶜ (fun a ↦ Over.mk (f (i a))) := Over.homMk g
    have hh : Pi.lift (fun a ↦ Over.homMk
        (g ≫ (Pi.π (fun a ↦ Over.mk (f (i a))) a).left) (by
          rw [Category.assoc]
          exact congrArg (g ≫ ·) (Over.w (Pi.π (fun a ↦ Over.mk (f (i a))) a)))) = h := by
      apply Pi.hom_ext
      intro a
      apply Over.OverMorphism.ext
      simp [h]
    exact congrArg Over.Hom.left hh

set_option backward.isDefEq.respectTransparency false in
/-- The tuple-generator map is bijective in each degree.
Source: Stacks Project, Tag 03AT, the decomposition preceding the homotopy;
Tag 03F5, first proof, with coefficients in O(W).
Proof: Evaluation preserves coproducts of presheaf modules. Each evaluated free
representable is the free O(W)-module on morphisms from W. Its basis is thus the
pairs (i,g) with i : Fin (n+1) → ι and g : W → the product over U₀ of U(i(a)).
Send such a pair to the common composite φ and its tuple of projections. Conversely,
from φ and a tuple of lifts form the product map in Over U₀ by Pi.lift. The projection
and uniqueness identities for the product show these functions are inverse. The
free-module extension of this bijection and the regrouping of finite support by φ
are linear isomorphisms; their inverse is exactly the displayed tuple-generator map.
This also handles an empty family, when both bases are empty, and the zero ring,
when both modules are zero. No lift of an arbitrary φ is chosen.
(blueprint: lem-weil-pbc-free-cech-tuple-basis) -/
theorem freeCechTupleMap_bijective (n : ℕ) :
    Function.Bijective (freeCechTupleMap X ι U₀ U f O W n) := by
  classical
  let R := O.obj (op W)
  let D := Π₀ φ : W ⟶ U₀,
    Algebra.powerSetComplexObject R (freeCechLifts X ι U₀ U f W φ) n
  let F (i : Fin (n + 1) → ι) := (PresheafOfModules.free O).obj
    (yoneda.obj ((∏ᶜ (fun a ↦ Over.mk (f (i a)))).left))
  let M := ((freeCechModule X ι U₀ U f O).obj (op ⦋n⦌)).obj (op W)
  let ev := PresheafOfModules.evaluation O (op W)
  -- Evaluation preserves the coproduct of free representable presheaves.
  let hc := (Cofan.isColimitMapCoconeEquiv ev F
    (Cofan.mk _ (Sigma.ι F)))
      (isColimitOfPreserves ev (coproductIsCoproduct F))
  let e := tupleIndexEquiv X ι U₀ U f W n
  let singleTuple (x : Σ φ : W ⟶ U₀,
      Fin (n + 1) → freeCechLifts X ι U₀ U f W φ) : D :=
    DFinsupp.single x.1 (Finsupp.single x.2 1)
  let gen (y : Σ i : Fin (n + 1) → ι,
      W ⟶ (∏ᶜ (fun a ↦ Over.mk (f (i a)))).left) : M :=
    ((Sigma.ι F y.1).app (op W)) (ModuleCat.freeMk y.2)
  -- Extend the inverse index bijection freely on each evaluated summand.
  let components (i : Fin (n + 1) → ι) :
      (F i).obj (op W) ⟶ ModuleCat.of R D :=
    ModuleCat.freeDesc (↾fun g ↦ singleTuple (e.symm ⟨i, g⟩))
  let d : M ⟶ ModuleCat.of R D := hc.desc (Cofan.mk _ components)
  let b := freeCechTupleMap X ι U₀ U f O W n
  have hd (y : Σ i : Fin (n + 1) → ι,
      W ⟶ (∏ᶜ (fun a ↦ Over.mk (f (i a)))).left) :
      d (gen y) = singleTuple (e.symm y) := by
    have h := hc.fac (Cofan.mk _ components) (Discrete.mk y.1)
    have h' := congrArg (fun k ↦ k (ModuleCat.freeMk y.2)) h
    change d (gen y) = components y.1 (ModuleCat.freeMk y.2) at h'
    exact h'.trans (ModuleCat.freeDesc_apply _ _)
  -- Check the two inverse identities on the respective free generators.
  have hleft : d.hom.comp b = LinearMap.id := by
    apply DFinsupp.lhom_ext'
    intro φ
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    change d (b (DFinsupp.single φ (Finsupp.single x 1))) =
      DFinsupp.single φ (Finsupp.single x 1)
    rw [freeCechTupleMap_single, one_smul]
    change d (gen (e ⟨φ, x⟩)) = singleTuple ⟨φ, x⟩
    rw [hd, e.symm_apply_apply]
  have hright : d ≫ ModuleCat.ofHom b = 𝟙 M := by
    apply hc.hom_ext
    intro i
    apply ModuleCat.free_hom_ext
    intro g
    change b (d (gen ⟨i.as, g⟩)) = gen ⟨i.as, g⟩
    rw [hd]
    change b (DFinsupp.single (e.symm ⟨i.as, g⟩).1
      (Finsupp.single (e.symm ⟨i.as, g⟩).2 1)) = gen ⟨i.as, g⟩
    rw [freeCechTupleMap_single, one_smul]
    change gen (e (e.symm ⟨i.as, g⟩)) = gen ⟨i.as, g⟩
    rw [e.apply_symm_apply]
  exact ⟨(show Function.LeftInverse d b from
    fun x ↦ LinearMap.congr_fun hleft x).injective,
    (show Function.RightInverse d b from
      fun x ↦ congrArg (fun k ↦ k x) hright).surjective⟩

end AlgebraicGeometry

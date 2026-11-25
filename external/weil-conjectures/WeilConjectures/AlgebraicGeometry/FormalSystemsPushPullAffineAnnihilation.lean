/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

public import Mathlib.Algebra.Category.ModuleCat.Limits

import WeilConjectures.AlgebraicGeometry.FormalComparisonCompletedAffineModel
import WeilConjectures.AlgebraicGeometry.CoherentAffineMapSupportRadical
import WeilConjectures.RingTheory.AdicCompletionNoetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Affine annihilation of the canonical formal push-pull comparison

Source: Stacks Project, Cohomology of Schemes, Lemma 088B, second half of the proof.
(blueprint: lem-weil-pbc-formal-systems-push-pull-affine-annihilation)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem annihilator_ker_of_square
    {B : Type u} [CommRing B] {M N P Q : ModuleCat.{u} B}
    (v : M ⟶ N) (w : P ⟶ Q) (eM : M ≅ P) (eN : N ≅ Q)
    (hs : v ≫ eN.hom = eM.hom ≫ w) {a : B}
    (ha : a ∈ Module.annihilator B (LinearMap.ker w.hom)) :
    a ∈ Module.annihilator B (LinearMap.ker v.hom) := by
  rw [Module.mem_annihilator] at ha ⊢
  intro x
  apply Subtype.ext
  change a • (x : M) = 0
  apply eM.toLinearEquiv.injective
  rw [map_smul, map_zero]
  have hx : eM.hom (x : M) ∈ LinearMap.ker w.hom := by
    rw [LinearMap.mem_ker]
    have he := congrArg (fun k : M ⟶ Q ↦ k (x : M)) hs
    change eN.hom (v.hom x) = w.hom (eM.hom x) at he
    rw [x.property, map_zero] at he
    exact he.symm
  exact congrArg Subtype.val (ha ⟨eM.hom x, hx⟩)

private theorem annihilator_coker_of_square
    {B : Type u} [CommRing B] {M N P Q : ModuleCat.{u} B}
    (v : M ⟶ N) (w : P ⟶ Q) (eM : M ≅ P) (eN : N ≅ Q)
    (hs : v ≫ eN.hom = eM.hom ≫ w) {a : B}
    (ha : a ∈ Module.annihilator B (Q ⧸ LinearMap.range w.hom)) :
    a ∈ Module.annihilator B (N ⧸ LinearMap.range v.hom) := by
  rw [Module.mem_annihilator] at ha ⊢
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range v.hom) x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hy : a • eN.hom y ∈ LinearMap.range w.hom := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    rw [Submodule.Quotient.mk_smul]
    exact ha (Submodule.Quotient.mk (eN.hom y))
  obtain ⟨z, hz⟩ := hy
  obtain ⟨x, hx⟩ := eM.toLinearEquiv.surjective z
  refine ⟨x, eN.toLinearEquiv.injective ?_⟩
  have he := congrArg (fun k : M ⟶ Q ↦ k x) hs
  change eN.hom (v.hom x) = w.hom (eM.hom x) at he
  change eM.hom x = z at hx
  change eN.hom (v.hom x) = eN.hom (a • y)
  rw [map_smul, he, hx]
  exact hz

private theorem annihilator_pow_of_restrictScalars_square
    {B R : Type u} [CommRing B] [CommRing R] [Algebra B R] [IsNoetherianRing R]
    (I : Ideal B) {M N : ModuleCat.{u} B} {P Q : ModuleCat.{u} R}
    (v : M ⟶ N) (w : P ⟶ Q)
    (eM : M ≅ (ModuleCat.restrictScalars (algebraMap B R)).obj P)
    (eN : N ≅ (ModuleCat.restrictScalars (algebraMap B R)).obj Q)
    (hs : v ≫ eN.hom =
      eM.hom ≫ (ModuleCat.restrictScalars (algebraMap B R)).map w)
    (hk : I.map (algebraMap B R) ≤ (Module.annihilator R (LinearMap.ker w.hom)).radical)
    (hq : I.map (algebraMap B R) ≤
      (Module.annihilator R (Q ⧸ LinearMap.range w.hom)).radical) :
    ∃ t : ℕ, 1 ≤ t ∧
      I ^ t ≤ Module.annihilator B (LinearMap.ker v.hom) ∧
      I ^ t ≤ Module.annihilator B (N ⧸ LinearMap.range v.hom) := by
  let L := I.map (algebraMap B R)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hk
    (Ideal.fg_of_isNoetherianRing L)
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hq
    (Ideal.fg_of_isNoetherianRing L)
  let t := max n m + 1
  have hnt : n ≤ t := (le_max_left n m).trans (Nat.le_succ _)
  have hmt : m ≤ t := (le_max_right n m).trans (Nat.le_succ _)
  have hker := (Ideal.pow_le_pow_right hnt).trans hn
  have hcoker := (Ideal.pow_le_pow_right hmt).trans hm
  refine ⟨t, Nat.succ_le_succ (Nat.zero_le _), ?_, ?_⟩
  · intro a ha
    have haR : algebraMap B R a ∈ L ^ t := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    apply annihilator_ker_of_square (B := B) _ _ eM eN hs
    rw [Module.mem_annihilator]
    intro x
    exact Module.mem_annihilator.mp (hker haR) x
  · intro a ha
    have haR : algebraMap B R a ∈ L ^ t := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    apply annihilator_coker_of_square (B := B) _ _ eM eN hs
    rw [Module.mem_annihilator]
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hy := Module.mem_annihilator.mp (hcoker haR) (Submodule.Quotient.mk y)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
    exact hy

/-- The canonical comparison, specified by its quotient and adjunction equations,
has affine limit kernel and cokernel killed by a positive power of K.

Source: Stacks Project, Lemma 088B, proof from the base change to Spec(B-completion)
to its last paragraph; Remark 0888, condition (2).
(blueprint: lem-weil-pbc-formal-systems-push-pull-affine-annihilation)

Proof: Restrict to an affine open U = Spec B. The quotient equation determines
κ uniquely because the quotient projections are epimorphisms. Formal functions
and the affine formal-module equivalence then show that the adjunction equation
determines α uniquely. Replace B by its J-adic completion B'; it is Noetherian
and flat over B, and B/J^n = B'/(JB')^n. Flat base change identifies the
pushforward sections, the quotient maps, and the adjunction units; uniqueness
therefore identifies the pulled-back comparison with the comparison over B'.
The affine formal-module equivalence algebraizes G over B'. Full faithfulness
of completion on coherent modules proper over a complete base algebraizes β
to an isomorphism b: f*G -> F. The comparison is now the completion of the
adjunction map G -> f_*f*G followed by f_*b, by its defining equations.
Over the complement of V(K) this is an isomorphism, since f is an isomorphism
there. Its coherent kernel and cokernel are supported on V(K); Tag 01Y9
annihilates both by a common positive power K^s. Exactness of completion on
finite modules carries this annihilation to the affine limit kernel and
cokernel. Since the two affine limit modules are already complete modules,
the original and completed limit maps coincide under the canonical equivalences;
restricting scalars carries annihilation by (KB')^s back to K^s. This yields
one exponent for each U. For K = 0 choose exponent 1; on an empty affine
all modules vanish, so exponent 1 also works.
-/
theorem formalSystemsPushPull_affine_annihilation
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl)))
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (α : G ⟶ (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) =
      (Scheme.Modules.pushforward f).map
        (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (hα : ∀ n : ℕ, α.hom.app (op n) ≫ κ.app (op n) =
      adj.unit.app (G.obj.obj (op n)) ≫
        (Scheme.Modules.pushforward f).map (β.hom.app (op n))) :
    ∀ U : Y.affineOpens, ∃ t : ℕ, 1 ≤ t ∧
      K.ideal U ^ t ≤ Module.annihilator Γ(Y, U.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)))).hom) ∧
      K.ideal U ^ t ≤ Module.annihilator Γ(Y, U.1)
        (↥(limit (((completion Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩).obj ⋙
          SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) :
          ModuleCat Γ(Y, U.1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)))).hom) := by
  intro U
  let B := Γ(Y, U.1)
  let R := AdicCompletion (J.ideal U) B
  let L := (K.ideal U).map (algebraMap B R)
  have : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing R := AdicCompletion.isNoetherianRing (J.ideal U)
  obtain ⟨A, D, c, hc, eA, eD, hs⟩ :=
    formalComparison_completed_affine_model J K f hV adj G F β h κ α hκ hα U
  obtain ⟨hk, hq⟩ := coherentAffineMap_support_radical R L A D c hc
  exact annihilator_pow_of_restrictScalars_square (K.ideal U) _ _ eA eD hs hk hq

end AlgebraicGeometry

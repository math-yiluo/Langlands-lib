/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.DirectedColimitBaseChangeElementwise
import Mathlib.Data.Fintype.Order

/-!
# Lifting maps into a tensor colimit

Source: Stacks Project, Algebra, Tag 05LI, proof of (3).
(blueprint: lem-pc-fp-restricted-hom-colimit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace ModuleCat

-- The finite free presentation argument, separated from the tensor bookkeeping.
-- Only existence is asserted; no data is selected from an unproved theorem.
private theorem lift_finitePresentation
    {R : Type u} [CommRing R] {J : Type u} [Preorder J] [Nonempty J]
    [IsDirected J (· ≤ ·)] {P T : Type (max u v)}
    [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    [AddCommGroup T] [Module R T]
    (G : J → Type (max u v)) [∀ j, AddCommGroup (G j)] [∀ j, Module R (G j)]
    (f : ∀ j k, j ≤ k → G j →ₗ[R] G k)
    [DirectedSystem G (fun {j k} h ↦ f j k h)]
    (α : ∀ j, G j →ₗ[R] T)
    (hc : ∀ j k h x, α k (f j k h x) = α j x)
    (hr : ∀ x : T, ∃ j xj, α j xj = x)
    (hz : ∀ j x, α j x = 0 → ∃ k h, f j k h x = 0)
    (h : P →ₗ[R] T) : ∃ (j : J) (a : P →ₗ[R] G j), (α j).comp a = h := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R P
  let p : (Fin n → R) →ₗ[R] P := e.symm.toLinearMap.comp K.mkQ
  let b := Pi.basisFun R (Fin n)
  choose j x hx using fun q : Fin n ↦ hr (h (p (b q)))
  obtain ⟨j₀, hj₀⟩ := (Set.finite_range j).exists_le
  let y (q : Fin n) : G j₀ := f (j q) j₀ (hj₀ _ ⟨q, rfl⟩) (x q)
  let a₀ := b.constr R y
  have ha₀ : (α j₀).comp a₀ = h.comp p := by
    apply b.ext
    intro q
    change α j₀ (b.constr R y (b q)) = h (p (b q))
    rw [Module.Basis.constr_basis]
    exact (hc _ _ _ _).trans (hx q)
  obtain ⟨s, hs⟩ := hK
  have hs0 (x : (Fin n → R)) (hx : x ∈ s) : α j₀ (a₀ x) = 0 := by
    have hxK : x ∈ K := by
      rw [← hs]
      exact Submodule.subset_span hx
    have hpx : p x = 0 := by simp [p, hxK]
    exact (LinearMap.congr_fun ha₀ x).trans (by simp [hpx])
  choose k hk hk0 using fun x : s ↦ hz j₀ (a₀ x) (hs0 x x.property)
  obtain ⟨k₀, hk₀⟩ := (Set.finite_range k).exists_le
  obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j₀ k₀
  let a₁ := (f j₀ l hjl).comp a₀
  have hkill : K ≤ LinearMap.ker a₁ := by
    rw [← hs, Submodule.span_le]
    intro x hx
    let z : s := ⟨x, hx⟩
    have hzl : k z ≤ l := (hk₀ _ ⟨z, rfl⟩).trans hkl
    change f j₀ l hjl (a₀ x) = 0
    rw [← DirectedSystem.map_map (f := fun {j k} h ↦ f j k h)
      (hk z) hzl (a₀ x), hk0 z, map_zero]
  let a : P →ₗ[R] G l := (K.liftQ a₁ hkill).comp e.toLinearMap
  refine ⟨l, a, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨z, hz⟩ := K.mkQ_surjective (e x)
  have hx : p z = x := by simp [p, hz]
  rw [← hx]
  change α l ((K.liftQ a₁ hkill) (e (p z))) = h (p z)
  have hep : e (p z) = K.mkQ z := by simp [p]
  rw [hep]
  change α l (a₁ z) = h (p z)
  exact (hc _ _ _ _).trans (LinearMap.congr_fun ha₀ z)

/-- A map from a finitely presented stage module into a tensor colimit lifts as
an uncurried map at a later stage. The target module need not be finitely presented.

Source: Stacks Project, Algebra, Tag 05LI, proof of (3),
label algebra-lemma-module-map-property-in-colimit.
(blueprint: lem-pc-fp-restricted-hom-colimit).

Proof: choose finite generators and finitely many generators of their relations
in M. Each generator image in A tensor N is a finite sum of pure tensors, whose
coefficients can be lifted to a common stage j above i. The relation combinations
of these lifted images vanish in the final tensor product. Tensor product
commutes with the directed colimit, so each such relation vanishes at some later
stage. Choose one upper bound for the finitely many relations. The lifted images
then define an Ai-linear map a into Aj tensor N. For any comparison e satisfying
the displayed pure-tensor equation, linearity forces the same comparison on all
pure tensors and their sums, giving the asserted equality. Empty presentations
and the zero target give the zero map. -/
theorem exists_stage_restricted_hom
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat) (i : I) (M N : ModuleCat.{max u v} (F.obj i))
    [Module.FinitePresentation (F.obj i) M]
    (h : M ⟶ (restrictScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj
      ((extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj N)) :
    ∃ (j : I) (hij : i ≤ j),
      let rij := CommRingCat.Hom.hom (F.map (homOfLE hij))
      let rj := CommRingCat.Hom.hom (colimit.ι F j)
      let ri := CommRingCat.Hom.hom (colimit.ι F i)
      ∃ (a : M ⟶ (restrictScalars rij).obj ((extendScalars rij).obj N)),
        ∀ (e : (extendScalars ri).obj N ≅
          (extendScalars rj).obj ((extendScalars rij).obj N)),
          (∀ n : N, e.hom ((1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj i, ri] n) =
            (1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj j, rj]
              ((1 : ↑(F.obj j)) ⊗ₜ[F.obj i, rij] n)) →
          ∀ m : M, e.hom (h m) =
            (1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj j, rj] (a m) := by
  classical
  let S := F.obj i
  let A := colimit F
  let ri := (colimit.ι F i).hom
  let : Algebra S A := ri.toAlgebra
  let J := {j : I // i ≤ j}
  let : Nonempty J := ⟨⟨i, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  let B (j : J) : Type u := F.obj j.val
  let : ∀ j, CommRing (B j) := fun j ↦ inferInstance
  let : ∀ j, Algebra S (B j) := fun j ↦ (F.map (homOfLE j.property)).hom.toAlgebra
  let G (j : J) := TensorProduct S (B j) N
  let : ∀ j, AddCommGroup (G j) := fun j ↦ inferInstance
  let : ∀ j, Module S (G j) := fun j ↦ inferInstance
  let β (j k : J) (hjk : j ≤ k) : B j →ₐ[S] B k :=
    { (F.map (homOfLE hjk)).hom with
      commutes' := fun s ↦ congrArg (fun p : F.obj i ⟶ F.obj k.val ↦ p s)
        (F.map_comp (homOfLE j.property) (homOfLE hjk)).symm }
  let f (j k : J) (hjk : j ≤ k) : G j →ₗ[S] G k :=
    (β j k hjk).toLinearMap.rTensor N
  let γ (j : J) : B j →ₐ[S] A :=
    { (colimit.ι F j.val).hom with
      commutes' := fun s ↦ congrArg (fun p : F.obj i ⟶ A ↦ p s)
        (colimit.w F (homOfLE j.property)) }
  let α (j : J) : G j →ₗ[S] (TensorProduct S A N) := (γ j).toLinearMap.rTensor N
  let : DirectedSystem G (fun {j k} hjk ↦ f j k hjk) :=
    { map_self := by
        intro j t
        induction t using TensorProduct.inductionOn with
        | tmul r n =>
          dsimp only [f, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
          change TensorProduct.tmul S (F.map (homOfLE (le_refl j.val)) r) n =
            TensorProduct.tmul S r n
          simp
        | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'
      map_map := by
        intro l k j hjk hkl t
        induction t using TensorProduct.inductionOn with
        | tmul r n =>
          dsimp only [f, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
          exact congrArg (fun r : F.obj l.val ↦ TensorProduct.tmul S r n)
            (ConcreteCategory.congr_hom (F.map_comp (homOfLE hjk) (homOfLE hkl)) r).symm
        | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht' }
  have hc (j k : J) (hjk : j ≤ k) (t : G j) : α k (f j k hjk t) = α j t := by
    induction t using TensorProduct.inductionOn with
    | tmul r n =>
      dsimp only [α, f, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      exact congrArg (fun r : A ↦ TensorProduct.tmul S r n)
        (ConcreteCategory.congr_hom (colimit.w F (homOfLE hjk)) r)
    | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'
  have hr (t : TensorProduct S A N) : ∃ j tj, α j tj = t := by
    obtain ⟨j, hij, tj, htj⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise F i N).1 t
    exact ⟨⟨j, hij⟩, tj, htj⟩
  have hz (j : J) (t : G j) (ht : α j t = 0) :
      ∃ (k : J) (hjk : j ≤ k), f j k hjk t = 0 := by
    obtain ⟨k, hjk, hk⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise F i N).2 j.val j.property t ht
    exact ⟨⟨k, j.property.trans hjk⟩, hjk, hk⟩
  let h' : M →ₗ[S] (TensorProduct S A N) :=
    { toFun := h
      map_add' := h.hom.map_add
      map_smul' := by
        intro r m
        have hm := h.hom.map_smul r m
        change h (r • m) = ri r • (h m : TensorProduct S A N) at hm
        change h (r • m) = r • (h m : TensorProduct S A N)
        have hs (t : TensorProduct S A N) : ri r • t = r • t := algebraMap_smul A r t
        exact hm.trans (hs (h m)) }
  obtain ⟨j, a, ha⟩ := lift_finitePresentation G f α hc hr hz h'
  refine ⟨j.val, j.property, ?_⟩
  dsimp only
  let rij := (F.map (homOfLE j.property)).hom
  let rj := (colimit.ι F j.val).hom
  let a' : M ⟶ (restrictScalars rij).obj ((extendScalars rij).obj N) :=
    ofHom (X := M) (Y := (restrictScalars rij).obj ((extendScalars rij).obj N))
      { toFun := a
        map_add' := a.map_add
        map_smul' := by
          intro r m
          change a (r • m) = (algebraMap S (B j)) r • (a m : G j)
          rw [algebraMap_smul]
          exact a.map_smul r m }
  refine ⟨a', ?_⟩
  intro e he m
  let : Algebra (B j) A := rj.toAlgebra
  have ht (t : G j) : e.hom (α j t) = (1 : A) ⊗ₜ[F.obj j.val, rj] t := by
    induction t using TensorProduct.inductionOn with
    | tmul r n =>
      change e.hom ((rj r) ⊗ₜ[F.obj i, ri] n) =
        (1 : A) ⊗ₜ[F.obj j.val, rj] (r ⊗ₜ[F.obj i, rij] n)
      have hin : (rj r) ⊗ₜ[F.obj i, ri] n =
          (rj r) • ((1 : A) ⊗ₜ[F.obj i, ri] n) := by
        rw [ExtendScalars.smul_tmul, mul_one]
      rw [hin, e.hom.hom.map_smul, he]
      change (rj r) • ((1 : A) ⊗ₜ[F.obj j.val, rj]
        ((1 : B j) ⊗ₜ[F.obj i, rij] n)) =
        (1 : A) ⊗ₜ[F.obj j.val, rj] (r ⊗ₜ[F.obj i, rij] n)
      change ((rj r) * 1) ⊗ₜ[F.obj j.val, rj]
        ((1 : B j) ⊗ₜ[F.obj i, rij] n) =
        (1 : A) ⊗ₜ[F.obj j.val, rj] (r ⊗ₜ[F.obj i, rij] n)
      rw [mul_one]
      have hn : r ⊗ₜ[F.obj i, rij] n =
          r • ((1 : B j) ⊗ₜ[F.obj i, rij] n) := by
        change r ⊗ₜ[F.obj i, rij] n = (r * 1) ⊗ₜ[F.obj i, rij] n
        rw [mul_one]
      rw [hn, TensorProduct.tmul_smul]
      change rj r ⊗ₜ[F.obj j.val, rj] ((1 : B j) ⊗ₜ[F.obj i, rij] n) =
        (rj r * 1) ⊗ₜ[F.obj j.val, rj] ((1 : B j) ⊗ₜ[F.obj i, rij] n)
      rw [mul_one]
    | add t t' ht ht' =>
      simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) ht ht'
  exact (congrArg (fun t ↦ e.hom t) (LinearMap.congr_fun ha m)).symm.trans (ht (a m))

end ModuleCat

import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Cancellation of finite-dimensional modules over a field algebra -/

namespace Langlands.FiniteModuleCancellation

universe u v w

open LinearMap

noncomputable section

variable {K : Type u} [Field K] {R : Type w} [Ring R] [Algebra K R]
variable {A M N : Type v} [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

private def Indecomposable (R : Type w) (A : Type v) [Ring R] [AddCommGroup A] [Module R A] : Prop :=
  ∀ (p q : Submodule R A), IsCompl p q → p = ⊥ ∨ q = ⊥

private theorem finite_submodule [Module K M] [IsScalarTower K R M] [Module.Finite K M]
    (p : Submodule R M) : Module.Finite K p :=
  Module.Finite.of_injective (p.subtype.restrictScalars K) Subtype.val_injective

private theorem bijective_of_injective [Module K A] [IsScalarTower K R A] [Module.Finite K A]
    {f : Module.End R A} (hf : Function.Injective f) : Function.Bijective f :=
  ⟨hf, (LinearMap.injective_iff_surjective (f := f.restrictScalars K)).mp hf⟩

private theorem end_isLocalRing [Nontrivial A] [Module K A] [IsScalarTower K R A]
    [Module.Finite K A] (hA : Indecomposable R A) : IsLocalRing (Module.End R A) := by
  have : IsArtinian R A := isArtinian_of_tower K (inferInstance : IsArtinian K A)
  have : IsNoetherian R A := isNoetherian_of_tower K (inferInstance : IsNoetherian K A)
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp f.eventually_isCompl_ker_pow_range_pow
  rcases hA _ _ (hk (k + 1) (Nat.le_succ k)) with hk' | hk'
  · have hinj : Function.Injective f := by
      apply LinearMap.ker_eq_bot.1
      apply LinearMap.ker_eq_bot'.2
      intro x hx
      apply LinearMap.ker_eq_bot'.1 hk'
      rw [pow_succ, Module.End.mul_apply, hx, map_zero]
    let e := LinearEquiv.ofBijective f (bijective_of_injective (K := K) hinj)
    exact Or.inl ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv e, rfl⟩
  · exact Or.inr (IsNilpotent.isUnit_one_sub ⟨k + 1, LinearMap.range_eq_bot.1 hk'⟩)

private theorem comp_split (a : A →ₗ[R] M) (b : M →ₗ[R] A) (h : b.comp a = LinearMap.id) :
    IsCompl (LinearMap.range a) (LinearMap.ker b) := by
  have ha : ∀ x, b (a x) = x := DFunLike.congr_fun h
  have hproj : LinearMap.IsProj (LinearMap.range a) (a.comp b) :=
    ⟨fun _ => LinearMap.mem_range_self _ _, fun _ ⟨x, hx⟩ => by rw [← hx, comp_apply, ha]⟩
  convert hproj.isCompl using 1
  exact (LinearMap.ker_comp_of_ker_eq_bot b
    (LinearMap.ker_eq_bot.2 (Function.LeftInverse.injective ha))).symm

private def equivOfSection (a : A →ₗ[R] M) (b : M →ₗ[R] A) (h : b.comp a = LinearMap.id) :
    (A × LinearMap.ker b) ≃ₗ[R] M :=
  let ha : Function.LeftInverse b a := DFunLike.congr_fun h
  ((LinearEquiv.ofInjective a ha.injective).prodCongr (LinearEquiv.refl R _)).trans
    (Submodule.prodEquivOfIsCompl _ _ (comp_split a b h))

private theorem exists_indecomposable_summand [Nontrivial M] [Module K M] [IsScalarTower K R M]
    [Module.Finite K M] :
    ∃ p q : Submodule R M, IsCompl p q ∧ Nontrivial p ∧ Indecomposable R p := by
  classical
  let P (k : ℕ) := ∃ p q : Submodule R M, IsCompl p q ∧ 0 < k ∧ Module.finrank K p = k
  have hP : ∃ k, P k := ⟨Module.finrank K M, ⊤, ⊥, isCompl_top_bot, Module.finrank_pos,
    (Submodule.topEquiv.restrictScalars K).finrank_eq⟩
  obtain ⟨p, q, hpq, hk, hpdim⟩ := Nat.find_spec hP
  have : Module.Finite K p := finite_submodule p
  have hp : Nontrivial p := Module.finrank_pos_iff.mp (hpdim.symm ▸ hk)
  refine ⟨p, q, hpq, hp, fun p' q' hcompl => ?_⟩
  by_contra! hne
  have : Nontrivial p' := Submodule.nontrivial_iff_ne_bot.mpr hne.1
  have : Nontrivial q' := Submodule.nontrivial_iff_ne_bot.mpr hne.2
  have : Module.Finite K p' := finite_submodule p'
  have : Module.Finite K q' := finite_submodule q'
  let a : p' →ₗ[R] M := p.subtype.comp p'.subtype
  let b := (p'.projectionOnto q' hcompl).comp (p.projectionOnto q hpq)
  have hab : b.comp a = LinearMap.id := by
    ext x
    simp [a, b]
  have hab' : Function.LeftInverse b a := DFunLike.congr_fun hab
  let e := LinearEquiv.ofInjective a hab'.injective
  have hd := ((Submodule.prodEquivOfIsCompl p' q' hcompl).restrictScalars K).finrank_eq
  rw [Module.finrank_prod, hpdim] at hd
  have hqpos : 0 < Module.finrank K q' := Module.finrank_pos
  have happ : P (Module.finrank K p') := ⟨LinearMap.range a, LinearMap.ker b,
    comp_split a b hab, Module.finrank_pos, (e.restrictScalars K).finrank_eq.symm⟩
  have hle := Nat.find_min' hP happ
  omega

private theorem cancel_of_pivot (e : (A × M) ≃ₗ[R] A × N)
    (hf : Function.Surjective fun a => (e (a, 0)).1) (hzero : ∀ a, (e (a, 0)).2 = 0) :
    Nonempty (M ≃ₗ[R] N) := by
  let f := (LinearMap.snd R A N).comp (e.toLinearMap.comp (LinearMap.inr R A M))
  have he (a : A) (x : M) : e (a, x) = e (a, 0) + e (0, x) := by
    rw [← map_add]
    simp
  refine ⟨LinearEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro x y hxy
    obtain ⟨a, ha⟩ := hf ((e (0, x)).1 - (e (0, y)).1)
    change (e (a, 0)).1 = _ at ha
    have h : e (0, x) = e (a, y) := by
      rw [he a y]
      apply Prod.ext
      · change (e (0, x)).1 = (e (a, 0)).1 + (e (0, y)).1
        rw [ha, sub_add_cancel]
      · change f x = (e (a, 0)).2 + f y
        rw [hzero, zero_add, hxy]
    exact congrArg Prod.snd (e.injective h)
  · intro y
    obtain ⟨⟨a, x⟩, h⟩ := e.surjective (0, y)
    refine ⟨x, ?_⟩
    have hh := congrArg Prod.snd h
    rw [he a x] at hh
    change _ + f x = y at hh
    simpa only [hzero, zero_add] using hh

private def addToFirst (f : N →ₗ[R] A) : (A × N) ≃ₗ[R] A × N where
  toFun x := (x.1 + f x.2, x.2)
  invFun x := (x.1 - f x.2, x.2)
  left_inv x := Prod.ext (add_sub_cancel_right _ _) rfl
  right_inv x := Prod.ext (sub_add_cancel _ _) rfl
  map_add' x y := Prod.ext (by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel) rfl
  map_smul' a x := Prod.ext (by simp [smul_add]) rfl

private theorem cancel_of_bijective_pivot (e : (A × M) ≃ₗ[R] A × N)
    (h : Function.Bijective fun a => (e (a, 0)).1) : Nonempty (M ≃ₗ[R] N) := by
  let f := (LinearMap.fst R A N).comp (e.toLinearMap.comp (LinearMap.inl R A M))
  let pivot := LinearEquiv.ofBijective f h
  let k := (LinearMap.snd R A N).comp (e.toLinearMap.comp (LinearMap.inl R A M))
  let correction := (LinearEquiv.prodComm R A N).trans
    ((addToFirst (-(k.comp pivot.symm.toLinearMap))).trans (LinearEquiv.prodComm R N A))
  apply cancel_of_pivot (e.trans correction) h.2
  intro a
  change k a + (-(k.comp pivot.symm.toLinearMap)) (pivot a) = 0
  simp

private theorem cancel_indecomposable [Nontrivial A] [Module K A] [IsScalarTower K R A]
    [Module.Finite K A] (hA : Indecomposable R A) (e : (A × M) ≃ₗ[R] A × N) :
    Nonempty (M ≃ₗ[R] N) := by
  have : IsLocalRing (Module.End R A) := end_isLocalRing (K := K) hA
  let first := e.toLinearMap.comp (LinearMap.inl R A M)
  let f := (LinearMap.fst R A N).comp first
  let k := (LinearMap.snd R A N).comp first
  let invFirst := (LinearMap.fst R A M).comp e.symm.toLinearMap
  let g := invFirst.comp (LinearMap.inl R A N)
  let h := invFirst.comp (LinearMap.inr R A N)
  have heq : g * f + h.comp k = 1 := by
    ext a
    change invFirst (f a, 0) + invFirst (0, k a) = a
    rw [← map_add]
    simp [f, k, first, invFirst]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one heq with hgf | hhk
  · obtain ⟨u, hu⟩ := hgf
    have hinj : Function.Injective f := by
      have huinj : Function.Injective (g * f) :=
        hu ▸ (LinearMap.GeneralLinearGroup.toLinearEquiv u).injective
      exact Function.Injective.of_comp (f := g) (g := f) huinj
    exact cancel_of_bijective_pivot e (bijective_of_injective (K := K) hinj)
  · obtain ⟨u, hu⟩ := hhk
    let adjust := ((1 - f).comp (u⁻¹).val).comp h
    apply cancel_of_bijective_pivot (e.trans (addToFirst adjust))
    have hp (a : A) : (e.trans (addToFirst adjust) (a, 0)).1 = a := by
      change f a + (1 - f) ((u⁻¹ : (Module.End R A)ˣ).val ((h.comp k) a)) = a
      have hInv : (u⁻¹ : (Module.End R A)ˣ).val (u.val a) = a :=
        (LinearMap.GeneralLinearGroup.toLinearEquiv u).symm_apply_apply a
      rw [← hu, hInv]
      change f a + (a - f a) = a
      abel
    exact ⟨fun a b hab => by simpa only [hp] using hab, fun a => ⟨a, hp a⟩⟩

private def succCopies (M : Type v) [AddCommGroup M] [Module R M] (d : ℕ) :
    (Fin (d + 1) → M) ≃ₗ[R] M × (Fin d → M) :=
  (LinearEquiv.piCongrLeft R (fun _ => M) (finSuccEquiv d)).trans
    (LinearEquiv.piOptionEquivProd R)

private theorem cancel_indecomposable_copies [Nontrivial A] [Module K A] [IsScalarTower K R A]
    [Module.Finite K A] (hA : Indecomposable R A) (d : ℕ)
    (e : ((Fin d → A) × M) ≃ₗ[R] (Fin d → A) × N) : Nonempty (M ≃ₗ[R] N) := by
  induction d with
  | zero =>
    have left (X : Type v) [AddCommGroup X] [Module R X] : ((Fin 0 → A) × X) ≃ₗ[R] X :=
      LinearEquiv.ofBijective (LinearMap.snd R (Fin 0 → A) X)
        ⟨fun x y h => Prod.ext (Subsingleton.elim _ _) h, fun x => ⟨(0, x), rfl⟩⟩
    exact ⟨(left M).symm.trans (e.trans (left N))⟩
  | succ d ih =>
    let split (X : Type v) [AddCommGroup X] [Module R X] :=
      ((succCopies (R := R) A d).prodCongr (LinearEquiv.refl R X)).trans
        (LinearEquiv.prodAssoc R A (Fin d → A) X)
    obtain ⟨e'⟩ := cancel_indecomposable (K := K) hA ((split M).symm.trans (e.trans (split N)))
    exact ih e'

private theorem split_of_copies [Nontrivial A] [Module K A] [IsScalarTower K R A]
    [Module.Finite K A] (hA : Indecomposable R A) {d : ℕ}
    (f : A →ₗ[R] Fin d → M) (g : (Fin d → M) →ₗ[R] A) (h : g.comp f = LinearMap.id) :
    ∃ q : Submodule R M, Nonempty ((A × q) ≃ₗ[R] M) := by
  classical
  have : IsLocalRing (Module.End R A) := end_isLocalRing (K := K) hA
  let fᵢ (i : Fin d) := (LinearMap.proj i).comp f
  let gᵢ (i : Fin d) := g.comp (LinearMap.single R (fun _ => M) i)
  have hsum : (∑ i, (gᵢ i).comp (fᵢ i)) = (1 : Module.End R A) := by
    ext a
    simp only [LinearMap.sum_apply, comp_apply, fᵢ, gᵢ, proj_apply, single_apply]
    have hp : (∑ i, Pi.single i (f a i)) = f a := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    rw [← map_sum, hp]
    exact DFunLike.congr_fun h a
  have hunit : IsUnit (∑ i, (gᵢ i).comp (fᵢ i)) := hsum.symm ▸ isUnit_one
  obtain ⟨i, _, u, hu⟩ := IsLocalRing.exists_of_isUnit_sum hunit
  let r := (u⁻¹).val.comp (gᵢ i)
  have hr : r.comp (fᵢ i) = LinearMap.id := by
    ext a
    change (u⁻¹ : (Module.End R A)ˣ).val (((gᵢ i).comp (fᵢ i)) a) = a
    rw [← hu]
    exact (LinearMap.GeneralLinearGroup.toLinearEquiv u).symm_apply_apply a
  exact ⟨LinearMap.ker r, ⟨equivOfSection (fᵢ i) r hr⟩⟩

/-- An isomorphism of the same positive number of copies of two finite-dimensional
modules over a field algebra implies an isomorphism of the modules. -/
theorem nonempty_linearEquiv_of_copies (K : Type u) [Field K] [Algebra K R]
    [Module K M] [IsScalarTower K R M] [Module.Finite K M]
    [Module K N] [IsScalarTower K R N] [Module.Finite K N]
    {d : ℕ} (hd : 0 < d) (e : (Fin d → M) ≃ₗ[R] (Fin d → N)) : Nonempty (M ≃ₗ[R] N) := by
  classical
  let P (k : ℕ) : Prop := ∀ (M N : Type v) [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module R N] [Module K M] [IsScalarTower K R M] [Module.Finite K M]
      [Module K N] [IsScalarTower K R N] [Module.Finite K N], Module.finrank K M = k →
      ((Fin d → M) ≃ₗ[R] (Fin d → N)) → Nonempty (M ≃ₗ[R] N)
  have key (k : ℕ) : P k := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro X Y _ _ _ _ _ _ _ _ _ _ hX e
      let i : Fin d := ⟨0, hd⟩
      rcases subsingleton_or_nontrivial X with hsub | hnontriv
      · have : Subsingleton (Fin d → X) := inferInstance
        have : Subsingleton (Fin d → Y) := e.symm.injective.subsingleton
        have hconst : Function.Injective (fun y : Y => fun _ : Fin d => y) :=
          fun _ _ h => congrFun h i
        have : Subsingleton Y := hconst.subsingleton
        exact ⟨LinearEquiv.ofSubsingleton X Y⟩
      · obtain ⟨p, q, hpq, hp, hpind⟩ := exists_indecomposable_summand (K := K) (R := R) (M := X)
        have : Module.Finite K p := finite_submodule p
        have : Module.Finite K q := finite_submodule q
        let a := Submodule.prodEquivOfIsCompl p q hpq
        let f := e.toLinearMap.comp ((LinearMap.single R (fun _ => X) i).comp p.subtype)
        let g := (p.projectionOnto q hpq).comp ((LinearMap.proj i).comp e.symm.toLinearMap)
        have hfg : g.comp f = LinearMap.id := by
          ext x
          simp [f, g]
        obtain ⟨s, ⟨b⟩⟩ := split_of_copies (K := K) hpind f g hfg
        have : Module.Finite K s := finite_submodule s
        let reindex (U V : Type v) [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] :
            (Fin d → U × V) ≃ₗ[R] (Fin d → U) × (Fin d → V) :=
          { toFun := fun x => (fun i => (x i).1, fun i => (x i).2)
            invFun := fun x i => (x.1 i, x.2 i)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        let e' := (reindex p q).symm.trans
          ((LinearEquiv.piCongrRight (fun _ => a)).trans (e.trans
            ((LinearEquiv.piCongrRight (fun _ => b.symm)).trans (reindex p s))))
        obtain ⟨e''⟩ := cancel_indecomposable_copies (K := K) hpind d e'
        have hdim := (a.restrictScalars K).finrank_eq
        rw [Module.finrank_prod, hX] at hdim
        have hpdim : 0 < Module.finrank K p := Module.finrank_pos
        obtain ⟨e'''⟩ := ih (Module.finrank K q) (by omega : Module.finrank K q < k) q s rfl e''
        exact ⟨a.symm.trans (((LinearEquiv.refl R p).prodCongr e''').trans b)⟩
  exact key (Module.finrank K M) M N rfl e

end

section Operators

variable {K : Type u} [Field K] {ι : Type w}
  {X Y : Type v} [AddCommGroup X] [Module K X] [Module.Finite K X]
  [AddCommGroup Y] [Module K Y] [Module.Finite K Y]

/-- Simultaneous intertwining of families of endomorphisms descends from a positive number
of copies. The free algebra on the indexing type acts through the specified operators. -/
theorem exists_intertwiningEquiv_of_copies {d : ℕ} (hd : 0 < d)
    (S : ι → Module.End K X) (T : ι → Module.End K Y)
    (e : (Fin d → X) ≃ₗ[K] (Fin d → Y))
    (he : ∀ j x i, e (fun a => S j (x a)) i = T j (e x i)) :
    ∃ e₀ : X ≃ₗ[K] Y, ∀ j x, e₀ (S j x) = T j (e₀ x) := by
  let R := FreeAlgebra K ι
  let s : R →ₐ[K] Module.End K X := FreeAlgebra.lift K S
  let t : R →ₐ[K] Module.End K Y := FreeAlgebra.lift K T
  have hs (j : ι) : s (FreeAlgebra.ι K j) = S j := FreeAlgebra.lift_ι_apply S j
  have ht (j : ι) : t (FreeAlgebra.ι K j) = T j := FreeAlgebra.lift_ι_apply T j
  let : Module R X := Module.compHom X s.toRingHom
  let : Module R Y := Module.compHom Y t.toRingHom
  have : IsScalarTower K R X := IsScalarTower.of_algebraMap_smul fun k x => by
    change (s (algebraMap K R k)) x = k • x
    rw [s.commutes, Module.algebraMap_end_apply]
  have : IsScalarTower K R Y := IsScalarTower.of_algebraMap_smul fun k y => by
    change (t (algebraMap K R k)) y = k • y
    rw [t.commutes, Module.algebraMap_end_apply]
  have hh (r : R) : ∀ x : Fin d → X, e (r • x) = r • e x := by
    induction r using FreeAlgebra.induction with
    | grade0 k =>
      intro x
      change e ((algebraMap K R k) • x) = (algebraMap K R k) • e x
      rw [algebraMap_smul, algebraMap_smul, map_smul]
    | grade1 j =>
      intro x
      funext i
      change e (fun a => s (FreeAlgebra.ι K j) (x a)) i = t (FreeAlgebra.ι K j) (e x i)
      rw [hs, ht]
      exact he j x i
    | mul a b ha hb => intro x; rw [mul_smul, ha, hb, mul_smul]
    | add a b ha hb => intro x; rw [add_smul, map_add, ha, hb, add_smul]
  let eR : (Fin d → X) ≃ₗ[R] (Fin d → Y) :=
    { e.toAddEquiv with map_smul' := fun r x => hh r x }
  obtain ⟨e₀⟩ := nonempty_linearEquiv_of_copies K hd eR
  refine ⟨e₀.restrictScalars K, fun j x => ?_⟩
  have h := e₀.map_smul (FreeAlgebra.ι K j) x
  change e₀ (s (FreeAlgebra.ι K j) x) = t (FreeAlgebra.ι K j) (e₀ x) at h
  rw [hs, ht] at h
  exact h

end Operators

end Langlands.FiniteModuleCancellation

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
import WeilConjectures.AlgebraicGeometry.DirectedColimitBaseChangeElementwise

/-! # Canonical descent of a single finitely presented module map

Source: Stacks Project, Algebra Tag 05N7 (2), used in Perfect Tag 09RE (1).
(blueprint: lem-pc-fp-module-map-canonical-preorder)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Lift a map from a finitely presented module through a directed system with the
representative and eventual-zero properties. Lift the finite generators together,
then move to one stage killing the images of the finitely many kernel generators.
Source: Stacks Project, Algebra Tag 05LI (3). -/
private theorem fp_lift
    {R : Type u} [CommRing R] {J : Type u} [Preorder J] [Nonempty J]
    [IsDirected J (· ≤ ·)] (D : J → Type u)
    [∀ i, AddCommGroup (D i)] [∀ i, Module R (D i)]
    (d : ∀ {i j : J}, i ≤ j → D i →ₗ[R] D j)
    (dc : ∀ {i j k : J} (hij : i ≤ j) (hjk : j ≤ k) (x : D i),
      d hjk (d hij x) = d (hij.trans hjk) x)
    {P : Type u} [AddCommGroup P] [Module R P] (μ : ∀ i, D i →ₗ[R] P)
    (hc : ∀ {i j : J} (hij : i ≤ j) (x : D i), μ j (d hij x) = μ i x)
    (hs : ∀ x : P, ∃ i, ∃ y : D i, μ i y = x)
    (hz : ∀ i (x : D i), μ i x = 0 → ∃ j, ∃ hij : i ≤ j, d hij x = 0)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (h : M →ₗ[R] P) : ∃ i, ∃ a : M →ₗ[R] D i, (μ i).comp a = h := by
  classical
  have finite_lift (s : Finset P) : ∃ i, ∀ x ∈ s, ∃ y : D i, μ i y = x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨Classical.arbitrary J, by simp⟩
    | @insert x s hxs ih =>
      obtain ⟨i, y, hy⟩ := hs x
      obtain ⟨j, hj⟩ := ih
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      refine ⟨k, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ⟨d hik y, (hc hik y).trans hy⟩
      · obtain ⟨y, hy⟩ := hj z hz
        exact ⟨d hjk y, (hc hjk y).trans hy⟩
  have finite_zero (i : J) (s : Finset (D i)) (hs : ∀ x ∈ s, μ i x = 0) :
      ∃ j, ∃ hij : i ≤ j, ∀ x ∈ s, d hij x = 0 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨i, le_rfl, by simp⟩
    | @insert x s hxs ih =>
      obtain ⟨j, hij, hj⟩ := hz i x (hs x (Finset.mem_insert_self _ _))
      obtain ⟨k, hik, hk⟩ := ih (fun y hy ↦ hs y (Finset.mem_insert_of_mem hy))
      obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
      refine ⟨l, hij.trans hjl, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [← dc hij hjl, hj, map_zero]
      · have he := dc hik hkl y
        rw [hk y hy, map_zero] at he
        exact he.symm
  -- A finite free cover and a finite generating set for its kernel.
  obtain ⟨σ, ⟨hσ, hτ⟩⟩ := (inferInstance : Module.FinitePresentation R M)
  obtain ⟨τ, hτ⟩ := hτ
  let π := Finsupp.linearCombination R ((↑) : σ → M)
  have hπ : Function.Surjective π :=
    LinearMap.range_eq_top.mp (by rw [Finsupp.range_linearCombination, Subtype.range_val, ← hσ])
  obtain ⟨i, hi⟩ := finite_lift (σ.image h)
  have hlift (x : σ) : ∃ y : D i, μ i y = h x :=
    hi (h x) (Finset.mem_image.mpr ⟨x, x.property, rfl⟩)
  choose v hv using hlift
  let a₀ := Finsupp.linearCombination R v
  have ha₀ : (μ i).comp a₀ = h.comp π := by
    ext x
    simpa [a₀, π] using hv x
  have hrel (x : τ) : μ i (a₀ x) = 0 := by
    change ((μ i).comp a₀) x = 0
    rw [ha₀, LinearMap.comp_apply]
    have hx : π x = 0 := by
      rw [← LinearMap.mem_ker, ← hτ]
      exact Submodule.subset_span x.property
    rw [hx, map_zero]
  obtain ⟨j, hij, hj⟩ := finite_zero i (τ.image a₀) (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hrel ⟨x, hx⟩)
  let b := (d hij).comp a₀
  have hker : LinearMap.ker π ≤ LinearMap.ker b := by
    rw [← hτ, Submodule.span_le]
    intro x hx
    exact hj (a₀ x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  -- The transported map kills the whole kernel, so descends through the quotient.
  let a := (LinearMap.ker π).liftQ b hker ∘ₗ
    (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap
  refine ⟨j, a, ?_⟩
  apply LinearMap.ext
  intro m
  obtain ⟨x, rfl⟩ := hπ m
  change μ j (a (π x)) = h (π x)
  have hax : a (π x) = b x := by simp [a]
  rw [hax]
  exact (hc hij (a₀ x)).trans (LinearMap.congr_fun ha₀ x)


open scoped ChangeOfRings TensorProduct in
/-- The canonical comparison, including transport along equality of ring maps,
sends a unit tensor to the iterated unit tensor. -/
private theorem comparison_one
    {S A R : Type u} [CommRing S] [CommRing A] [CommRing R]
    (r : S →+* A) (s : A →+* R) (t : S →+* R) (hc : s.comp r = t)
    (X : ModuleCat.{u} S) (x : X) :
    let e := eqToIso (congrArg (fun q ↦ (extendScalars q).obj X) hc.symm) ≪≫
      (extendScalarsComp r s).app X
    e.hom ((1 : R) ⊗ₜ[S, t] x) = (1 : R) ⊗ₜ[A, s] ((1 : A) ⊗ₜ[S, r] x) := by
  subst t
  exact extendScalarsComp_hom_app_one_tmul r s X x

/-- A single map over a directed ring colimit lifts at a stage above the initial one,
with the canonical scalar-extension comparison.

Source: Stacks Project, Algebra Tag 05N7 (2); Perfect Tag 09RE, affine case (1).
Proof: Choose finite generators and finite relations for M and N. Express the images
of the generators of M as finite linear combinations of the generators of N over the
colimit ring. Lift all these coefficients to a common stage above i₀, using the
filtered-ring elementwise criterion. Each relation of M maps to zero in N over the
colimit, so express it as a finite combination of the defining relations of N and
lift those coefficients too. The resulting finitely many coefficient equations
hold at a common later stage by the same criterion. They define a map at that stage.
The two canonical comparison maps send 1 tensor x to 1 tensor (1 tensor x), so the
lift has the asserted conjugated extension, by linearity and generation by pure
tensors. Only directedness and finite lists of coefficients and relations enter,
so this argument works for a preorder, including mutually comparable distinct indices.
If M or N is zero the same presentation argument applies, and the unique zero map
also gives the result.
(blueprint: lem-pc-fp-module-map-canonical-preorder) -/
theorem finitePresentation_map_directedColimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I) (M N : ModuleCat.{u} (F.obj i₀))
    (hM : Module.FinitePresentation (F.obj i₀) M)
    (hN : Module.FinitePresentation (F.obj i₀) N)
    (f : (extendScalars (colimit.ι F i₀).hom).obj M ⟶
      (extendScalars (colimit.ι F i₀).hom).obj N) :
    let e (i : Set.Ici i₀) (X : ModuleCat.{u} (F.obj i₀)) :=
      eqToIso (congrArg (fun r ↦ (extendScalars r).obj X)
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm)) ≪≫
      (extendScalarsComp (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom).app X
    ∃ i : Set.Ici i₀,
      ∃ g : (extendScalars (F.map (homOfLE i.property)).hom).obj M ⟶
        (extendScalars (F.map (homOfLE i.property)).hom).obj N,
        (e i M).hom ≫ (extendScalars (colimit.ι F i.val).hom).map g ≫ (e i N).inv = f := by
  classical
  let _ : Module.FinitePresentation (F.obj i₀) N := hN
  let e (i : Set.Ici i₀) (X : ModuleCat.{u} (F.obj i₀)) :=
    eqToIso (congrArg (fun r ↦ (extendScalars r).obj X)
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm)) ≪≫
    (extendScalarsComp (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom).app X
  change ∃ i : Set.Ici i₀, ∃ g,
    (e i M).hom ≫ (extendScalars (colimit.ι F i.val).hom).map g ≫ (e i N).inv = f
  let S := F.obj i₀
  let R := colimit F
  let J := Set.Ici i₀
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let : Algebra S R := (colimit.ι F i₀).hom.toAlgebra
  let A (i : J) := F.obj i.val
  let : ∀ i, CommRing (A i) := fun i ↦ inferInstance
  let : ∀ i, Algebra S (A i) := fun i ↦ (F.map (homOfLE i.property)).hom.toAlgebra
  let D (i : J) := TensorProduct S (A i) N
  let α (i : J) : A i →ₐ[S] R :=
    { (colimit.ι F i.val).hom with
      commutes' := fun s ↦ congrArg (fun p : F.obj i₀ ⟶ colimit F ↦ p s)
        (colimit.w F (homOfLE i.property)) }
  let β {i j : J} (hij : i ≤ j) : A i →ₐ[S] A j :=
    { (F.map (homOfLE hij)).hom with
      commutes' := fun s ↦ congrArg (fun p : F.obj i₀ ⟶ F.obj j.val ↦ p s)
        (F.map_comp (homOfLE i.property) (homOfLE hij)).symm }
  let d {i j : J} (hij : i ≤ j) : D i →ₗ[S] D j := (β hij).toLinearMap.rTensor N
  let μ (i : J) : D i →ₗ[S] TensorProduct S R N := (α i).toLinearMap.rTensor N
  have dc {i j k : J} (hij : i ≤ j) (hjk : j ≤ k) (x : D i) :
      d hjk (d hij x) = d (hij.trans hjk) x := by
    induction x using TensorProduct.inductionOn with
    | tmul a n =>
      simp only [d]
      exact congrArg (fun a ↦ TensorProduct.tmul S a n)
        (ConcreteCategory.congr_hom (F.map_comp (homOfLE hij) (homOfLE hjk)) a).symm
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hc {i j : J} (hij : i ≤ j) (x : D i) : μ j (d hij x) = μ i x := by
    induction x using TensorProduct.inductionOn with
    | tmul a n =>
      simp only [d, μ]
      exact congrArg (fun a ↦ TensorProduct.tmul S a n)
        (ConcreteCategory.congr_hom (colimit.w F (homOfLE hij)) a)
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hs : ∀ x : TensorProduct S R N, ∃ i : J, ∃ y : D i, μ i y = x := by
    intro x
    obtain ⟨i, hi, y, hy⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise F i₀ N).1 x
    exact ⟨⟨i, hi⟩, y, hy⟩
  have hz : ∀ (i : J) (x : D i), μ i x = 0 →
      ∃ j : J, ∃ hij : i ≤ j, d hij x = 0 := by
    intro i x hx
    obtain ⟨j, hij, hj⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise F i₀ N).2 i.val i.property x hx
    exact ⟨⟨j, i.property.trans hij⟩, hij, hj⟩
  let : Module.FinitePresentation S M := hM
  let f' : TensorProduct S R M →ₗ[R] TensorProduct S R N := f.hom
  -- Uncurry f over the initial ring; only the source needs finite presentation.
  let h : M →ₗ[S] TensorProduct S R N :=
    (f'.restrictScalars S).comp (TensorProduct.mk S R M 1)
  obtain ⟨i, a, ha⟩ := fp_lift D d dc μ hc hs hz M h
  let g : (extendScalars (F.map (homOfLE i.property)).hom).obj M ⟶
      (extendScalars (F.map (homOfLE i.property)).hom).obj N :=
    ofHom (a.liftBaseChange (A i))
  let : ∀ j, Algebra (A j) R := fun j ↦ (colimit.ι F j.val).hom.toAlgebra
  have he (j : J) (X : ModuleCat.{u} S) (x : X) :
      (e j X).hom (TensorProduct.tmul S (1 : R) x) =
        TensorProduct.tmul (A j) (1 : R)
          (TensorProduct.tmul S (1 : A j) x) :=
    comparison_one _ _ _
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property))) X x
  -- Identify the elementwise coprojection with the canonical iterated extension.
  have heμ (x : D i) :
      (e i N).hom (μ i x) = TensorProduct.tmul (A i) (1 : R) x := by
    change (e i N).hom.hom (μ i x) = _
    induction x using TensorProduct.inductionOn with
    | tmul b n =>
      rw [show μ i (TensorProduct.tmul S b n) = (α i b) • (TensorProduct.tmul S (1 : R) n) by
        change TensorProduct.tmul S (α i b) n = _
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      rw [map_smul]
      change (α i b) • ((e i N).hom (TensorProduct.tmul S (1 : R) n)) = _
      rw [he]
      let : Algebra (A i) R := (colimit.ι F i.val).hom.toAlgebra
      change (algebraMap (A i) R b) •
        (TensorProduct.tmul (A i) (1 : R) (TensorProduct.tmul S (1 : A i) n)) = _
      rw [algebraMap_smul, ← TensorProduct.tmul_smul]
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy =>
      simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hx hy
  refine ⟨i, g, ?_⟩
  rw [← cancel_mono (e i N).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply ExtendScalars.hom_ext
  intro m
  change (extendScalars (colimit.ι F i.val).hom).map g
      ((e i M).hom (TensorProduct.tmul S (1 : R) m)) =
    (e i N).hom (f (TensorProduct.tmul S (1 : R) m))
  rw [he, ExtendScalars.map_tmul]
  change TensorProduct.tmul (A i) (1 : R)
    ((a.liftBaseChange (A i)) (TensorProduct.tmul S (1 : A i) m)) = (e i N).hom (h m)
  rw [LinearMap.liftBaseChange_one_tmul, ← LinearMap.congr_fun ha m]
  exact (heμ (a m)).symm

end ModuleCat

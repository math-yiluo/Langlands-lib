/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private lemma telescope_injective (R : Type u) [CommRing R]
    (M : ULift.{v} ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n, M n →ₗ[R] M ⟨n.down + 1⟩) :
    Function.Injective (DFinsupp.lsum R (fun n : ULift.{v} ℕ ↦
      DFinsupp.lsingle (R := R) (M := M) n -
        (DFinsupp.lsingle (R := R) (M := M) ⟨n.down + 1⟩).comp (t n))) := by
  classical
  let a : (Π₀ n, M n) →ₗ[R] (Π₀ n, M n) := DFinsupp.lsum R (fun n : ULift.{v} ℕ ↦
    DFinsupp.lsingle (R := R) (M := M) n -
        (DFinsupp.lsingle (R := R) (M := M) ⟨n.down + 1⟩).comp (t n))
  have hzero (x : Π₀ n, M n) : a x ⟨0⟩ = x ⟨0⟩ := by
    induction x using DFinsupp.induction with
    | h0 => simp
    | ha i x f hi hx ih =>
      simp only [map_add, DFinsupp.add_apply, ih]
      congr 1
      simp [a, DFinsupp.single_apply]
  have hsucc (x : Π₀ n, M n) (n : ℕ) :
      a x ⟨n + 1⟩ = x ⟨n + 1⟩ - t ⟨n⟩ (x ⟨n⟩) := by
    induction x using DFinsupp.induction with
    | h0 => simp
    | ha i x f hi hx ih =>
      simp only [map_add, DFinsupp.add_apply, ih]
      have hs : a (DFinsupp.single i x) ⟨n + 1⟩ =
          (DFinsupp.single i x) ⟨n + 1⟩ - t ⟨n⟩ ((DFinsupp.single i x) ⟨n⟩) := by
        by_cases h : i = ⟨n⟩
        · subst i
          simp [a]
        · have hn : (⟨i.down + 1⟩ : ULift.{v} ℕ) ≠ ⟨n + 1⟩ := by
            intro he
            apply h
            cases i
            simpa using he
          simp [a, DFinsupp.single_apply, h, hn]
      rw [hs]
      abel
  change Function.Injective a
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hh (n : ℕ) : x ⟨n⟩ = 0 := by
    induction n with
    | zero => simpa only [hx, DFinsupp.zero_apply] using (hzero x).symm
    | succ n ih =>
      have := hsucc x n
      simpa [hx, ih] using this.symm
  ext ⟨n⟩
  exact hh n

private lemma telescope_kernel (R : Type u) [CommRing R]
    (M : ULift.{v} ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (L : Type v) [AddCommGroup L] [Module R L]
    (t : ∀ n, M n →ₗ[R] M ⟨n.down + 1⟩)
    (ι : ∀ n, M n →ₗ[R] L)
    (hi : ∀ n, Function.Injective (ι n))
    (ht : ∀ n x, ι ⟨n.down + 1⟩ (t n x) = ι n x)
    (x : Π₀ n, M n) (hx : DFinsupp.lsum R ι x = 0) :
    x ∈ LinearMap.range (DFinsupp.lsum R (fun n : ULift.{v} ℕ ↦
      DFinsupp.lsingle (R := R) (M := M) n -
        (DFinsupp.lsingle (R := R) (M := M) ⟨n.down + 1⟩).comp (t n))) := by
  classical
  let a : (Π₀ n, M n) →ₗ[R] (Π₀ n, M n) := DFinsupp.lsum R (fun n ↦
    DFinsupp.lsingle (R := R) (M := M) n -
      (DFinsupp.lsingle (R := R) (M := M) ⟨n.down + 1⟩).comp (t n))
  let q := (LinearMap.range a).mkQ
  have rel (n : ULift.{v} ℕ) (z : M n) :
      q (DFinsupp.single n z) = q (DFinsupp.single ⟨n.down + 1⟩ (t n z)) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨DFinsupp.single n z, ?_⟩
    simp [a]
  have raise (n m : ℕ) (hnm : n ≤ m) (z : M ⟨n⟩) :
      ∃ z' : M ⟨m⟩,
        q (DFinsupp.single ⟨n⟩ z) = q (DFinsupp.single ⟨m⟩ z') ∧
          ι ⟨n⟩ z = ι ⟨m⟩ z' := by
    induction m, hnm using Nat.le_induction with
    | base => exact ⟨z, rfl, rfl⟩
    | succ m hnm ih =>
      obtain ⟨z', hq, hι⟩ := ih
      exact ⟨t ⟨m⟩ z', hq.trans (rel ⟨m⟩ z'), hι.trans (ht ⟨m⟩ z').symm⟩
  have rep (y : Π₀ n, M n) :
      ∃ (n : ℕ) (z : M ⟨n⟩), q y = q (DFinsupp.single ⟨n⟩ z) ∧
        DFinsupp.lsum R ι y = ι ⟨n⟩ z := by
    induction y using DFinsupp.induction with
    | h0 => exact ⟨0, 0, by simp, by simp⟩
    | ha i z y hi hz ih =>
      obtain ⟨n, z', hq, hι⟩ := ih
      let N := max i.down n
      obtain ⟨w, hwq, hwι⟩ := raise i.down N (Nat.le_max_left _ _) z
      obtain ⟨w', hwq', hwι'⟩ := raise n N (Nat.le_max_right _ _) z'
      refine ⟨N, w + w', ?_, ?_⟩
      · rw [map_add, hq, hwq, hwq', ← map_add, ← DFinsupp.single_add]
      · simp only [map_add, DFinsupp.lsum_single, hι, hwι, hwι']
  obtain ⟨n, z, hq, hι⟩ := rep x
  have hz : z = 0 := hi ⟨n⟩ (by simpa [hx] using hι.symm)
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change q x = 0
  simp [hq, hz]

/-- The algebraic short exact sequence underlying the filtration telescope.
Source: Stacks Project, More on Algebra, Remark 09PB (remark-P-resolution),
displayed telescope triangle.
(blueprint: lem-pc-derived-module-filtration-telescope).

Proof: coproducts of complexes are computed degreewise. In each degree write a
coproduct element as a finitely supported tuple. The map `a` sends the element `x`
in summand `n` to `x` in summand `n` minus `step n x` in summand `n + 1`.
If `a x = 0`, its component at zero vanishes; induction on the component number
then gives every component of `x` zero, so `a` is injective. Exhaustiveness says
that the map `b` induced by the inclusions is surjective. For a tuple `x` with
`b x = 0`, choose `N` at least as large as every index in its support. Modulo the
image of `a`, move each component successively into summand `N` using the relation
`z` in summand `n` equals `step n z` in summand `n + 1`. The resulting tuple has
only one component `z` in summand `N`; its image in `L` remains zero. Monicity of
`ι N`, hence degreewise injectivity, gives `z = 0`. Therefore `ker b = im a`.
The three degreewise statements imply short exactness of complexes. The supplied
`hzero` only packages the already compatible maps as a short complex. -/
private lemma filtration_telescope_shortExact (R : Type u) [CommRing R]
    (L : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} R) ℤ)
    (ι : ∀ n, F n ⟶ L) (step : ∀ n, F n ⟶ F (n + 1))
    (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : L.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hzero :
      (Sigma.desc (fun n : ULift.{max u v} ℕ ↦
        Sigma.ι (fun n : ULift.{max u v} ℕ ↦ F n.down) n -
          step n.down ≫ Sigma.ι (fun n : ULift.{max u v} ℕ ↦ F n.down)
            ⟨n.down + 1⟩)) ≫
        Sigma.desc (fun n : ULift.{max u v} ℕ ↦ ι n.down) = 0) :
    (ShortComplex.mk _ _ hzero).ShortExact := by
  classical
  let K := fun n : ULift.{max u v} ℕ ↦ F n.down
  let a : ∐ K ⟶ ∐ K := Sigma.desc (fun n ↦
    Sigma.ι K n - step n.down ≫ Sigma.ι K ⟨n.down + 1⟩)
  let b : ∐ K ⟶ L := Sigma.desc (fun n ↦ ι n.down)
  change (ShortComplex.mk a b hzero).ShortExact
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro k
  let Z := fun n : ULift.{max u v} ℕ ↦ (F n.down).X k
  let hc : IsColimit (Cofan.mk ((∐ K).X k) (fun n ↦ (Sigma.ι K n).f k)) :=
    isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.up ℤ) k) K
  let hd := ModuleCat.coproductCoconeIsColimit Z
  let e : (∐ K).X k ≅ ModuleCat.of R (Π₀ n, Z n) :=
    hc.coconePointUniqueUpToIso hd
  have he (n : ULift.{max u v} ℕ) :
      (Sigma.ι K n).f k ≫ e.hom =
        ModuleCat.ofHom (DFinsupp.lsingle (R := R) (M := fun n ↦ Z n) n) := by
    simpa [ModuleCat.coproductCocone, DirectSum.lof] using
      hc.comp_coconePointUniqueUpToIso_hom hd ⟨n⟩
  let t := fun n : ULift.{max u v} ℕ ↦ ((step n.down).f k).hom
  let i := fun n : ULift.{max u v} ℕ ↦ ((ι n.down).f k).hom
  let A : (Π₀ n, Z n) →ₗ[R] (Π₀ n, Z n) := DFinsupp.lsum R (fun n ↦
    DFinsupp.lsingle (R := R) (M := fun n ↦ Z n) n -
      (DFinsupp.lsingle (R := R) (M := fun n ↦ Z n) ⟨n.down + 1⟩).comp (t n))
  let B : (Π₀ n, Z n) →ₗ[R] L.X k := DFinsupp.lsum R i
  have hai (n : ULift.{max u v} ℕ) :
      (Sigma.ι K n).f k ≫ a.f k = (Sigma.ι K n).f k -
        (step n.down).f k ≫ (Sigma.ι K ⟨n.down + 1⟩).f k := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply] using
      congrArg (fun f ↦ f.f k)
      (Sigma.ι_comp_desc (fun n ↦ Sigma.ι K n -
        step n.down ≫ Sigma.ι K ⟨n.down + 1⟩) n)
  have hbi (n : ULift.{max u v} ℕ) :
      (Sigma.ι K n).f k ≫ b.f k = (ι n.down).f k := by
    simpa only [HomologicalComplex.comp_f] using
      congrArg (fun f ↦ f.f k)
      (Sigma.ι_comp_desc (fun n ↦ ι n.down) n)
  have ha : a.f k ≫ e.hom = e.hom ≫ ModuleCat.ofHom A := by
    apply hc.hom_ext
    intro ⟨n⟩
    change (Sigma.ι K n).f k ≫ (a.f k ≫ e.hom) =
      (Sigma.ι K n).f k ≫ (e.hom ≫ ModuleCat.ofHom A)
    rw [← Category.assoc, hai, Preadditive.sub_comp, Category.assoc]
    rw [he, he, ← Category.assoc, he]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change DFinsupp.single n x - DFinsupp.single ⟨n.down + 1⟩ (t n x) =
      A (DFinsupp.single n x)
    dsimp only [A]
    rw [DFinsupp.lsum_single]
    rfl
  have hb : b.f k = e.hom ≫ ModuleCat.ofHom B := by
    apply hc.hom_ext
    intro ⟨n⟩
    change (Sigma.ι K n).f k ≫ b.f k =
      (Sigma.ι K n).f k ≫ (e.hom ≫ ModuleCat.ofHom B)
    rw [hbi, ← Category.assoc, he]
    ext x
    change i n x = B (DFinsupp.single n x)
    exact (DFinsupp.lsum_single R i n x).symm
  have hae (x : (∐ K).X k) : e.hom (a.f k x) = A (e.hom x) :=
    congrArg (fun f ↦ f x) ha
  have hbe (x : (∐ K).X k) : b.f k x = B (e.hom x) :=
    congrArg (fun f ↦ f x) hb
  have hinj : Function.Injective e.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hAi : Function.Injective A := telescope_injective R (fun n ↦ Z n) t
  have hmi (n : ULift.{max u v} ℕ) : Function.Injective (i n) := by
    have := hmono n.down
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  have hti (n : ULift.{max u v} ℕ) (x : Z n) :
      i ⟨n.down + 1⟩ (t n x) = i n x := by
    exact congrArg (fun f ↦ f.f k x) (hcompat n.down)
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    have hx' : B (e.hom x) = 0 := (hbe x).symm.trans hx
    obtain ⟨y, hy⟩ := telescope_kernel R (fun n ↦ Z n) (L.X k) t i hmi hti
      (e.hom x) hx'
    refine ⟨e.inv y, ?_⟩
    apply hinj
    change e.hom (a.f k (e.inv y)) = e.hom x
    rw [hae]
    have hey : e.hom (e.inv y) = y := by
      exact congrArg (fun f ↦ f y) e.inv_hom_id
    rw [hey]
    exact hy
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro x y hxy
    change a.f k x = a.f k y at hxy
    exact hinj (hAi (by rw [← hae, ← hae, hxy]))
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    obtain ⟨n, y, hy⟩ := hexhaustive k x
    refine ⟨(Sigma.ι K ⟨n⟩).f k y, ?_⟩
    exact (congrArg (fun f ↦ f y) (hbi ⟨n⟩)).trans hy

/-- An exhaustive filtration by subcomplexes gives the mapping telescope triangle.
Source: Stacks Project, More on Algebra, Remark 15.60.11 (Tag 09PB), displayed triangle.
(blueprint: lem-pc-derived-module-filtration-telescope).

Proof: form the termwise direct sum `S₀` of the `F n`. Let `s` send summand `n` to
summand `n+1` via `step n`, and let `p : S₀ ⟶ L` be induced by the compatible `ι n`.
In each degree the sequence `0 → S₀ → S₀ → L → 0`, with maps `1-s` and `p`, is exact.
Injectivity of `1-s` follows by inspecting components successively starting at zero.
Surjectivity of `p` is exhaustiveness. If a finitely supported tuple is in its kernel,
choose a filtration stage beyond its support. Moving each component to that stage
changes the tuple by an element of the image of `1-s`; the resulting component is zero
because the inclusion of that stage into `L` is injective. Thus `ker p = im (1-s)`.
Apply `DerivedCategory.triangleOfSES_distinguished` to this short exact sequence.
Use `derivedModuleDirectSums` to make `Q(S₀)` a coproduct of the `Q(F n)`.
Reindex this coproduct along the equivalence `ULift ℕ ≃ ℕ` to place its index in the
module universe. This supplies `S`, `j`, and the distinguished triangle in the conclusion.
This construction uses neither free modules nor a property of derived objects. -/
theorem derivedModuleFiltrationTelescope (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (L : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} R) ℤ)
    (ι : ∀ n, F n ⟶ L) (step : ∀ n, F n ⟶ F (n + 1))
    (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : L.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x) :
    ∃ (S : DerivedCategory (ModuleCat.{max u v} R))
      (j : ∀ n : ULift.{max u v} ℕ, DerivedCategory.Q.obj (F n.down) ⟶ S),
      Nonempty (IsColimit (Cofan.mk S j)) ∧
      ∃ (a : S ⟶ S) (b : S ⟶ DerivedCategory.Q.obj L)
        (c : DerivedCategory.Q.obj L ⟶ S⟦(1 : ℤ)⟧),
        Pretriangulated.Triangle.mk a b c ∈ Pretriangulated.distinguishedTriangles := by
  let K := fun n : ULift.{max u v} ℕ ↦ F n.down
  let a : ∐ K ⟶ ∐ K := Sigma.desc (fun n ↦
    Sigma.ι K n - step n.down ≫ Sigma.ι K ⟨n.down + 1⟩)
  let b : ∐ K ⟶ L := Sigma.desc (fun n ↦ ι n.down)
  have hzero : a ≫ b = 0 := by
    apply Sigma.hom_ext
    intro n
    simp [a, b, Preadditive.sub_comp, hcompat]
  have hses := filtration_telescope_shortExact R L F ι step hmono hcompat
    hexhaustive hzero
  refine ⟨DerivedCategory.Q.obj (∐ K),
    (fun n ↦ DerivedCategory.Q.map (Sigma.ι K n)),
    derivedModuleDirectSums R (ULift.{max u v} ℕ) K,
    DerivedCategory.Q.map a, DerivedCategory.Q.map b,
    DerivedCategory.triangleOfSESδ hses, ?_⟩
  exact DerivedCategory.triangleOfSES_distinguished hses

end CategoryTheory

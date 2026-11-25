/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.Mathlib.RingTheory.MatrixAlgebra
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel

/-!
# Independence of the scalar-defect class for a fixed central simple algebra

Source: Stacks Project, the construction between Tags 03R6 and 03R7, and Tag 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-unique).
-/

@[expose] public section

universe u

namespace Field

open CategoryTheory TopRep in
private lemma rho_mul {R : Type*} [CommRing R] [TopologicalSpace R]
    {G : Type*} [Group G] (M : TopRep R G) (g h : G) (a : M) : M.ρ g (M.ρ h a) = M.ρ (g * h) a :=
  (congrArg (fun t ↦ t a) (M.ρ.toMonoidHom.map_mul g h)).symm
open CategoryTheory TopRep in
private lemma equivariant {R : Type*} [CommRing R] [TopologicalSpace R]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : TopRep R G) (f : (homogeneousCochains M).X 2) (g a b c : G) :
    M.ρ g (f.val a b c) = f.val (g * a) (g * b) (g * c) := by
  have h := DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun
    ((ContRepresentation.mem_invariants _).mp f.property g) (g * a)) (g * b)) (g * c)
  simpa using h
open CategoryTheory TopRep in
private def oneCochain {R : Type*} [CommRing R] [TopologicalSpace R]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : TopRep R G) (hc : Continuous (fun p : G × M ↦ M.ρ p.1 p.2))
    (c : C(G, M)) : (homogeneousCochains M).X 1 := by
  let F : C(G × G, M) :=
    ⟨fun p ↦ M.ρ p.1 (c (p.1⁻¹ * p.2)),
      hc.comp (continuous_fst.prodMk (c.continuous.comp (by fun_prop)))⟩
  refine ⟨F.curry, ?_⟩
  apply (ContRepresentation.mem_invariants _).mpr
  intro g
  ext a b
  change M.ρ g (M.ρ (g⁻¹ * a) (c ((g⁻¹ * a)⁻¹ * (g⁻¹ * b)))) =
    M.ρ a (c (a⁻¹ * b))
  simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  rw [rho_mul, mul_inv_cancel_left]
open CategoryTheory TopRep in
private lemma cochain_eq_of_coordinates {R : Type*} [CommRing R] [TopologicalSpace R]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : TopRep R G)
    (f t : (homogeneousCochains M).X 2)
    (h : ∀ g h, f.val 1 g (g * h) = t.val 1 g (g * h)) : f = t := by
  apply Subtype.ext
  ext a b c
  have hh := congrArg (M.ρ a) (h (a⁻¹ * b) (b⁻¹ * c))
  rw [equivariant, equivariant] at hh
  simpa [mul_assoc] using hh
open CategoryTheory TopRep in
private theorem homology_eq_of_coordinates_coboundary {R : Type*} [CommRing R] [TopologicalSpace R]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : TopRep R G)
    (hc : Continuous (fun p : G × M ↦ M.ρ p.1 p.2))
    (z w : ContinuousCohomology.cocycles M 2) (c : C(G, M))
    (h : ∀ g h,
      (((homogeneousCochains M).iCycles 2).hom w).val 1 g (g * h) =
        (((homogeneousCochains M).iCycles 2).hom z).val 1 g (g * h) +
          (M.ρ g (c h) - c (g * h) + c g)) :
    (ContinuousCohomology.π M 2).hom z = (ContinuousCohomology.π M 2).hom w := by
  let C := homogeneousCochains M
  let q := oneCochain M hc c
  have hq : (C.d 1 2).hom q = (C.iCycles 2).hom (w - z) := by
    apply cochain_eq_of_coordinates
    intro g h'
    rw [homogeneousCochains.d_apply]
    change M.ρ g (c (g⁻¹ * (g * h'))) -
      (M.ρ 1 (c (1⁻¹ * (g * h'))) - M.ρ 1 (c (1⁻¹ * g))) = _
    simp only [inv_mul_cancel_left, inv_one, one_mul, map_one, one_apply_eq_self]
    rw [map_sub]
    change M.ρ g (c h') - (c (g * h') - c g) =
      (((C.iCycles 2).hom w).val 1 g (g * h')) -
        (((C.iCycles 2).hom z).val 1 g (g * h'))
    rw [h g h']
    abel
  have he : (C.toCycles 1 2).hom q = w - z := by
    let e : C.cycles 2 ≅ TopModuleCat.of R (C.d 2 3).hom.ker :=
      Limits.KernelFork.mapIsoOfIsLimit
        (C.cyclesIsKernel 2 3 (by simp))
        (TopModuleCat.isLimitKer _) (Iso.refl _)
    apply (((forget (TopModuleCat R)).mapIso e).toEquiv).injective
    apply Subtype.ext
    have hi := congrArg (fun f ↦ f.hom q) (C.toCycles_i 1 2)
    have hι : e.hom ≫ TopModuleCat.kerι (C.d 2 3) = C.iCycles 2 := by
      dsimp [e, Limits.KernelFork.mapIsoOfIsLimit]
      simpa using
        Limits.KernelFork.mapOfIsLimit_ι
          (Limits.KernelFork.ofι (C.iCycles 2) (C.iCycles_d 2 3))
          (TopModuleCat.isLimitKer (C.d 2 3)) (𝟙 (Arrow.mk (C.d 2 3)))
    have hx := congrArg (fun f ↦ f.hom ((C.toCycles 1 2).hom q)) hι
    have hy := congrArg (fun f ↦ f.hom (w - z)) hι
    exact hx.trans ((hi.trans hq).trans hy.symm)
  have hz := congrArg (fun f ↦ f.hom q) (C.toCycles_comp_homologyπ 1 2)
  change (C.homologyπ 2).hom ((C.toCycles 1 2).hom q) = 0 at hz
  rw [he, map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

private theorem action_continuous (K : Type u) [Field K] : Continuous (fun p :
    Gal(SeparableClosure K/K) × (galoisUnitsTopRep K) ↦
    (galoisUnitsTopRep K).ρ p.1 p.2) := by
  have : DiscreteTopology (galoisUnitsTopRep K) := ⟨rfl⟩
  rw [continuous_prod_of_discrete_right]
  intro x
  rw [continuous_discrete_rng]
  intro y
  change Additive ((SeparableClosure K)ˣ) at x y
  let : TopologicalSpace (SeparableClosure K) := ⊥
  have : DiscreteTopology (SeparableClosure K) := ⟨rfl⟩
  have : ContinuousSMul Gal(SeparableClosure K/K) (SeparableClosure K) :=
    continuousSMul_iff_stabilizer_isOpen.mpr stabilizer_isOpen_of_isIntegral
  have h : Continuous (fun g : Gal(SeparableClosure K/K) ↦
      g • ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)) :=
    continuous_id.smul continuous_const
  convert h.isOpen_preimage {((y.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)}
    (isOpen_discrete _) using 1
  ext g
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  change Additive.ofMul (g • x.toMul) = y ↔
    g ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) =
      ((y.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)
  exact ⟨fun h ↦ congrArg (fun z : Additive ((SeparableClosure K)ˣ) ↦
      (z.toMul : SeparableClosure K)) h,
    fun h ↦ congrArg Additive.ofMul (Units.ext h)⟩

open scoped TensorProduct in
private theorem matrixSize_eq (K : Type u) [Field K]
    (A : CSA.{u, u} K) (n m : ℕ)
    (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (e' : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin m) (Fin m) (SeparableClosure K)) : n = m := by
  have h := (e.symm.trans e').toLinearEquiv.finrank_eq
  have hh : n ^ 2 = m ^ 2 := by
    simpa [Module.finrank_matrix, pow_two] using h
  exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hh

private theorem scalar_injective (K : Type u) [Field K] (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin n) :
      (SeparableClosure K)ˣ → Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K)) := by
  intro a b h
  apply Units.ext
  have he := congrArg (fun X : Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K) ↦
    X.val ⟨0, Nat.pos_of_ne_zero hn⟩ ⟨0, Nat.pos_of_ne_zero hn⟩) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using he
private theorem gauge_defect (K : Type u) [Field K] (n : ℕ) (hn : n ≠ 0)
    (b b' : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (P : Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (c : Gal(SeparableClosure K/K) → (SeparableClosure K)ˣ)
    (hb : ∀ g, b' g = Matrix.GeneralLinearGroup.scalar (Fin n) (c g) *
      (P⁻¹ * b g * Matrix.GeneralLinearGroup.map g.toRingHom P))
    (s t : Gal(SeparableClosure K/K) → Gal(SeparableClosure K/K) →
      (SeparableClosure K)ˣ)
    (hs : ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
      Matrix.GeneralLinearGroup.scalar (Fin n) (s g h) * b (g * h))
    (ht : ∀ g h, b' g * Matrix.GeneralLinearGroup.map g.toRingHom (b' h) =
      Matrix.GeneralLinearGroup.scalar (Fin n) (t g h) * b' (g * h)) :
    ∀ g h, t g h = c g * Units.map g.toMonoidHom (c h) * (c (g * h))⁻¹ * s g h := by
  intro g h
  let S := Matrix.GeneralLinearGroup.scalar (Fin n) (R := SeparableClosure K)
  let T (g : Gal(SeparableClosure K/K)) :=
    Matrix.GeneralLinearGroup.map (n := Fin n) g.toRingHom
  let d (g : Gal(SeparableClosure K/K)) := P⁻¹ * b g * T g P
  have hT : T g (T h P) = T (g * h) P := rfl
  have hd : d g * T g (d h) = S (s g h) * d (g * h) := by
    dsimp [d]
    rw [map_mul, map_mul, map_inv, hT]
    calc
      _ = P⁻¹ * (b g * T g (b h)) * T (g * h) P := by group
      _ = P⁻¹ * (S (s g h) * b (g * h)) * T (g * h) P := by rw [hs]
      _ = S (s g h) * (P⁻¹ * b (g * h) * T (g * h) P) := by
        rw [← mul_assoc P⁻¹, ← Matrix.GeneralLinearGroup.scalar_commute]
        dsimp [S]
        group
  have hscalar : T g (S (c h)) = S (Units.map g.toMonoidHom (c h)) := by
    exact Matrix.GeneralLinearGroup.map_scalar g.toRingHom (c h)
  have hrel : S (t g h) * (S (c (g * h)) * d (g * h)) =
      S (c g * Units.map g.toMonoidHom (c h) * s g h) * d (g * h) := by
    rw [← hb (g * h), ← ht, hb g, hb h, map_mul, hscalar]
    change (S (c g) * d g) * (S (Units.map g.toMonoidHom (c h)) * T g (d h)) = _
    rw [← mul_assoc, mul_assoc (S (c g)),
      ← Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc]
    rw [mul_assoc (S (c g) * S _), hd]
    simp only [map_mul, mul_assoc]
  have hu : t g h * c (g * h) = c g * Units.map g.toMonoidHom (c h) * s g h := by
    apply scalar_injective K n hn
    exact mul_right_cancel (by simpa only [map_mul, mul_assoc] using hrel)
  calc
    _ = (c g * Units.map g.toMonoidHom (c h) * s g h) * (c (g * h))⁻¹ :=
      (eq_mul_inv_iff_mul_eq.mpr hu)
    _ = _ := by ac_rfl

/-- Evaluation is locally constant for every integral field extension with its
Krull topology: open stabilizers make the action on the discrete field continuous. -/
private theorem locallyConstant_integral_galois_eval (K L : Type*)
    [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L] (x : L) :
    IsLocallyConstant (fun g : L ≃ₐ[K] L ↦ g x) := by
  let : TopologicalSpace L := ⊥
  let : DiscreteTopology L := ⟨rfl⟩
  let : ContinuousSMul (L ≃ₐ[K] L) L :=
    continuousSMul_iff_stabilizer_isOpen.mpr (fun y ↦ stabilizer_isOpen_of_isIntegral y)
  exact (IsLocallyConstant.iff_continuous _).mpr (continuous_id.smul continuous_const)

open scoped TensorProduct in
private theorem scalar_of_same_conj (K : Type u) [Field K]
    (A : CSA.{u, u} K) (n : ℕ)
    (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (U V : Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (h : ∀ a : A, (U⁻¹).val * e (1 ⊗ₜ[K] a) * U.val =
      (V⁻¹).val * e (1 ⊗ₜ[K] a) * V.val) :
    ∃ c : (SeparableClosure K)ˣ,
      Matrix.GeneralLinearGroup.scalar (Fin n) c = V * U⁻¹ := by
  have hh (a : A) : (V * U⁻¹).val * e (1 ⊗ₜ[K] a) =
      e (1 ⊗ₜ[K] a) * (V * U⁻¹).val := by
    have ht := congrArg (fun X ↦ V.val * X * (U⁻¹).val) (h a)
    simpa [mul_assoc] using ht
  have hc (x : SeparableClosure K ⊗[K] A) :
      (V * U⁻¹).val * e x = e x * (V * U⁻¹).val := by
    induction x using TensorProduct.inductionOn with
    | tmul r a =>
      have he : e (r ⊗ₜ[K] a) = r • e (1 ⊗ₜ[K] a) := by
        rw [← map_smul]
        congr 1
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he, mul_smul_comm, smul_mul_assoc, hh]
    | add x y hx hy => rw [map_add, mul_add, add_mul, hx, hy]
  have hz : V * U⁻¹ ∈ Subgroup.center
      (Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K)) := by
    apply Subgroup.mem_center_iff.mpr
    intro W
    apply Units.ext
    simpa only [Units.val_mul, AlgEquiv.apply_symm_apply] using (hc (e.symm W.val)).symm
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  exact hz

open scoped TensorProduct in
/-- Two splittings of equal positive size have matrix descent lifts related by a
fixed conjugating matrix and a locally constant scalar function.

Proof: the automorphism e' composed with inverse e of the full matrix algebra is
inner by Skolem-Noether. Choose its conjugating matrix P with
 e'(a) = P inverse * e(a) * P. Set d(g) = P inverse * b(g) * g(P).
Substitution in the descent equation shows that d(g) and b'(g) implement the same
conjugation on e'(1 tensor a). These elements span the matrix algebra over the
separable closure: every pure tensor is a scalar times 1 tensor a, and pure tensors
span the tensor product. Thus b'(g) * inverse d(g) commutes with every matrix.
The centre of a full matrix algebra consists of scalars. Since the quotient is a unit
and n is positive, it is a unique scalar unit c(g), with b'(g) = c(g) * d(g).
Every entry of P has an open Galois stabilizer, since it is integral over K. Hence
entrywise g(P) is locally constant, as is d and the quotient b' * inverse d.
Its scalar is its (0,0) entry; therefore c is locally constant. More precisely, equality
of quotients implies equality of scalars by evaluating that entry and using Units.ext,
so local constancy descends along the injective scalar embedding. Positivity supplies
the entry. The argument applies also to n = 1 and does not normalize lifts at 1.

Source: Stacks Project, Etale Cohomology, construction following Lemma 03R6 and
preceding Theorem 03R7, equation `equation-two-cocycle`; Skolem-Noether, Tag 074P.
The change-of-lift calculation is expanded above in the orientation of
`HasBrauerScalarDefect`.
(blueprint: lem-sc-brauer-scalar-defect-unique). -/
private theorem exists_locallyConstant_brauer_lift_comparison (K : Type u) [Field K]
    (A : CSA.{u, u} K) (n : ℕ) (hn : n ≠ 0)
    (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (e' : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (b : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (b' : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b) (hb' : IsLocallyConstant b')
    (hdesc : ∀ (g : Gal(SeparableClosure K/K)) (a : A),
      (e (1 ⊗ₜ[K] a)).map g = ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val)
    (hdesc' : ∀ (g : Gal(SeparableClosure K/K)) (a : A),
      (e' (1 ⊗ₜ[K] a)).map g = ((b' g)⁻¹).val * e' (1 ⊗ₜ[K] a) * (b' g).val) :
    ∃ (P : Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
      (c : Gal(SeparableClosure K/K) → (SeparableClosure K)ˣ),
      IsLocallyConstant c ∧ ∀ g,
        b' g = Matrix.GeneralLinearGroup.scalar (Fin n) (c g) *
          (P⁻¹ * b g * Matrix.GeneralLinearGroup.map g.toRingHom P) := by
  classical
  obtain ⟨Q, hQ⟩ := Matrix.exists_unit_conj_of_algEquiv (e.symm.trans e')
  have he (a : A) : e' (1 ⊗ₜ[K] a) = Q.val * e (1 ⊗ₜ[K] a) * (Q⁻¹).val := by
    simpa using hQ (e (1 ⊗ₜ[K] a))
  let d (g : Gal(SeparableClosure K/K)) :=
    Q * b g * Matrix.GeneralLinearGroup.map g.toRingHom Q⁻¹
  have hd (g : Gal(SeparableClosure K/K)) (a : A) :
      (e' (1 ⊗ₜ[K] a)).map g =
        ((d g)⁻¹).val * e' (1 ⊗ₜ[K] a) * (d g).val := by
    have hi := congrArg Units.val
      ((Matrix.GeneralLinearGroup.map (n := Fin n) g.toRingHom).map_inv Q)
    have hinv : (Q.val)⁻¹.map g = ((Q.val).map g)⁻¹ := by
      change (Q⁻¹).val.map g =
        ((Matrix.GeneralLinearGroup.map g.toRingHom Q)⁻¹).val at hi
      simp only [Matrix.GeneralLinearGroup.coe_inv] at hi
      exact hi
    rw [he, Matrix.map_mul, Matrix.map_mul, hdesc]
    simp [d, mul_inv_rev, mul_assoc, hinv]
  have hex (g : Gal(SeparableClosure K/K)) : ∃ c : (SeparableClosure K)ˣ,
      Matrix.GeneralLinearGroup.scalar (Fin n) c = b' g * (d g)⁻¹ := by
    apply scalar_of_same_conj K A n e' (d g) (b' g)
    intro a
    exact (hd g a).symm.trans (hdesc' g a)
  let c (g : Gal(SeparableClosure K/K)) := Classical.choose (hex g)
  have hc (g : Gal(SeparableClosure K/K)) :
      Matrix.GeneralLinearGroup.scalar (Fin n) (c g) = b' g * (d g)⁻¹ :=
    Classical.choose_spec (hex g)
  refine ⟨Q⁻¹, c, ?_, ?_⟩
  · have hmap : IsLocallyConstant
        (fun g : Gal(SeparableClosure K/K) ↦
          Matrix.GeneralLinearGroup.map g.toRingHom Q⁻¹) := by
      have hval : IsLocallyConstant (fun g : Gal(SeparableClosure K/K) ↦
          (Matrix.GeneralLinearGroup.map g.toRingHom Q⁻¹).val) := by
        exact (LocallyConstant.unflip (fun i ↦ LocallyConstant.unflip (fun j ↦
          ⟨fun g : Gal(SeparableClosure K/K) ↦ g ((Q⁻¹).val i j),
            locallyConstant_integral_galois_eval K (SeparableClosure K) _⟩))).isLocallyConstant
      exact IsLocallyConstant.desc _ Units.val hval Units.val_injective
    have hdLC : IsLocallyConstant d := (IsLocallyConstant.const Q).mul hb |>.mul hmap
    have hscalar : IsLocallyConstant
        (fun g ↦ Matrix.GeneralLinearGroup.scalar (Fin n) (c g)) := by
      have hf := hb'.mul hdLC.inv
      convert hf using 1
      funext g
      exact hc g
    apply IsLocallyConstant.desc c (Matrix.GeneralLinearGroup.scalar (Fin n)) hscalar
    intro a b hab
    apply Units.ext
    have hv := congrArg (fun X : Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K) ↦
      X.val ⟨0, Nat.pos_of_ne_zero hn⟩ ⟨0, Nat.pos_of_ne_zero hn⟩) hab
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using hv
  · intro g
    rw [hc]
    dsimp [d]
    simp only [inv_inv, mul_assoc, inv_mul_cancel, mul_one]

/-- Two matrix descent realizations for the same algebra have the same class.

Proof: unpack both realizations into splittings `e`, `e'`, locally constant lifts
`b`, `b'`, and homogeneous cocycles `z`, `z'`. Equality of the dimensions of the
split algebras gives equality of their positive matrix sizes. After reindexing,
Skolem-Noether identifies the change of splitting with conjugation by a fixed
invertible matrix `P`, so that `e'(a) = P⁻¹ * e(a) * P`.
The lifts `d(g) = P⁻¹ * b(g) * g(P)` implement the descent datum for `e'`.
Both `d(g)` and `b'(g)` implement the same automorphism of the full matrix algebra:
the descent identity holds on `e'(1 ⊗ a)`, which spans it over the separable closure.
Their quotient is therefore central, hence uniquely a scalar unit `c(g)`.
The map `g ↦ g(P)` is locally constant: the finitely many entries of `P` lie in a
finite separable extension and its fixing subgroup is open. Thus `d` is locally
constant. Extract `c(g)` from any diagonal entry of `b'(g) * d(g)⁻¹`; positivity
of the size supplies such an entry, and this extraction shows `c` is locally constant.
Substitute `b'(g) = c(g) * d(g)` in the multiplication-defect identities. Cancellation
of `P` and `g(P)` gives `z'(g,h) = c(g) * g(c(h)) * c(gh)⁻¹ * z(g,h)` in
inhomogeneous coordinates. Thus the two cocycles differ by the continuous
one-coboundary of `c`. Convert back to homogeneous cochains by
`q(g₀,g₁) = g₀(c(g₀⁻¹*g₁))`. Its alternating differential is their difference,
and equality of the inhomogeneous values determines an equivariant homogeneous
cochain by evaluating at `(1,g,g*h)`. The homology projection kills that differential.
Use the two equations identifying the homology images with `x` and `y` to conclude.

Source: Stacks Project, scalar-defect independence in the construction following
Lemma 03R6 and preceding Theorem 03R7; the differential of Section 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-unique). -/
theorem brauerScalarDefect_unique (K : Type u) [Field K]
    (A : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K A y) :
    x = y := by
  obtain ⟨n, hn, e, b, hb, z, hz, hdesc, hs⟩ := hx
  obtain ⟨m, hm, e', b', hb', w, hw, hdesc', ht⟩ := hy
  have hnm := matrixSize_eq K A n m e e'
  subst m
  obtain ⟨P, c, hc, hbc⟩ := exists_locallyConstant_brauer_lift_comparison K A
    n hn e e' b b' hb hb' hdesc hdesc'
  have hct := gauge_defect K n hn b b' P c hbc
    (galoisUnitsCocycleValue K z) (galoisUnitsCocycleValue K w) hs ht
  let a : Gal(SeparableClosure K/K) → galoisUnitsTopRep K :=
    fun g ↦ Additive.ofMul (c g)
  have : DiscreteTopology (galoisUnitsTopRep K) := ⟨rfl⟩
  have ha : Continuous a :=
    (IsLocallyConstant.iff_continuous a).mp (hc.comp Additive.ofMul)
  have heq := homology_eq_of_coordinates_coboundary (galoisUnitsTopRep K)
    (action_continuous K) z w ⟨a, ha⟩ (by
      intro g h
      have he := congrArg Additive.ofMul (hct g h)
      change Additive.ofMul (galoisUnitsCocycleValue K w g h) =
        Additive.ofMul (c g) + Additive.ofMul (Units.map g.toMonoidHom (c h)) -
          Additive.ofMul (c (g * h)) + Additive.ofMul (galoisUnitsCocycleValue K z g h) at he
      change Additive.ofMul (galoisUnitsCocycleValue K w g h) =
        Additive.ofMul (galoisUnitsCocycleValue K z g h) +
          (Additive.ofMul (Units.map g.toMonoidHom (c h)) -
            Additive.ofMul (c (g * h)) + Additive.ofMul (c g))
      rw [he]
      abel)
  exact hz.symm.trans (heq.trans hw)

end Field

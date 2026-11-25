/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.Mathlib.Algebra.CharP.Algebra
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.LinearAlgebra.Lagrange
public import WeilConjectures.RingTheory.MvPolynomial.ArtinSchreier

/-!
# The Artin–Schreier map of relative affine space

The Artin–Schreier map `AS_q : 𝔸(n; S) ⟶ 𝔸(n; S)`, `x ↦ x ^ q - x`, applied coordinatewise.
Over a scheme `S` receiving a ring map from a finite field `k` with `q` elements, it is a finite
étale torsor under `kⁿ` acting by translations.

## Main definitions

- `AlgebraicGeometry.AffineSpace.artinSchreierMap`: the Artin–Schreier map `x ↦ x ^ q - x`.
- `AlgebraicGeometry.AffineSpace.artinSchreierTorsorMap`: the map
  `∐_{a ∈ kⁿ} 𝔸(n; S) ⟶ 𝔸(n; S) ×_{AS_q} 𝔸(n; S)`, `(a, x) ↦ (x, x + a)`.

## Main statements

- `AlgebraicGeometry.AffineSpace.isFinite_artinSchreierMap`: `AS_q` is finite for `q ≠ 1`.
- `AlgebraicGeometry.AffineSpace.etale_artinSchreierMap`: `AS_q` is étale when `q = 0` on `S`.
- `AlgebraicGeometry.AffineSpace.surjective_artinSchreierMap`: `AS_q` is surjective on the affine
  line over a finite field with `q` elements.
- `AlgebraicGeometry.AffineSpace.translation_comp_artinSchreierMap_of_finiteField`: `AS_q` is
  invariant under translation by the elements of a finite field with `q` elements.
- `AlgebraicGeometry.AffineSpace.isIso_artinSchreierTorsorMap`: `AS_q` is a torsor under them.

-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.AffineSpace

variable (n : Type u) (S : Scheme.{u})

/-- The Artin–Schreier map `x ↦ x ^ q - x` of `𝔸(n; S)`, applied coordinatewise. -/
def artinSchreierMap (q : ℕ) : 𝔸(n; S) ⟶ 𝔸(n; S) :=
  homOfVector (𝔸(n; S) ↘ S) fun i ↦ coord S i ^ q - coord S i

@[reassoc (attr := simp)]
lemma artinSchreierMap_over (q : ℕ) : artinSchreierMap n S q ≫ 𝔸(n; S) ↘ S = 𝔸(n; S) ↘ S :=
  homOfVector_over _ _

@[simp]
lemma artinSchreierMap_appTop_coord (q : ℕ) (i : n) :
    (artinSchreierMap n S q).appTop (coord S i) = coord S i ^ q - coord S i :=
  homOfVector_appTop_coord _ _ _

variable {n S}

/-- The Artin–Schreier map commutes with the base change map `map f` of `f : S ⟶ T`: the
square of `AlgebraicGeometry.AffineSpace.isPullback_map_artinSchreierMap` commutes. -/
@[reassoc]
lemma map_comp_artinSchreierMap {T : Scheme.{u}} (f : S ⟶ T) (q : ℕ) :
    map n f ≫ artinSchreierMap n T q = artinSchreierMap n S q ≫ map n f :=
  hom_ext (by simp) fun i ↦ by simp

/-- The Artin–Schreier map of `𝔸(n; S)` is the base change of that of `𝔸(n; T)` along
`f : S ⟶ T`, that is, the following square is cartesian:

```
𝔸(n; S) --map f--> 𝔸(n; T)
   |                  |
   | AS_q             | AS_q
   v                  v
𝔸(n; S) --map f--> 𝔸(n; T)
```
-/
lemma isPullback_map_artinSchreierMap {T : Scheme.{u}} (f : S ⟶ T) (q : ℕ) :
    IsPullback (map n f) (artinSchreierMap n S q) (artinSchreierMap n T q) (map n f) :=
  IsPullback.of_bot (by simpa using isPullback_map (n := n) f)
    (map_comp_artinSchreierMap f q) (isPullback_map (n := n) f)

variable (n) in
/-- Over an affine base `Spec R`, the Artin–Schreier map is `Spec` of the ring map
`R[n] → R[n]`, `Xᵢ ↦ Xᵢ ^ q - Xᵢ`. -/
lemma artinSchreierMap_Spec (R : CommRingCat.{u}) (q : ℕ) :
    artinSchreierMap n (Spec R) q = (SpecIso n R).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.artinSchreierRingHom R n q)) ≫
        (SpecIso n R).inv := by
  refine hom_ext ?_ fun i ↦ ?_
  · rw [artinSchreierMap_over, Category.assoc, Category.assoc, SpecIso_inv_over, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, MvPolynomial.artinSchreierRingHom_comp_C, ← SpecIso_inv_over,
      Iso.hom_inv_id_assoc]
  · rw [artinSchreierMap_appTop_coord, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, CommRingCat.comp_apply, SpecIso_inv_appTop_coord,
      Scheme.specMap_appTop_ΓSpecIso_inv, CommRingCat.ofHom_apply,
      MvPolynomial.artinSchreierRingHom_X, map_sub, map_pow, ← SpecIso_inv_appTop_coord, map_sub,
      map_pow, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id,
      Scheme.Hom.id_appTop, CommRingCat.id_apply]

variable (n S)

/-- For `q ≠ 1` and finitely many coordinates, the Artin–Schreier map `x ↦ x ^ q - x` is
finite. (For `q = 0` it is the isomorphism `x ↦ 1 - x`; for `q = 1` it is the zero map.)
This is the finiteness of the Artin–Schreier covering of the blueprint definition
`lemma-artin-schreier-character-sheaf--1` (sketch blueprint:
`lemma-artin-schreier-character-sheaf--1`). -/
lemma isFinite_artinSchreierMap [Finite n] {q : ℕ} (hq : q ≠ 1) :
    IsFinite (artinSchreierMap n S q) := by
  -- over `Spec Γ(S, ⊤)` each coordinate ring map `T ↦ T ^ q - T` is integral and of finite
  -- type; `AS_q` over `S` is its base change
  have (R : CommRingCat.{u}) : IsFinite (artinSchreierMap n (Spec R) q) := by
    have := (IsFinite.SpecMap_iff (CommRingCat.ofHom (MvPolynomial.artinSchreierRingHom R n q))).mpr
      (MvPolynomial.finite_artinSchreierRingHom n hq)
    rw [artinSchreierMap_Spec]
    infer_instance
  exact MorphismProperty.of_isPullback (isPullback_map_artinSchreierMap S.toSpecΓ q) (this _)

/-- If `q = 0` on `S`, the Artin–Schreier map `x ↦ x ^ q - x` of `𝔸(n; S)` is étale. This is
the étaleness of the Artin–Schreier covering of the blueprint definition
`lemma-artin-schreier-character-sheaf--1` (sketch blueprint:
`lemma-artin-schreier-character-sheaf--1`). -/
lemma etale_artinSchreierMap [Finite n] {q : ℕ} (hq : (q : Γ(S, ⊤)) = 0) :
    Etale (artinSchreierMap n S q) := by
  -- the Jacobian of `x ↦ x ^ q - x` is `q x ^ (q - 1) - 1 = -1`, a unit; over
  -- `Spec Γ(S, ⊤)` this is `MvPolynomial.etale_artinSchreierRingHom`, and `AS_q` over `S` is its
  -- base change
  have : Etale (artinSchreierMap n (Spec Γ(S, ⊤)) q) := by
    have : Etale (Spec.map (CommRingCat.ofHom (MvPolynomial.artinSchreierRingHom Γ(S, ⊤) n q))) :=
      HasRingHomProperty.Spec_iff.mpr (MvPolynomial.etale_artinSchreierRingHom n q hq)
    rw [artinSchreierMap_Spec]
    infer_instance
  exact MorphismProperty.of_isPullback (isPullback_map_artinSchreierMap S.toSpecΓ q) this

variable {n S}

/-- In characteristic `p`, the Artin–Schreier map `x ↦ x ^ (p ^ m) - x` is invariant under
translation by a vector `a` with `a ^ (p ^ m) = a`:

```
𝔸(n; S) --translation a--> 𝔸(n; S)
      \                       |
       \ AS_{p^m}             | AS_{p^m}
        \                     v
         -----------------> 𝔸(n; S)
```
-/
@[reassoc]
lemma translation_comp_artinSchreierMap {p : ℕ} (hp : p.Prime) (hpS : (p : Γ(S, ⊤)) = 0)
    (m : ℕ) (a : n → Γ(S, ⊤)) (ha : ∀ i, a i ^ p ^ m = a i) :
    translation a ≫ artinSchreierMap n S (p ^ m) = artinSchreierMap n S (p ^ m) := by
  refine hom_ext (by simp) fun i ↦ ?_
  nontriviality Γ(𝔸(n; S), ⊤)
  have := CharP.of_ringHom_of_prime (𝔸(n; S) ↘ S).appTop.hom hp hpS
  have := Fact.mk hp
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, artinSchreierMap_appTop_coord, map_sub,
    map_pow, translation_appTop_coord, add_pow_char_pow, ← map_pow, ha]
  ring

/-- Over a scheme `S` with a ring map `φ : k →+* Γ(S, 𝒪_S)` from a finite field `k` with `q`
elements, translation by a vector `a` with entries in `k` leaves the Artin–Schreier map
`x ↦ x ^ q - x` of `𝔸(n; S)` invariant:

```
𝔸(n; S) --translation (φ ∘ a)--> 𝔸(n; S)
      \                             |
       \ AS_q                       | AS_q
        \                           v
         -----------------------> 𝔸(n; S)
```
-/
@[reassoc]
lemma translation_comp_artinSchreierMap_of_finiteField (k : Type*) [Field k] [Fintype k]
    (φ : k →+* Γ(S, ⊤)) (a : n → k) :
    translation (fun i ↦ φ (a i)) ≫ artinSchreierMap n S (Fintype.card k) =
      artinSchreierMap n S (Fintype.card k) := by
  obtain ⟨m, hp, hm⟩ := FiniteField.card k (ringChar k)
  rw [hm]
  refine translation_comp_artinSchreierMap hp ?_ _ _ fun _ ↦ ?_
  · rw [← map_natCast φ, ringChar.Nat.cast_ringChar, map_zero]
  · rw [← map_pow, ← hm, FiniteField.pow_card]

/-- Over a scheme `S` with a ring map `φ : k →+* Γ(S, 𝒪_S)` from a finite field `k` with `q`
elements, the map `∐_{a ∈ kⁿ} 𝔸(n; S) ⟶ 𝔸(n; S) ×_{AS_q} 𝔸(n; S)`, `(a, x) ↦ (x, x + a)`:

```
∐_{a ∈ kⁿ} 𝔸(n; S) ---> 𝔸(n; S) ×_{AS_q} 𝔸(n; S) --snd--> 𝔸(n; S)
                                   |                          |
                               fst |                          | AS_q
                                   v                          v
                                𝔸(n; S) -------- AS_q ------> 𝔸(n; S)
```

On the summand indexed by `a`, its composites with `fst` and `snd` are `𝟙` and
`translation a` (`AlgebraicGeometry.AffineSpace.ι_artinSchreierTorsorMap_fst`,
`AlgebraicGeometry.AffineSpace.ι_artinSchreierTorsorMap_snd`). -/
def artinSchreierTorsorMap (k : Type u) [Field k] [Fintype k] (φ : k →+* Γ(S, ⊤)) :
    ∐ (fun _ : n → k ↦ 𝔸(n; S)) ⟶
      pullback (artinSchreierMap n S (Fintype.card k)) (artinSchreierMap n S (Fintype.card k)) :=
  Sigma.desc fun a ↦ pullback.lift (𝟙 𝔸(n; S)) (translation fun i ↦ φ (a i))
    (by rw [Category.id_comp, translation_comp_artinSchreierMap_of_finiteField])

@[reassoc (attr := simp)]
lemma ι_artinSchreierTorsorMap_fst (k : Type u) [Field k] [Fintype k]
    (φ : k →+* Γ(S, ⊤)) (a : n → k) :
    Sigma.ι _ a ≫ artinSchreierTorsorMap k φ ≫ pullback.fst _ _ = 𝟙 𝔸(n; S) := by
  simp [artinSchreierTorsorMap]

@[reassoc (attr := simp)]
lemma ι_artinSchreierTorsorMap_snd (k : Type u) [Field k] [Fintype k]
    (φ : k →+* Γ(S, ⊤)) (a : n → k) :
    Sigma.ι _ a ≫ artinSchreierTorsorMap k φ ≫ pullback.snd _ _ =
      translation fun i ↦ φ (a i) := by
  simp [artinSchreierTorsorMap]

/-- The two projections of `𝔸(n; S) ×_{AS_q} 𝔸(n; S)` agree over `S`. -/
@[reassoc]
lemma pullback_fst_artinSchreierMap_over (q : ℕ) :
    pullback.fst (artinSchreierMap n S q) (artinSchreierMap n S q) ≫ 𝔸(n; S) ↘ S =
      pullback.snd (artinSchreierMap n S q) (artinSchreierMap n S q) ≫ 𝔸(n; S) ↘ S := by
  rw [← artinSchreierMap_over n S q, pullback.condition_assoc]

/-- Over a scheme `S` with a ring map `φ : k →+* Γ(S, 𝒪_S)` from a finite field `k` with `q`
elements, the Artin–Schreier map `AS_q` of `𝔸(n; S)` is a torsor under `kⁿ` acting by
translations: `AlgebraicGeometry.AffineSpace.artinSchreierTorsorMap` is an isomorphism.
This is the torsor structure of the Artin–Schreier covering of the blueprint definition
`lemma-artin-schreier-character-sheaf--1` (sketch blueprint:
`lemma-artin-schreier-character-sheaf--1`).

The idempotents `E_a`, `a ∈ kⁿ`, obtained by evaluating Lagrange interpolation polynomials at
the differences `d = y - x` (which satisfy `d ^ q = d`) split the fibre product into the open
subschemes `D(E_a)`, and the summand indexed by `a` maps isomorphically onto `D(E_a)`. -/
lemma isIso_artinSchreierTorsorMap [Finite n] (k : Type u) [Field k] [Fintype k]
    (φ : k →+* Γ(S, ⊤)) :
    IsIso (artinSchreierTorsorMap k φ : ∐ (fun _ : n → k ↦ 𝔸(n; S)) ⟶ _) := by
  classical
  have := Fintype.ofFinite n
  set AS := artinSchreierMap n S (Fintype.card k)
  let ψ : k →+* Γ(pullback AS AS, ⊤) := (pullback.fst AS AS ≫ 𝔸(n; S) ↘ S).appTop.hom.comp φ
  let d (i : n) : Γ(pullback AS AS, ⊤) :=
    (pullback.snd AS AS).appTop (coord S i) - (pullback.fst AS AS).appTop (coord S i)
  have hd (i : n) : d i ^ Fintype.card k = d i := by
    have hc := congrArg (fun f ↦ f.appTop (coord S i))
      (pullback.condition (f := AS) (g := AS))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AS, artinSchreierMap_appTop_coord,
      map_sub, map_pow] at hc
    exact FiniteField.sub_pow_card_eq_of_pow_card_sub_eq ψ hc
  let E := FiniteField.lagrangeIdem ψ d
  have key (a : n → k) :
      IsOpenImmersion (Sigma.ι (fun _ : n → k ↦ 𝔸(n; S)) a ≫ artinSchreierTorsorMap k φ) ∧
      Set.range (Sigma.ι (fun _ : n → k ↦ 𝔸(n; S)) a ≫ artinSchreierTorsorMap k φ) =
        (pullback AS AS).basicOpen (E a) := by
    refine isOpenImmersion_and_range_eq_of_section (pullback.fst AS AS) _ (by simp [AS]) _
      ?_ ?_
    · have hcomp {Z : Scheme.{u}} (g : pullback AS AS ⟶ Z) (x : Γ(Z, ⊤)) :
          (Sigma.ι (fun _ : n → k ↦ 𝔸(n; S)) a ≫ artinSchreierTorsorMap k φ).appTop
            (g.appTop x) =
          (Sigma.ι (fun _ : n → k ↦ 𝔸(n; S)) a ≫ artinSchreierTorsorMap k φ ≫ g).appTop x := by
        rw [← Category.assoc, Scheme.Hom.comp_appTop]
        rfl
      have hψ : (Sigma.ι (fun _ : n → k ↦ 𝔸(n; S)) a ≫
          artinSchreierTorsorMap k φ).appTop.hom.comp ψ = (𝔸(n; S) ↘ S).appTop.hom.comp φ := by
        ext c
        change (Sigma.ι (fun _ : n → k ↦ 𝔸(n; S)) a ≫ artinSchreierTorsorMap k φ).appTop
          ((pullback.fst AS AS ≫ 𝔸(n; S) ↘ S).appTop (φ c)) = _
        rw [hcomp, ι_artinSchreierTorsorMap_fst_assoc]
        rfl
      have hd' (i : n) :
          (Sigma.ι (fun _ : n → k ↦ 𝔸(n; S)) a ≫ artinSchreierTorsorMap k φ).appTop (d i) =
            (𝔸(n; S) ↘ S).appTop.hom.comp φ (a i) := by
        simp only [d, map_sub]
        rw [hcomp, hcomp, ι_artinSchreierTorsorMap_snd, ι_artinSchreierTorsorMap_fst,
          translation_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply, add_sub_cancel_left]
        rfl
      rw [Scheme.preimage_basicOpen_top, FiniteField.map_lagrangeIdem]
      refine (congrArg (𝔸(n; S)).basicOpen ?_).trans (Scheme.basicOpen_one _)
      convert FiniteField.lagrangeIdem_self ((𝔸(n; S) ↘ S).appTop.hom.comp φ) a using 2
      exact funext hd'
    · refine pullback.hom_ext (by simp [AS]) ?_
      simp only [Category.assoc]
      rw [ι_artinSchreierTorsorMap_snd]
      refine hom_ext (by simp [AS, pullback_fst_artinSchreierMap_over]) fun i ↦ ?_
      have h0 : ((pullback AS AS).basicOpen (E a)).ι.appTop (d i - ψ (a i)) = 0 := by
        have := congrArg (fun x ↦ ((pullback AS AS).basicOpen (E a)).ι.appTop x)
          (FiniteField.lagrangeIdem_mul_sub ψ hd a i)
        rw [map_mul, map_zero] at this
        exact (Scheme.isUnit_ι_appTop_basicOpen _ (E a)).mul_right_eq_zero.mp this
      simp only [d, ψ, map_sub, RingHom.comp_apply, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply] at h0
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, translation_appTop_coord,
        map_add]
      linear_combination -h0
  have := fun a ↦ (key a).1
  have hR (a : n → k) :
      (Sigma.ι (fun _ : n → k ↦ 𝔸(n; S)) a ≫ artinSchreierTorsorMap k φ).opensRange =
        (pullback AS AS).basicOpen (E a) :=
    TopologicalSpace.Opens.ext (by rw [Scheme.Hom.coe_opensRange, (key a).2])
  have h := nonempty_isColimit_cofanMk_of
    (fun a ↦ Sigma.ι (fun _ : n → k ↦ 𝔸(n; S)) a ≫ artinSchreierTorsorMap k φ) ?_ ?_
  · rw [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc, cofan_mk_inj] at h
    have hT : Sigma.desc (fun a ↦ Sigma.ι (fun _ : n → k ↦ 𝔸(n; S)) a ≫
        artinSchreierTorsorMap k φ) = artinSchreierTorsorMap k φ :=
      Sigma.hom_ext _ _ fun a ↦ by simp
    exact hT ▸ h
  · simp_rw [hR]
    exact Scheme.iSup_basicOpen_eq_top_of_sum_eq_one E (FiniteField.sum_lagrangeIdem ψ d)
  · intro a b hab
    simp only [Function.onFun, hR]
    rw [disjoint_iff, ← Scheme.basicOpen_mul, FiniteField.lagrangeIdem_mul_lagrangeIdem ψ hd hab,
      Scheme.basicOpen_zero]

/-- Over a finite field `k` with `q` elements, every geometric point of `𝔸¹_k` lifts along the
Artin–Schreier map `AS_q`: the equation `T ^ q - T = c` has a root in an algebraically closed
field. -/
lemma exists_comp_artinSchreierMap_eq (k : Type u) [Field k] [Fintype k] {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ 𝔸(PUnit; Spec (.of k))) :
    ∃ t : Spec (.of Ω) ⟶ 𝔸(PUnit; Spec (.of k)),
      t ≫ artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k) = y := by
  set c := (Scheme.ΓSpecIso (.of Ω)).hom.hom (y.appTop (coord (Spec (.of k)) PUnit.unit))
  have hlt : (Polynomial.X : Polynomial Ω).degree <
      ((Polynomial.X : Polynomial Ω) ^ Fintype.card k).degree := by
    rw [Polynomial.degree_X, Polynomial.degree_X_pow]
    exact_mod_cast Fintype.one_lt_card
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_root (Polynomial.X ^ Fintype.card k - Polynomial.X -
    Polynomial.C c) (by
      rw [Polynomial.degree_sub_C (by
        rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
        exact_mod_cast Fintype.card_pos)]
      rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
      exact_mod_cast Fintype.card_ne_zero)
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at hd
  refine ⟨homOfVector (y ≫ 𝔸(PUnit; Spec (.of k)) ↘ Spec (.of k))
    fun _ ↦ (Scheme.ΓSpecIso (.of Ω)).inv.hom d, hom_ext ?_ fun _ ↦ ?_⟩
  · rw [Category.assoc, artinSchreierMap_over, homOfVector_over]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, artinSchreierMap_appTop_coord, map_sub,
      map_pow, homOfVector_appTop_coord, ← map_pow, ← map_sub, sub_eq_zero.mp hd]
    exact (Scheme.ΓSpecIso (.of Ω)).hom_inv_id_apply _

/-- Over a finite field `k` with `q` elements, the Artin–Schreier map `AS_q` of `𝔸¹_k` is
surjective: every point has a geometric point over it, which lifts along `AS_q`
(`AlgebraicGeometry.AffineSpace.exists_comp_artinSchreierMap_eq`). -/
lemma surjective_artinSchreierMap (k : Type u) [Field k] [Fintype k] :
    Function.Surjective (artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)).base := by
  intro x
  obtain ⟨t, ht⟩ := exists_comp_artinSchreierMap_eq k
    (Spec.map (CommRingCat.ofHom (algebraMap (𝔸(PUnit; Spec (.of k)).residueField x)
      (AlgebraicClosure (𝔸(PUnit; Spec (.of k)).residueField x)))) ≫
      𝔸(PUnit; Spec (.of k)).fromSpecResidueField x)
  obtain ⟨p⟩ : Nonempty (Spec (.of (AlgebraicClosure (𝔸(PUnit; Spec (.of k)).residueField x)))) :=
    inferInstance
  refine ⟨t.base p, ?_⟩
  rw [← Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

end AlgebraicGeometry.AffineSpace

end

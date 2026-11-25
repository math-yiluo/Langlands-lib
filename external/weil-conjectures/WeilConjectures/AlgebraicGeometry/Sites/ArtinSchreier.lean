/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Ga
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.ZMod.QuotientRing

/-!
# The Artin–Schreier sequence and the `p`-cohomological dimension of affine schemes

Let `X` be a scheme on which the prime `p` vanishes. The Artin–Schreier sequence

```
  0 ──▶ ℤ/p ──▶ 𝔾ₐ ──℘──▶ 𝔾ₐ ──▶ 0,     ℘(x) = xᵖ - x,
```

is exact on the small étale site of `X`: the kernel of `℘` on an étale `X`-scheme `U` consists of
the sections which are locally constant with values in `𝔽_p ⊆ Γ(U, 𝒪)`, and every section `f` of
`𝔾ₐ` acquires a preimage `y` with `yᵖ - y = f` on the finite étale surjective cover
`Spec 𝒪(U)[y]/(yᵖ - y - f)`. Since `Hᵠ(X_ét, 𝔾ₐ) = 0` for `q ≥ 1` on an affine scheme
(`AlgebraicGeometry.Scheme.subsingleton_sheafH_gaSheaf_of_isAffine`), its long exact sequence
gives `Hᵠ(X_ét, ℤ/p) = 0` for `q ≥ 2`.

## Main definitions

- `AlgebraicGeometry.Scheme.gaArtinSchreier`: the Artin–Schreier map `℘ : 𝔾ₐ ⟶ 𝔾ₐ`.
- `AlgebraicGeometry.Scheme.artinSchreierSequence`: the short complex `ker ℘ ⟶ 𝔾ₐ ⟶ 𝔾ₐ`.
- `AlgebraicGeometry.Scheme.constantZModIsoKernelGaArtinSchreier`: `ℤ/p ≅ ker ℘`.

## Main statements

- `AlgebraicGeometry.Scheme.artinSchreierSequence_shortExact`: the Artin–Schreier sequence is
  short exact.
- `AlgebraicGeometry.Scheme.subsingleton_sheafH_constantZMod_of_isAffine`: `Hᵠ(X_ét, ℤ/p) = 0`
  for `q ≥ 2` on an affine scheme `X` with `p = 0` in `Γ(X, 𝒪_X)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Polynomial

/-! ### Algebraic preliminaries -/

section Algebra

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-- The ring map `ℤ/p → R` for a ring `R` in which `p = 0`. -/
noncomputable def zmodRingHomOfNatCastEqZero (h : (p : R) = 0) : ZMod p →+* R :=
  (Ideal.Quotient.lift (Ideal.span {(p : ℤ)}) (Int.castRingHom R) fun a ha ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp [h]).comp (Int.quotientSpanNatEquivZMod p).symm.toRingHom

/-- In a ring in which the prime `p` vanishes, `(x + y)ᵖ = xᵖ + yᵖ`. -/
lemma add_pow_prime_of_natCast_eq_zero (h : (p : R) = 0) (x y : R) :
    (x + y) ^ p = x ^ p + y ^ p := by
  nontriviality R
  have : CharP R p := (CharP.charP_iff_prime_eq_zero hp.out).2 h
  exact add_pow_char x y p

/-- The Artin–Schreier map `x ↦ xᵖ - x`, additive in a ring in which `p = 0`. -/
noncomputable def artinSchreierAddHom (h : (p : R) = 0) : R →+ R where
  toFun x := x ^ p - x
  map_zero' := by simp [hp.out.ne_zero]
  map_add' x y := by
    rw [add_pow_prime_of_natCast_eq_zero p h]
    ring

lemma artinSchreierAddHom_apply (h : (p : R) = 0) (x : R) :
    artinSchreierAddHom p h x = x ^ p - x :=
  rfl


/-- `∏_{s ∈ 𝔽_p} (x - s) = xᵖ - x`. -/
lemma prod_sub_zmodRingHom (h : (p : R) = 0) (x : R) :
    ∏ s : ZMod p, (x - zmodRingHomOfNatCastEqZero p h s) = x ^ p - x := by
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod p)
    rwa [ZMod.card] at this
  have hmonic : (X ^ p - X : (ZMod p)[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hp.out.one_lt)
  have hcard : Multiset.card (X ^ p - X : (ZMod p)[X]).roots =
      (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.out.one_lt]
    simp
  have e := congrArg (eval₂ (zmodRingHomOfNatCastEqZero p h) x)
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard)
  rw [hroots] at e
  simp only [eval₂_multiset_prod, Multiset.map_map, Function.comp_def, eval₂_sub, eval₂_X,
    eval₂_C, eval₂_X_pow] at e
  exact e

/-- **Lagrange interpolation at the points of `𝔽_p`.** -/
lemma sum_mul_prod_erase_sub_zmodRingHom (h : (p : R) = 0) (x : R) :
    ∑ r : ZMod p, zmodRingHomOfNatCastEqZero p h (∏ s ∈ Finset.univ.erase r, (r - s)⁻¹) *
      ∏ s ∈ Finset.univ.erase r, (x - zmodRingHomOfNatCastEqZero p h s) = 1 := by
  classical
  have hne : (Finset.univ : Finset (ZMod p)).Nonempty := Finset.univ_nonempty
  have := congrArg (eval₂ (zmodRingHomOfNatCastEqZero p h) x)
    (Lagrange.sum_basis (v := id) (Set.injOn_id _) hne)
  simp only [Lagrange.basis, Lagrange.basisDivisor, eval₂_finsetSum, eval₂_finsetProd,
    eval₂_mul, eval₂_C, eval₂_sub, eval₂_X, eval₂_one, id] at this
  rw [← this]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_prod, ← Finset.prod_mul_distrib]

end Algebra

namespace AlgebraicGeometry.Scheme

/-! ### Artin–Schreier covers -/

/-- An element `t` of `Γ(U, ⊤)` whose image under `φ : Γ(U, ⊤) ⟶ R` is of the form `rᵖ - r`
has an Artin–Schreier root on the base change of `Spec R ⟶ Spec Γ(U, ⊤)` along
`U ⟶ Spec Γ(U, ⊤)`. -/
private lemma exists_pow_sub_eq_pullback_fst_toSpecΓ_appTop {U : Scheme.{u}} {R : CommRingCat.{u}}
    (φ : Γ(U, ⊤) ⟶ R) {p : ℕ} {t : Γ(U, ⊤)} {r : R} (h : φ t = r ^ p - r) :
    ∃ ω : Γ(pullback U.toSpecΓ (Spec.map φ), ⊤),
      ω ^ p - ω = (pullback.fst U.toSpecΓ (Spec.map φ)).appTop t := by
  refine ⟨(pullback.snd U.toSpecΓ (Spec.map φ)).appTop ((ΓSpecIso R).inv r), ?_⟩
  rw [pullback_fst_toSpecΓ_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply, h, map_sub,
    map_pow, map_sub, map_pow]

/-- For `p = 0` in `R`, the pair `(Xᵖ - X - t, 1)` is a standard étale pair: the derivative of
`Xᵖ - X - t` is `-1`. -/
noncomputable def standardEtalePairArtinSchreier {R : Type*} [CommRing R] {p : ℕ}
    (hp : p.Prime) (h : (p : R) = 0) (t : R) : StandardEtalePair R where
  f := X ^ p - X - C t
  monic_f := by
    nontriviality R
    have : (X + C t : R[X]).degree < (X ^ p : R[X]).degree := by
      rw [degree_X_add_C, degree_X_pow]
      exact_mod_cast hp.one_lt
    rw [sub_sub]
    exact (monic_X_pow p).sub_of_left this
  g := 1
  cond := ⟨-1, 0, 0, by
    simp only [derivative_sub, derivative_X_pow, derivative_X, derivative_C, mul_zero, add_zero,
      pow_zero]
    rw [show (C (p : R)) = 0 by rw [h, C_0]]
    ring⟩

/-- The standard étale algebra of `(Xᵖ - X - t, 1)` is `R[X]/(Xᵖ - X - t)`. -/
noncomputable def standardEtalePairArtinSchreierRingEquiv {R : Type*} [CommRing R] {p : ℕ}
    (hp : p.Prime) (h : (p : R) = 0) (t : R) :
    (standardEtalePairArtinSchreier hp h t).Ring ≃ₐ[R] AdjoinRoot (X ^ p - X - C t) :=
  .ofAlgHom
    ((standardEtalePairArtinSchreier hp h t).lift (AdjoinRoot.root _)
      ⟨by
        change aeval (AdjoinRoot.root (X ^ p - X - C t)) (X ^ p - X - C t) = 0
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self], by
        change IsUnit (aeval _ (1 : R[X]))
        simp⟩)
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (standardEtalePairArtinSchreier hp h t).X
      StandardEtalePair.hasMap_X.1)
    (AdjoinRoot.algHom_ext (by simp [AdjoinRoot.liftAlgHom_root]))
    (StandardEtalePair.hom_ext (by simp [AdjoinRoot.liftAlgHom_root]))

/-- **Artin–Schreier covers.** Let `U` be a scheme with `p = 0` in `Γ(U, 𝒪)` and `t ∈ Γ(U, 𝒪)`.
Then `t = ωᵖ - ω` on a surjective étale cover of `U`: the base change of
`Spec Γ(U, 𝒪)[y]/(yᵖ - y - t) ⟶ Spec Γ(U, 𝒪)` along `U ⟶ Spec Γ(U, 𝒪)`. The algebra is étale
since the derivative of `yᵖ - y - t` is `-1`, and faithfully flat since it is free of rank
`p ≥ 1`. -/
theorem exists_etale_surjective_pow_sub_eq_appTop {U : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    (h : (p : Γ(U, ⊤)) = 0) (t : Γ(U, ⊤)) :
    ∃ (V : Scheme.{u}) (f : V ⟶ U), Etale f ∧ Surjective f ∧
      ∃ ω : Γ(V, ⊤), ω ^ p - ω = f.appTop t := by
  let φ : Γ(U, ⊤) ⟶ CommRingCat.of (AdjoinRoot (X ^ p - X - C t)) :=
    CommRingCat.ofHom (algebraMap _ _)
  have : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr
      (Algebra.Etale.of_equiv (standardEtalePairArtinSchreierRingEquiv hp h t))
  have hmonic := (standardEtalePairArtinSchreier hp h t).monic_f
  have hdeg : (X ^ p - X - C t : Γ(U, ⊤)[X]).degree ≠ 0 := by
    nontriviality Γ(U, ⊤)
    have : (X ^ p - X - C t : Γ(U, ⊤)[X]) = X ^ p - (X + C t) := by ring
    rw [this, degree_sub_eq_left_of_degree_lt, degree_X_pow]
    · exact_mod_cast hp.ne_zero
    · rw [degree_X_pow, degree_X_add_C]
      exact_mod_cast hp.one_lt
  have : Surjective (Spec.map φ) :=
    ((flat_and_surjective_SpecMap_iff φ).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr
      (AdjoinRoot.faithfullyFlat_of_monic hmonic hdeg))).2
  have hφ : φ t = AdjoinRoot.root (X ^ p - X - C t) ^ p - AdjoinRoot.root (X ^ p - X - C t) := by
    have := AdjoinRoot.eval₂_root (X ^ p - X - C t)
    rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, sub_eq_zero] at this
    exact this.symm
  exact ⟨_, _, inferInstance, inferInstance, exists_pow_sub_eq_pullback_fst_toSpecΓ_appTop φ hφ⟩

/-! ### The Artin–Schreier map on `𝔾ₐ` -/

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hp : (p : Γ(X, ⊤)) = 0)

omit [Fact p.Prime] in
include hp in
lemma natCast_eq_zero_of_etale (U : X.Etale) : (p : Γ(U.left, ⊤)) = 0 := by
  rw [← map_natCast U.hom.appTop.hom, hp, map_zero]

/-- The **Artin–Schreier map** `℘ : 𝔾ₐ ⟶ 𝔾ₐ`, `x ↦ xᵖ - x`, on the small étale site of a scheme
`X` with `p = 0` in `Γ(X, 𝒪)`. -/
noncomputable def gaArtinSchreier : X.gaSheaf ⟶ X.gaSheaf :=
  ⟨{ app U := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((artinSchreierAddHom p (natCast_eq_zero_of_etale X p hp U.unop)).comp
          AddEquiv.ulift.toAddMonoidHom))
     naturality U V g := by
       ext x
       apply ULift.ext
       change (g.unop.left.appTop (ULift.down (α := Γ(U.unop.left, ⊤)) x)) ^ p -
           g.unop.left.appTop (ULift.down (α := Γ(U.unop.left, ⊤)) x) =
         g.unop.left.appTop ((ULift.down (α := Γ(U.unop.left, ⊤)) x) ^ p -
           ULift.down (α := Γ(U.unop.left, ⊤)) x)
       rw [map_sub, map_pow] }⟩

lemma gaArtinSchreier_app_apply (U : X.Etaleᵒᵖ) (x : X.gaSheaf.obj.obj U) :
    ULift.down (α := Γ(U.unop.left, ⊤)) ((X.gaArtinSchreier p hp).hom.app U x) =
      (ULift.down (α := Γ(U.unop.left, ⊤)) x) ^ p - ULift.down (α := Γ(U.unop.left, ⊤)) x :=
  rfl


/-- **`℘` is an epimorphism of étale sheaves**: every section `t` of `𝔾ₐ` is of the form
`ωᵖ - ω` on the Artin–Schreier cover `Spec 𝒪[y]/(yᵖ - y - t)`. -/
theorem isLocallySurjective_gaArtinSchreier :
    Sheaf.IsLocallySurjective (X.gaArtinSchreier p hp) where
  imageSieve_mem {U} s := by
    obtain ⟨V, f, hf, hsurj, ω, hω⟩ := exists_etale_surjective_pow_sub_eq_appTop
      (Fact.out : p.Prime) (natCast_eq_zero_of_etale X p hp U) s.down
    have : Etale (f ≫ U.hom) := by have := U.prop; infer_instance
    let g : MorphismProperty.Over.mk ⊤ (f ≫ U.hom) this ⟶ U :=
      MorphismProperty.Over.homMk f rfl
    refine GrothendieckTopology.superset_covering _ ?_
      ((ofArrows_mem_smallEtaleTopology_iff (fun _ : Unit ↦ g)).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨⟩
      exact ⟨ULift.up ω, ULift.ext hω⟩
    · simp only [Set.iUnion_const]
      exact Set.range_eq_univ.mpr hsurj.surj

/-- The **Artin–Schreier sequence** `ker ℘ ⟶ 𝔾ₐ ⟶ 𝔾ₐ`; its kernel term is the constant sheaf
`ℤ/p` (`AlgebraicGeometry.Scheme.constantZModIsoKernelGaArtinSchreier`). -/
noncomputable def artinSchreierSequence :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (kernel.ι (X.gaArtinSchreier p hp)) (X.gaArtinSchreier p hp)
    (kernel.condition _)

/-- **Exactness of the Artin–Schreier sequence**: `0 → ker ℘ → 𝔾ₐ → 𝔾ₐ → 0` is short exact. -/
theorem artinSchreierSequence_shortExact : (X.artinSchreierSequence p hp).ShortExact :=
  have := X.isLocallySurjective_gaArtinSchreier p hp
  { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
    mono_f := by dsimp [artinSchreierSequence]; infer_instance
    epi_g := Sheaf.epi_of_isLocallySurjective (X.gaArtinSchreier p hp) }

/-! ### The kernel of `℘` is the constant sheaf `ℤ/p` -/

/-- The map of presheaves `ℤ/p ⟶ 𝔾ₐ` from the constant presheaf `ℤ/p`, sending `a ∈ ℤ/p` over an
étale `X`-scheme `U` to the image of `a` in `Γ(U, 𝒪)`. -/
noncomputable def zmodToGaPresheaf :
    (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))) ⟶
      X.gaPresheaf where
  app U := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((zmodRingHomOfNatCastEqZero p hp).toAddMonoidHom.comp AddEquiv.ulift.toAddMonoidHom)) ≫
    X.gaPresheaf.map ((MorphismProperty.Over.mkIdTerminal @Etale X).from U.unop).op
  naturality U V g := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc,
      ← Functor.map_comp]
    congr 3
    exact (MorphismProperty.Over.mkIdTerminal @Etale X).hom_ext _ _

/-- The value of `AlgebraicGeometry.Scheme.zmodToGaPresheaf` at `a` over `U` is the image of
`a` in `Γ(U, 𝒪)`. -/
lemma zmodToGaPresheaf_app_apply (U : X.Etaleᵒᵖ) (a : ZMod p) :
    ULift.down (α := Γ(U.unop.left, ⊤)) ((X.zmodToGaPresheaf p hp).app U (ULift.up a)) =
      U.unop.hom.appTop (zmodRingHomOfNatCastEqZero p hp a) := by
  have h : ((MorphismProperty.Over.mkIdTerminal @Etale X).from U.unop).left = U.unop.hom :=
    (Category.comp_id _).symm.trans
      (MorphismProperty.Over.w ((MorphismProperty.Over.mkIdTerminal @Etale X).from U.unop))
  change ((MorphismProperty.Over.mkIdTerminal @Etale X).from U.unop).left.appTop _ = _
  rw [h]
  rfl

/-- The image of `a ∈ ℤ/p` in `Γ(U, 𝒪)` is the image under the ring map
`ℤ/p → Γ(X, 𝒪) → Γ(U, 𝒪)`. -/
noncomputable abbrev zmodToΓ (U : X.Etale) : ZMod p →+* Γ(U.left, ⊤) :=
  U.hom.appTop.hom.comp (zmodRingHomOfNatCastEqZero p hp)

/-- The map of étale sheaves `ℤ/p ⟶ 𝔾ₐ`: the sheafification of
`AlgebraicGeometry.Scheme.zmodToGaPresheaf`. -/
noncomputable def constantZModToGaSheaf : X.constantZMod p ⟶ X.gaSheaf :=
  ⟨sheafifyLift _ (X.zmodToGaPresheaf p hp) X.isSheaf_gaPresheaf⟩

lemma toSheafify_constantZModToGaSheaf :
    toSheafify _ _ ≫ (X.constantZModToGaSheaf p hp).hom = X.zmodToGaPresheaf p hp :=
  toSheafify_sheafifyLift _ _ _

/-- The constants `a ∈ 𝔽_p` satisfy `aᵖ = a`: the composite `ℤ/p ⟶ 𝔾ₐ ⟶ 𝔾ₐ` vanishes. -/
lemma constantZModToGaSheaf_comp_gaArtinSchreier :
    X.constantZModToGaSheaf p hp ≫ X.gaArtinSchreier p hp = 0 := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ X.isSheaf_gaPresheaf
  rw [InducedCategory.comp_hom, ← Category.assoc, toSheafify_constantZModToGaSheaf]
  ext U a
  apply ULift.ext
  obtain ⟨a⟩ := a
  change ULift.down (α := Γ(U.unop.left, ⊤)) ((X.zmodToGaPresheaf p hp).app U (ULift.up a)) ^ p -
    ULift.down (α := Γ(U.unop.left, ⊤)) ((X.zmodToGaPresheaf p hp).app U (ULift.up a)) = 0
  have key : (U.unop.hom.appTop (zmodRingHomOfNatCastEqZero p hp a)) ^ p -
      U.unop.hom.appTop (zmodRingHomOfNatCastEqZero p hp a) = 0 := by
    rw [← map_pow, ← map_pow (zmodRingHomOfNatCastEqZero p hp) a p, ZMod.pow_card, sub_self]
  rw [zmodToGaPresheaf_app_apply]
  exact key

/-- The map `θ : ℤ/p ⟶ ker ℘` of étale sheaves; it is an isomorphism
(`AlgebraicGeometry.Scheme.isIso_constantZModToKernelGaArtinSchreier`). -/
noncomputable def constantZModToKernelGaArtinSchreier :
    X.constantZMod p ⟶ kernel (X.gaArtinSchreier p hp) :=
  kernel.lift _ (X.constantZModToGaSheaf p hp) (X.constantZModToGaSheaf_comp_gaArtinSchreier p hp)

/-- **Local injectivity of `ℤ/p ⟶ 𝔾ₐ`.** If two constants `a ≠ b` agree on `U`, then the unit
`a - b` of `𝔽_p` vanishes on `U`, so `U` is empty. -/
lemma isLocallyInjective_zmodToGaPresheaf :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (X.zmodToGaPresheaf p hp) where
  equalizerSieve_mem {U} a b hab := by
    by_cases hab' : a = b
    · subst hab'
      simp
    have : Subsingleton Γ(U.unop.left, ⊤) := by
      obtain ⟨i⟩ := a
      obtain ⟨j⟩ := b
      have e := congrArg (ULift.down (α := Γ(U.unop.left, ⊤))) hab
      rw [zmodToGaPresheaf_app_apply, zmodToGaPresheaf_app_apply] at e
      have hij : i - j ≠ 0 := sub_ne_zero.2 fun h ↦ hab' (by rw [h])
      have e' : zmodToΓ X p hp U.unop (i - j) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.2 e
      refine subsingleton_of_zero_eq_one ?_
      rw [← map_one (zmodToΓ X p hp U.unop), ← mul_inv_cancel₀ hij, map_mul, e', zero_mul]
    have := Scheme.isEmpty_of_subsingleton_Γ this
    refine GrothendieckTopology.superset_covering _ ?_
      ((ofArrows_mem_smallEtaleTopology_iff (W := U.unop) (Z := PEmpty.elim)
        (fun i : PEmpty.{1} ↦ i.elim)).2 (Set.eq_univ_of_forall fun p ↦ isEmptyElim p))
    rintro _ _ ⟨_, _, _, ⟨i⟩, -⟩
    exact i.elim

/-- **Local surjectivity of `ℤ/p ⟶ ker ℘`.** A section `x` of `𝔾ₐ` with `xᵖ = x` is locally
constant with values in `𝔽_p`: with `y_r = ∏_{s ≠ r} (x - s)`, `x = r` on the basic open set
`D(y_r)`, as `y_r (x - r) = xᵖ - x = 0`, and these open sets cover, as the `y_r` generate the unit
ideal by Lagrange interpolation. -/
lemma imageSieve_zmodToGaPresheaf_mem {U : X.Etale} (x : X.gaPresheaf.obj (op U))
    (hx : (ULift.down (α := Γ(U.left, ⊤)) x) ^ p - ULift.down (α := Γ(U.left, ⊤)) x = 0) :
    Presheaf.imageSieve (X.zmodToGaPresheaf p hp) x ∈ X.smallEtaleTopology U := by
  classical
  let ρ := zmodToΓ X p hp U
  have hpU := natCast_eq_zero_of_etale X p hp U
  have hρ (s : ZMod p) : ρ s = zmodRingHomOfNatCastEqZero p hpU s := by
    have : (zmodRingHomOfNatCastEqZero p hpU) = ρ := RingHom.ext_zmod _ _
    rw [this]
  let u : Γ(U.left, ⊤) := ULift.down (α := Γ(U.left, ⊤)) x
  let y : ZMod p → Γ(U.left, ⊤) := fun r ↦ ∏ s ∈ Finset.univ.erase r, (u - ρ s)
  let D : ZMod p → U.left.Opens := fun r ↦ U.left.basicOpen (y r)
  have hD (r : ZMod p) : Etale ((D r).ι ≫ U.hom) := by have := U.prop; infer_instance
  let g : ∀ r : ZMod p, MorphismProperty.Over.mk ⊤ ((D r).ι ≫ U.hom) (hD r) ⟶ U :=
    fun r ↦ MorphismProperty.Over.homMk (D r).ι rfl
  refine GrothendieckTopology.superset_covering _ ?_
    ((ofArrows_mem_smallEtaleTopology_iff g).2 ?_)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨r⟩
    refine ⟨ULift.up r, ULift.ext ?_⟩
    refine (X.zmodToGaPresheaf_app_apply p hp _ r).trans ?_
    change ((D r).ι ≫ U.hom).appTop (zmodRingHomOfNatCastEqZero p hp r) = (D r).ι.appTop u
    have h0 : (D r).ι.appTop (y r * (u - ρ r)) = 0 := by
      have e : y r * (u - ρ r) = u ^ p - u := by
        rw [← prod_sub_zmodRingHom p hpU u]
        simp only [y, hρ]
        exact Finset.prod_erase_mul _ _ (Finset.mem_univ r)
      rw [e, hx, map_zero]
    rw [map_mul, (U.left.isUnit_ι_appTop_basicOpen (y r)).mul_right_eq_zero, map_sub,
      sub_eq_zero] at h0
    have key : ((D r).ι ≫ U.hom).appTop (zmodRingHomOfNatCastEqZero p hp r) = (D r).ι.appTop u := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h0]
      rfl
    exact key
  · have hspan : Ideal.span (Set.range y) = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have e := sum_mul_prod_erase_sub_zmodRingHom p hpU u
      simp only [← hρ] at e
      rw [← e]
      exact Ideal.sum_mem _ fun r _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨r, rfl⟩)
    have hcov := iSup_basicOpen_of_span_eq_top (X := U.left) ⊤ _ hspan
    refine Set.eq_univ_of_forall fun q ↦ ?_
    have hq : q ∈ (⨆ i ∈ Set.range y, U.left.basicOpen i) := by
      rw [hcov]; exact TopologicalSpace.Opens.mem_top q
    simp only [TopologicalSpace.Opens.mem_iSup] at hq
    obtain ⟨_, ⟨r, rfl⟩, hqr⟩ := hq
    refine Set.mem_iUnion.2 ⟨r, ?_⟩
    change q ∈ Set.range (D r).ι
    rw [Scheme.Opens.range_ι]
    exact hqr

/-- The inclusion `ker ℘ ⟶ 𝔾ₐ` is injective on sections. -/
lemma injective_kernelι_gaArtinSchreier_app (U : X.Etaleᵒᵖ) :
    Function.Injective ((kernel.ι (X.gaArtinSchreier p hp)).hom.app U) := by
  have : Mono ((sheafToPresheaf _ _).map (kernel.ι (X.gaArtinSchreier p hp))) := inferInstance
  have : Mono ((kernel.ι (X.gaArtinSchreier p hp)).hom.app U) :=
    inferInstanceAs (Mono (((sheafToPresheaf _ _).map
      (kernel.ι (X.gaArtinSchreier p hp))).app U))
  exact (AddCommGrpCat.mono_iff_injective _).1 this

/-- **`θ: ℤ/p ⟶ ker ℘` is an isomorphism.** It is locally injective
(`AlgebraicGeometry.Scheme.isLocallyInjective_zmodToGaPresheaf`) and locally surjective
(`AlgebraicGeometry.Scheme.imageSieve_zmodToGaPresheaf_mem`). -/
theorem isIso_constantZModToKernelGaArtinSchreier :
    IsIso (X.constantZModToKernelGaArtinSchreier p hp) := by
  set θ := X.constantZModToKernelGaArtinSchreier p hp
  set ι := kernel.ι (X.gaArtinSchreier p hp)
  have e : θ.hom ≫ ι.hom = (X.constantZModToGaSheaf p hp).hom :=
    congrArg (fun φ : X.constantZMod p ⟶ X.gaSheaf ↦ φ.hom)
      (kernel.lift_ι (X.gaArtinSchreier p hp) (X.constantZModToGaSheaf p hp)
        (X.constantZModToGaSheaf_comp_gaArtinSchreier p hp))
  have fac : (toSheafify X.smallEtaleTopology _ ≫ θ.hom) ≫ ι.hom =
      X.zmodToGaPresheaf p hp := by
    rw [Category.assoc, e]
    exact X.toSheafify_constantZModToGaSheaf p hp
  have := X.isLocallyInjective_zmodToGaPresheaf p hp
  refine (Sheaf.isLocallyBijective_iff_isIso θ).1 ⟨?_, ?_⟩
  · have : Presheaf.IsLocallyInjective X.smallEtaleTopology
        (toSheafify X.smallEtaleTopology _ ≫ θ.hom) :=
      Presheaf.isLocallyInjective_of_isLocallyInjective_fac _ fac
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective _
      (toSheafify X.smallEtaleTopology _) θ.hom
  · have : Presheaf.IsLocallySurjective X.smallEtaleTopology
        (toSheafify X.smallEtaleTopology _ ≫ θ.hom) := by
      refine ⟨fun {U} s ↦ ?_⟩
      have hx : ULift.down (α := Γ(U.left, ⊤)) (ι.hom.app (op U) s) ^ p -
          ULift.down (α := Γ(U.left, ⊤)) (ι.hom.app (op U) s) = 0 := by
        have h := congrArg (fun φ : kernel (X.gaArtinSchreier p hp) ⟶ X.gaSheaf ↦
          ULift.down (α := Γ(U.left, ⊤)) (φ.hom.app (op U) s))
          (kernel.condition (X.gaArtinSchreier p hp))
        exact h
      refine GrothendieckTopology.superset_covering _ ?_
        (X.imageSieve_zmodToGaPresheaf_mem p hp _ hx)
      rintro V g ⟨t, ht⟩
      refine ⟨t, X.injective_kernelι_gaArtinSchreier_app p hp _ ?_⟩
      calc ι.hom.app _ ((toSheafify _ _ ≫ θ.hom).app _ t)
          = ((toSheafify _ _ ≫ θ.hom) ≫ ι.hom).app _ t := rfl
        _ = (X.zmodToGaPresheaf p hp).app _ t := by rw [fac]; rfl
        _ = X.gaPresheaf.map g.op (ι.hom.app _ s) := ht
        _ = ι.hom.app _ ((kernel (X.gaArtinSchreier p hp)).obj.map g.op s) :=
          (NatTrans.naturality_apply ι.hom g.op s).symm
    exact Presheaf.isLocallySurjective_of_isLocallySurjective _ (toSheafify _ _) θ.hom

/-- The isomorphism `ℤ/p ≅ ker ℘` of étale sheaves on a scheme with `p = 0`. -/
noncomputable def constantZModIsoKernelGaArtinSchreier :
    X.constantZMod p ≅ kernel (X.gaArtinSchreier p hp) :=
  haveI := X.isIso_constantZModToKernelGaArtinSchreier p hp
  asIso (X.constantZModToKernelGaArtinSchreier p hp)

/-! ### Vanishing on affine schemes -/

/-- **Vanishing of `ℤ/p`-cohomology of an affine scheme in characteristic `p`.** Let `X` be an
affine scheme with `p = 0` in `Γ(X, 𝒪_X)`. Then `Hᵠ(X_ét, ℤ/p) = 0` for `q ≥ 2`. This combines
the exactness of the Artin–Schreier sequence `0 → ℤ/p → 𝔾ₐ → 𝔾ₐ → 0` with the vanishing of `Hᵠ(X_ét,
𝔾ₐ)` for `q ≥ 1`
on an affine scheme. -/
theorem subsingleton_sheafH_constantZMod_of_isAffine (X : Scheme.{u}) [IsAffine X] (p : ℕ)
    [Fact p.Prime] (hp : (p : Γ(X, ⊤)) = 0) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H (X.constantZMod p) q) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 + 1 := ⟨q - 2, by omega⟩
  have hS := X.artinSchreierSequence_shortExact p hp
  have h₁ : Subsingleton (Sheaf.H (X.artinSchreierSequence p hp).X₃ (n + 1)) :=
    X.subsingleton_sheafH_gaSheaf_of_isAffine n
  have h₂ : Subsingleton (Sheaf.H (X.artinSchreierSequence p hp).X₂ (n + 1 + 1)) :=
    X.subsingleton_sheafH_gaSheaf_of_isAffine (n + 1)
  have hker : Subsingleton (Sheaf.H (kernel (X.gaArtinSchreier p hp)) (n + 1 + 1)) := by
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := (Sheaf.H.exact_δSucc_map hS (n + 1) x).1 (Subsingleton.elim _ _)
    rw [Subsingleton.elim y 0, map_zero]
  let e := X.constantZModIsoKernelGaArtinSchreier p hp
  exact (Function.LeftInverse.injective (f := Sheaf.H.map e.hom (n + 1 + 1))
    (g := Sheaf.H.map e.inv (n + 1 + 1))
    fun x ↦ by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]).subsingleton

end AlgebraicGeometry.Scheme

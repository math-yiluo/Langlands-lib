/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.Mathlib.LinearAlgebra.Lagrange

/-!
# The sheaf of roots of unity over a base with enough roots of unity

Let `X` be a scheme and `ζ` a global unit of `X` with `ζ ^ n = 1` such that the differences
`ζ ^ i - ζ ^ j`, `i ≠ j < n`, are invertible on `X`. Then the map `θ_ζ : ℤ/n ⟶ μₙ`,
`a ↦ ζ ^ a`, of étale sheaves (`AlgebraicGeometry.Scheme.constantZModToRootsOfUnitySheaf`) is an
isomorphism (`AlgebraicGeometry.Scheme.isIso_constantZModToRootsOfUnitySheaf_of_isUnit_sub`).

This is the version over a general base of
`AlgebraicGeometry.Scheme.isIso_constantZModToRootsOfUnitySheaf`, where `ζ` comes from a
primitive root of unity of a base field. The proof is the same: a section `x` of `μₙ` over an
étale `U` equals `ζ ^ r` on the basic open set of `y_r = ∏_{s ≠ r} (x - ζ ^ s)`, as
`y_r (x - ζ ^ r) = xⁿ - 1 = 0`, and these basic open sets cover `U` by Lagrange interpolation at
the nodes `ζ ^ r`; both identities hold over any commutative ring once the differences of the
nodes are invertible (`Polynomial.X_pow_sub_one_eq_prod_of_isUnit_sub`,
`Polynomial.sum_inverse_mul_prod_erase_eq_one`).

## Main statements

- `AlgebraicGeometry.Scheme.isIso_constantZModToRootsOfUnitySheaf_of_isUnit_sub`: `θ_ζ` is an
  isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (n : ℕ)

lemma nsmul_gmSheaf_hom_app_apply (m : ℕ) (U : X.Etaleᵒᵖ) (x : X.gmSheaf.obj.obj U) :
    (m • 𝟙 X.gmSheaf).hom.app U x = m • x := by
  have e : (m • 𝟙 X.gmSheaf).hom = m • 𝟙 X.gmSheaf.obj :=
    (sheafToPresheaf _ _).map_nsmul (f := 𝟙 X.gmSheaf) (n := m)
  rw [e, NatTrans.app_nsmul, NatTrans.id_app]
  rfl

/-- **Local surjectivity of `a ↦ ζ ^ a` onto `μₙ`.** Let `ζ` be a global unit of `X` with
`ζ ^ n = 1` such that the differences `ζ ^ i - ζ ^ j`, `i ≠ j < n`, are invertible. Every section
`x` of `𝔾ₘ` with `xⁿ = 1` is, locally on `X_ét`, of the form `ζ ^ a`. -/
lemma imageSieve_zmodToGmPresheaf_mem_of_isUnit_sub [NeZero n] (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1)
    (hζ' : ∀ i < n, ∀ j < n, i ≠ j → IsUnit ((ζ : Γ(X, ⊤)) ^ i - (ζ : Γ(X, ⊤)) ^ j))
    {U : X.Etale} (x : X.gmPresheaf.obj (op U)) (hx : n • x = 0) :
    Presheaf.imageSieve (X.zmodToGmPresheaf n ζ hζ) x ∈ X.smallEtaleTopology U := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let ρ : Γ(X, ⊤) →+* Γ(U.left, ⊤) := U.hom.appTop.hom
  let z : Γ(X, ⊤) := ζ
  have hz : z ^ n = 1 := by
    simpa [z] using congrArg Units.val hζ
  let u : Γ(U.left, ⊤) := ((Additive.toMul x.down : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤))
  have hu : u ^ n = 1 := by
    have : (Additive.toMul (n • x.down) : Γ(U.left, ⊤)ˣ) = 1 := by
      rw [show n • x.down = (n • x).down from rfl, hx]
      rfl
    rw [toMul_nsmul] at this
    simpa [u] using congrArg Units.val this
  let R := Finset.range n
  let y : R → Γ(U.left, ⊤) := fun r ↦ ∏ s ∈ R.erase r, (u - ρ (z ^ s))
  let D : R → U.left.Opens := fun r ↦ U.left.basicOpen (y r)
  have hD (r : R) : Etale ((D r).ι ≫ U.hom) := by have := U.prop; infer_instance
  let g : ∀ r : R, MorphismProperty.Over.mk ⊤ ((D r).ι ≫ U.hom) (hD r) ⟶ U :=
    fun r ↦ MorphismProperty.Over.homMk (D r).ι rfl
  refine GrothendieckTopology.superset_covering _ ?_
    ((ofArrows_mem_smallEtaleTopology_iff g).2 ?_)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨r⟩
    refine ⟨ULift.up ((r : ℕ) : ZMod n), ?_⟩
    apply ULift.ext
    apply Additive.toMul.injective
    apply Units.ext
    refine (X.zmodToGmPresheaf_app_natCast n ζ hζ _ r).trans
      (Eq.trans ?_ (gmPresheaf_map_apply (g r) x).symm)
    change ((D r).ι ≫ U.hom).appTop (ζ : Γ(X, ⊤)) ^ (r : ℕ) = (D r).ι.appTop u
    have hprod := congrArg (Polynomial.eval₂ ρ u)
      (Polynomial.X_pow_sub_one_eq_prod_of_isUnit_sub hn hz hζ')
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, hu, sub_self,
      Polynomial.eval₂_finsetProd, Polynomial.eval₂_X, Polynomial.eval₂_C] at hprod
    rw [← Finset.prod_erase_mul _ _ r.2] at hprod
    have h0 := congrArg (D r).ι.appTop hprod.symm
    rw [map_mul, map_zero, (U.left.isUnit_ι_appTop_basicOpen (y r)).mul_right_eq_zero, map_sub,
      sub_eq_zero] at h0
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h0, map_pow, map_pow]
    rfl
  · have hspan : Ideal.span (Set.range y) = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have hsum := congrArg (Polynomial.eval₂ ρ u)
        (Polynomial.sum_inverse_mul_prod_erase_eq_one hn hζ')
      simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_one] at hsum
      rw [← hsum]
      exact Ideal.sum_mem _ fun r hr ↦
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨r, hr⟩, rfl⟩)
    have hcov := iSup_basicOpen_of_span_eq_top (X := U.left) ⊤ _ hspan
    refine Set.eq_univ_of_forall fun p ↦ ?_
    have hp : p ∈ (⨆ i ∈ Set.range y, U.left.basicOpen i) := by
      rw [hcov]; exact TopologicalSpace.Opens.mem_top p
    simp only [TopologicalSpace.Opens.mem_iSup] at hp
    obtain ⟨_, ⟨r, rfl⟩, hpr⟩ := hp
    refine Set.mem_iUnion.2 ⟨r, ?_⟩
    change p ∈ Set.range (D r).ι
    rw [Scheme.Opens.range_ι]
    exact hpr

/-- **Local injectivity of `a ↦ ζ ^ a`.** If the differences `ζ ^ i - ζ ^ j`, `i ≠ j < n`, are
invertible, then `ζ ^ a = ζ ^ b` on a nonempty `U` forces `a = b`. -/
lemma isLocallyInjective_zmodToGmPresheaf_of_isUnit_sub [NeZero n] (ζ : Γ(X, ⊤)ˣ)
    (hζ : ζ ^ n = 1)
    (hζ' : ∀ i < n, ∀ j < n, i ≠ j → IsUnit ((ζ : Γ(X, ⊤)) ^ i - (ζ : Γ(X, ⊤)) ^ j)) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (X.zmodToGmPresheaf n ζ hζ) where
  equalizerSieve_mem {U} a b hab := by
    by_cases hab' : a = b
    · subst hab'
      simp
    have : Subsingleton Γ(U.unop.left, ⊤) := by
      let ρ : Γ(X, ⊤) →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom
      have e := congrArg (fun z : X.gmPresheaf.obj U ↦
        ((Additive.toMul z.down : Γ(U.unop.left, ⊤)ˣ) : Γ(U.unop.left, ⊤))) hab
      obtain ⟨i⟩ := a
      obtain ⟨j⟩ := b
      have hij : i.val ≠ j.val := fun hij ↦ hab' (congrArg ULift.up (ZMod.val_injective n hij))
      rw [← ZMod.natCast_zmod_val i, ← ZMod.natCast_zmod_val j, zmodToGmPresheaf_app_natCast,
        zmodToGmPresheaf_app_natCast] at e
      have e' : ρ ((ζ : Γ(X, ⊤)) ^ i.val - (ζ : Γ(X, ⊤)) ^ j.val) = 0 := by
        rw [map_sub, map_pow, map_pow]
        exact sub_eq_zero.2 e
      obtain ⟨c, hc⟩ := hζ' i.val (ZMod.val_lt i) j.val (ZMod.val_lt j) hij
      refine subsingleton_of_zero_eq_one ?_
      rw [← map_one ρ, ← c.mul_inv, hc, map_mul, e', zero_mul]
    have := Scheme.isEmpty_of_subsingleton_Γ this
    refine GrothendieckTopology.superset_covering _ ?_
      ((ofArrows_mem_smallEtaleTopology_iff (W := U.unop) (Z := PEmpty.elim)
        (fun i : PEmpty.{1} ↦ i.elim)).2 (Set.eq_univ_of_forall fun p ↦ isEmptyElim p))
    rintro _ _ ⟨_, _, _, ⟨i⟩, -⟩
    exact i.elim

/-- **`θ_ζ` is an isomorphism over a base with enough roots of unity.** Let `ζ` be a global unit
of `X` with `ζ ^ n = 1` such that the differences `ζ ^ i - ζ ^ j`, `i ≠ j < n`, are invertible.
Then `θ_ζ : ℤ/n ⟶ μₙ`, `a ↦ ζ ^ a`, is an isomorphism of étale sheaves. -/
theorem isIso_constantZModToRootsOfUnitySheaf_of_isUnit_sub [NeZero n] (ζ : Γ(X, ⊤)ˣ)
    (hζ : ζ ^ n = 1)
    (hζ' : ∀ i < n, ∀ j < n, i ≠ j → IsUnit ((ζ : Γ(X, ⊤)) ^ i - (ζ : Γ(X, ⊤)) ^ j)) :
    IsIso (X.constantZModToRootsOfUnitySheaf n ζ hζ) := by
  set θ := X.constantZModToRootsOfUnitySheaf n ζ hζ
  set ι := kernel.ι (n • 𝟙 X.gmSheaf)
  have e : θ.hom ≫ ι.hom = (X.constantZModToGmSheaf n ζ hζ).hom :=
    congrArg (fun φ : X.constantZMod n ⟶ X.gmSheaf ↦ φ.hom)
      (kernel.lift_ι (n • 𝟙 X.gmSheaf) (X.constantZModToGmSheaf n ζ hζ)
        (X.constantZModToGmSheaf_comp_nsmul n ζ hζ))
  have fac : (toSheafify X.smallEtaleTopology _ ≫ θ.hom) ≫ ι.hom =
      X.zmodToGmPresheaf n ζ hζ := by
    rw [Category.assoc, e]
    exact X.toSheafify_constantZModToGmSheaf n ζ hζ
  have := X.isLocallyInjective_zmodToGmPresheaf_of_isUnit_sub n ζ hζ hζ'
  refine (Sheaf.isLocallyBijective_iff_isIso θ).1 ⟨?_, ?_⟩
  · have : Presheaf.IsLocallyInjective X.smallEtaleTopology
        (toSheafify X.smallEtaleTopology _ ≫ θ.hom) :=
      Presheaf.isLocallyInjective_of_isLocallyInjective_fac _ fac
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective _
      (toSheafify X.smallEtaleTopology _) θ.hom
  · have : Presheaf.IsLocallySurjective X.smallEtaleTopology
        (toSheafify X.smallEtaleTopology _ ≫ θ.hom) := by
      refine ⟨fun {U} s ↦ ?_⟩
      have hx : n • ι.hom.app (op U) s = 0 := by
        rw [← nsmul_gmSheaf_hom_app_apply, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
          ← InducedCategory.comp_hom, kernel.condition]
        rfl
      refine GrothendieckTopology.superset_covering _ ?_
        (X.imageSieve_zmodToGmPresheaf_mem_of_isUnit_sub n ζ hζ hζ' _ hx)
      rintro V g ⟨t, ht⟩
      refine ⟨t, X.injective_kernelι_app n _ ?_⟩
      calc ι.hom.app _ ((toSheafify _ _ ≫ θ.hom).app _ t)
          = ((toSheafify _ _ ≫ θ.hom) ≫ ι.hom).app _ t := rfl
        _ = (X.zmodToGmPresheaf n ζ hζ).app _ t := by rw [fac]; rfl
        _ = X.gmPresheaf.map g.op (ι.hom.app _ s) := ht
        _ = ι.hom.app _ ((X.rootsOfUnitySheaf n).obj.map g.op s) :=
          (NatTrans.naturality_apply ι.hom g.op s).symm
    exact Presheaf.isLocallySurjective_of_isLocallySurjective _ (toSheafify _ _) θ.hom

end AlgebraicGeometry.Scheme

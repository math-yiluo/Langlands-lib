/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# The trivialization of the sheaf of roots of unity

Let `X` be a scheme over a field `k` and let `ζ ∈ k` be a primitive `n`-th root of unity. Then
`a ↦ ζ ^ a` is an isomorphism `θ_ζ : ℤ/n ≅ μₙ` of étale sheaves on `X` from the constant sheaf
`ℤ/n` to the sheaf `μₙ` of `n`-th roots of unity. In particular the cohomology of `μₙ` is that
of `ℤ/n` once a primitive root of unity is chosen.

The map is first defined for any global unit `ζ` of `X` with `ζ ^ n = 1`, as the sheafification
of the map of presheaves `a ↦ ζ ^ a`, which lands in `μₙ = ker(n • 𝟙 : 𝔾ₘ ⟶ 𝔾ₘ)`. It is an
isomorphism because it is locally injective and locally surjective. Local surjectivity is the
decomposition of an étale `X`-scheme `U` with a section `x` of `μₙ` into the open sets on which
`x` is constant: with `y_r = ∏_{s ≠ r} (x - s)`, `x = r` where `y_r` is invertible, and the `y_r`
generate the unit ideal by Lagrange interpolation at the `n`-th roots of unity.

## Main definitions

- `AlgebraicGeometry.Scheme.constantZModToRootsOfUnitySheaf`: the map `θ_ζ : ℤ/n ⟶ μₙ`,
  `a ↦ ζ ^ a`, for a global unit `ζ` with `ζ ^ n = 1`.
- `AlgebraicGeometry.Scheme.constantZModIsoRootsOfUnitySheaf`: the isomorphism `ℤ/n ≅ μₙ` for
  `ζ` a primitive `n`-th root of unity of the base field.

## Main statements

- `AlgebraicGeometry.Scheme.isIso_constantZModToRootsOfUnitySheaf`: `θ_ζ` is an isomorphism when
  `ζ` comes from a primitive `n`-th root of unity of the base field.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (n : ℕ)

/-- The homomorphism `ZMod n →+ Additive G`, `a ↦ ζ ^ a`, for `ζ` with `ζ ^ n = 1`. -/
private noncomputable abbrev zmodHomOfPowEqOne {G : Type*} [CommGroup G] (ζ : G)
    (hζ : ζ ^ n = 1) : ZMod n →+ Additive G :=
  ZMod.lift n ⟨zmultiplesHom _ (Additive.ofMul ζ), by simp [← ofMul_pow, hζ]⟩

private lemma zmodHomOfPowEqOne_natCast {G : Type*} [CommGroup G] (ζ : G) (hζ : ζ ^ n = 1)
    (a : ℕ) : zmodHomOfPowEqOne n ζ hζ a = Additive.ofMul (ζ ^ a) := by
  rw [show ((a : ℕ) : ZMod n) = ((a : ℤ) : ZMod n) from (Int.cast_natCast a).symm,
    zmodHomOfPowEqOne, ZMod.lift_coe]
  simp [← ofMul_pow]

variable (X)

/-- The map of presheaves `ℤ/n ⟶ 𝔾ₘ` from the constant presheaf `ℤ/n` on the small étale site of
`X`, sending `a ∈ ℤ/n` over an étale `X`-scheme `U` to the restriction of `ζ ^ a` to `U`, for a
global unit `ζ` of `X` with `ζ ^ n = 1`. Its sheafification is
`AlgebraicGeometry.Scheme.constantZModToGmSheaf`. -/
noncomputable def zmodToGmPresheaf (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) :
    (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ⟶ X.gmPresheaf where
  app U := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((ZMod.lift n ⟨zmultiplesHom _ (Additive.ofMul ζ), by simp [← ofMul_pow, hζ]⟩).comp
          AddEquiv.ulift.toAddMonoidHom)) ≫
      X.gmPresheaf.map ((MorphismProperty.Over.mkIdTerminal @Etale X).from U.unop).op
  naturality U V g := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc,
      ← Functor.map_comp]
    congr 3
    exact (MorphismProperty.Over.mkIdTerminal @Etale X).hom_ext _ _

/-- The value of `AlgebraicGeometry.Scheme.zmodToGmPresheaf` at `a ∈ ℕ` over `U` is `ζ ^ a`. -/
lemma zmodToGmPresheaf_app_natCast (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) (U : X.Etaleᵒᵖ) (a : ℕ) :
    ((Additive.toMul ((X.zmodToGmPresheaf n ζ hζ).app U (ULift.up (a : ZMod n))).down :
      Γ(U.unop.left, ⊤)ˣ) : Γ(U.unop.left, ⊤)) = U.unop.hom.appTop (ζ : Γ(X, ⊤)) ^ a := by
  have h : ((MorphismProperty.Over.mkIdTerminal @Etale X).from U.unop).left = U.unop.hom :=
    (Category.comp_id _).symm.trans
      (MorphismProperty.Over.w ((MorphismProperty.Over.mkIdTerminal @Etale X).from U.unop))
  change ((MorphismProperty.Over.mkIdTerminal @Etale X).from U.unop).left.appTop
    ((Additive.toMul (zmodHomOfPowEqOne n ζ hζ (a : ZMod n)) : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) = _
  rw [h, zmodHomOfPowEqOne_natCast, toMul_ofMul, Units.val_pow_eq_pow_val, map_pow]
  rfl

private lemma nsmul_hom_app_apply (m : ℕ) (U : X.Etaleᵒᵖ) (x : X.gmSheaf.obj.obj U) :
    (m • 𝟙 X.gmSheaf).hom.app U x = m • x := by
  have e : (m • 𝟙 X.gmSheaf).hom = m • 𝟙 X.gmSheaf.obj :=
    (sheafToPresheaf _ _).map_nsmul (f := 𝟙 X.gmSheaf) (n := m)
  rw [e, NatTrans.app_nsmul, NatTrans.id_app]
  rfl

/-- The map of étale sheaves `ℤ/n ⟶ 𝔾ₘ`, `a ↦ ζ ^ a`, for a global unit `ζ` of `X` with
`ζ ^ n = 1`: the sheafification of `AlgebraicGeometry.Scheme.zmodToGmPresheaf`. -/
noncomputable def constantZModToGmSheaf (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) :
    X.constantZMod n ⟶ X.gmSheaf :=
  ⟨sheafifyLift _ (X.zmodToGmPresheaf n ζ hζ) X.isSheaf_gmPresheaf⟩

/-- `AlgebraicGeometry.Scheme.constantZModToGmSheaf` extends
`AlgebraicGeometry.Scheme.zmodToGmPresheaf` along the sheafification map. -/
lemma toSheafify_constantZModToGmSheaf (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) :
    toSheafify _ _ ≫ (X.constantZModToGmSheaf n ζ hζ).hom = X.zmodToGmPresheaf n ζ hζ :=
  toSheafify_sheafifyLift _ _ _

/-- The map `a ↦ ζ ^ a` lands in `μₙ`: its composite with the `n`-th power map is zero. -/
lemma constantZModToGmSheaf_comp_nsmul (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) :
    X.constantZModToGmSheaf n ζ hζ ≫ (n • 𝟙 X.gmSheaf) = 0 := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ X.isSheaf_gmPresheaf
  rw [InducedCategory.comp_hom, ← Category.assoc, toSheafify_constantZModToGmSheaf]
  ext U a
  change (n • 𝟙 X.gmSheaf).hom.app U ((X.zmodToGmPresheaf n ζ hζ).app U a) = _
  rw [nsmul_hom_app_apply]
  refine (map_nsmul ((X.zmodToGmPresheaf n ζ hζ).app U).hom n a).symm.trans ?_
  have ha : n • a = 0 := ULift.ext (by
    change n • a.down = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])
  rw [ha, map_zero]
  rfl

/-- **The trivialization associated to `ζ`.** For a global unit `ζ` of `X` with `ζ ^ n = 1`,
the map of étale sheaves `θ_ζ: ℤ/n ⟶ μₙ`, `a ↦ ζ ^ a`. It is an isomorphism when `X` lives over
a field `k` and `ζ` comes from a primitive `n`-th root of unity of `k`
(`AlgebraicGeometry.Scheme.isIso_constantZModToRootsOfUnitySheaf`). -/
noncomputable def constantZModToRootsOfUnitySheaf (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) :
    X.constantZMod n ⟶ X.rootsOfUnitySheaf n :=
  kernel.lift _ (X.constantZModToGmSheaf n ζ hζ) (X.constantZModToGmSheaf_comp_nsmul n ζ hζ)

variable {k : Type u} [Field k]

/-- **Local surjectivity of `a ↦ ζ ^ a` onto `μₙ`.** Let `X` be a scheme over a field `k`, `ζ₀`
a primitive `n`-th root of unity of `k` and `ζ` its image on `X`. Every section `x` of `𝔾ₘ` with
`xⁿ = 1` is, locally on `X_ét`, of the form `ζ ^ a`. -/
lemma imageSieve_zmodToGmPresheaf_mem [NeZero n] (f : X ⟶ Spec (.of k)) {ζ₀ : k}
    (hζ₀ : IsPrimitiveRoot ζ₀ n) (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1)
    (h : (ζ : Γ(X, ⊤)) = ((ΓSpecIso (.of k)).inv ≫ f.appTop) ζ₀) {U : X.Etale}
    (x : X.gmPresheaf.obj (op U)) (hx : n • x = 0) :
    Presheaf.imageSieve (X.zmodToGmPresheaf n ζ hζ) x ∈ X.smallEtaleTopology U := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let ρ : k →+* Γ(U.left, ⊤) := ((ΓSpecIso (.of k)).inv ≫ f.appTop ≫ U.hom.appTop).hom
  let u : Γ(U.left, ⊤) := ((Additive.toMul x.down : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤))
  have hu : u ^ n = 1 := by
    have : (Additive.toMul (n • x.down) : Γ(U.left, ⊤)ˣ) = 1 := by
      rw [show n • x.down = (n • x).down from rfl, hx]
      rfl
    rw [toMul_nsmul] at this
    simpa [u] using congrArg Units.val this
  let R := Polynomial.nthRootsFinset n (1 : k)
  let y : R → Γ(U.left, ⊤) := fun r ↦ ∏ s ∈ R.erase r, (u - ρ s)
  let D : R → U.left.Opens := fun r ↦ U.left.basicOpen (y r)
  have hD (r : R) : Etale ((D r).ι ≫ U.hom) := by have := U.prop; infer_instance
  let g : ∀ r : R, MorphismProperty.Over.mk ⊤ ((D r).ι ≫ U.hom) (hD r) ⟶ U :=
    fun r ↦ MorphismProperty.Over.homMk (D r).ι rfl
  refine GrothendieckTopology.superset_covering _ ?_
    ((ofArrows_mem_smallEtaleTopology_iff g).2 ?_)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨r⟩
    obtain ⟨i, -, hi⟩ := hζ₀.eq_pow_of_pow_eq_one
      ((Polynomial.mem_nthRootsFinset hn _).1 r.2)
    refine ⟨ULift.up (i : ZMod n), ?_⟩
    apply ULift.ext
    apply Additive.toMul.injective
    apply Units.ext
    refine (X.zmodToGmPresheaf_app_natCast n ζ hζ _ i).trans
      (Eq.trans ?_ (gmPresheaf_map_apply (g r) x).symm)
    change ((D r).ι ≫ U.hom).appTop (ζ : Γ(X, ⊤)) ^ i = (D r).ι.appTop u
    have hρ : U.hom.appTop (ζ : Γ(X, ⊤)) = ρ ζ₀ := by rw [h]; rfl
    have h0 := congrArg (D r).ι.appTop
      (Polynomial.prod_erase_mul_sub_eq_zero ρ hζ₀ hn hu r.1 r.2)
    rw [map_mul, map_zero, (U.left.isUnit_ι_appTop_basicOpen (y r)).mul_right_eq_zero, map_sub,
      sub_eq_zero] at h0
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    refine (congrArg (fun z ↦ (D r).ι.appTop z ^ i) hρ).trans ?_
    dsimp only
    rw [← map_pow, ← map_pow, hi, h0]
  · have hspan : Ideal.span (Set.range y) = ⊤ := by
      rw [Ideal.eq_top_iff_one, ← Polynomial.sum_mul_prod_erase_sub_eq_one ρ hn u]
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

/-- **Local injectivity of `a ↦ ζ ^ a`.** If `ζ` comes from a primitive `n`-th root of unity
`ζ₀` of a field `k` over which `X` lives, then `ζ ^ a = ζ ^ b` on a nonempty `U` forces
`a = b`. -/
lemma isLocallyInjective_zmodToGmPresheaf [NeZero n] (f : X ⟶ Spec (.of k)) {ζ₀ : k}
    (hζ₀ : IsPrimitiveRoot ζ₀ n) (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1)
    (h : (ζ : Γ(X, ⊤)) = ((ΓSpecIso (.of k)).inv ≫ f.appTop) ζ₀) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (X.zmodToGmPresheaf n ζ hζ) where
  equalizerSieve_mem {U} a b hab := by
    by_cases hab' : a = b
    · subst hab'
      simp
    have : Subsingleton Γ(U.unop.left, ⊤) := by
      let ρ : k →+* Γ(U.unop.left, ⊤) :=
        ((ΓSpecIso (.of k)).inv ≫ f.appTop ≫ U.unop.hom.appTop).hom
      have hρ : U.unop.hom.appTop (ζ : Γ(X, ⊤)) = ρ ζ₀ := by rw [h]; rfl
      have e := congrArg (fun z : X.gmPresheaf.obj U ↦
        ((Additive.toMul z.down : Γ(U.unop.left, ⊤)ˣ) : Γ(U.unop.left, ⊤))) hab
      obtain ⟨i⟩ := a
      obtain ⟨j⟩ := b
      have hij : i.val ≠ j.val := fun hij ↦ hab' (congrArg ULift.up (ZMod.val_injective n hij))
      rw [← ZMod.natCast_zmod_val i, ← ZMod.natCast_zmod_val j, zmodToGmPresheaf_app_natCast,
        zmodToGmPresheaf_app_natCast, hρ] at e
      have e' : ρ (ζ₀ ^ i.val - ζ₀ ^ j.val) = 0 := by
        rw [map_sub, map_pow, map_pow]
        exact sub_eq_zero.2 e
      have hc : ζ₀ ^ i.val - ζ₀ ^ j.val ≠ 0 :=
        sub_ne_zero.2 fun hc ↦ hij (hζ₀.pow_inj (ZMod.val_lt i) (ZMod.val_lt j) hc)
      refine subsingleton_of_zero_eq_one ?_
      rw [← map_one ρ, ← mul_inv_cancel₀ hc, map_mul, e', zero_mul]
    have := Scheme.isEmpty_of_subsingleton_Γ this
    refine GrothendieckTopology.superset_covering _ ?_
      ((ofArrows_mem_smallEtaleTopology_iff (W := U.unop) (Z := PEmpty.elim)
        (fun i : PEmpty.{1} ↦ i.elim)).2 (Set.eq_univ_of_forall fun p ↦ isEmptyElim p))
    rintro _ _ ⟨_, _, _, ⟨i⟩, -⟩
    exact i.elim

/-- The forgetful functor from abelian groups to sets preserves sheaves on the small étale
site. -/
instance : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  inferInstance

/-- The inclusion `μₙ ⟶ 𝔾ₘ` is injective on sections. -/
lemma injective_kernelι_app (U : X.Etaleᵒᵖ) :
    Function.Injective ((kernel.ι (n • 𝟙 X.gmSheaf)).hom.app U) := by
  have : Mono ((sheafToPresheaf _ _).map (kernel.ι (n • 𝟙 X.gmSheaf))) := inferInstance
  have : Mono ((kernel.ι (n • 𝟙 X.gmSheaf)).hom.app U) :=
    inferInstanceAs (Mono (((sheafToPresheaf _ _).map (kernel.ι (n • 𝟙 X.gmSheaf))).app U))
  exact (AddCommGrpCat.mono_iff_injective _).1 this

/-- **`θ_ζ` is an isomorphism.** Let `X` be a scheme over a field `k`, `ζ₀ ∈ k` a primitive
`n`-th root of unity and `ζ` its image on `X`. Then `θ_ζ: ℤ/n ⟶ μₙ`, `a ↦ ζ ^ a`, is an
isomorphism of étale sheaves. -/
theorem isIso_constantZModToRootsOfUnitySheaf [NeZero n] (f : X ⟶ Spec (.of k)) {ζ₀ : k}
    (hζ₀ : IsPrimitiveRoot ζ₀ n) (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1)
    (h : (ζ : Γ(X, ⊤)) = ((ΓSpecIso (.of k)).inv ≫ f.appTop) ζ₀) :
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
  have := X.isLocallyInjective_zmodToGmPresheaf n f hζ₀ ζ hζ h
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
        rw [← nsmul_hom_app_apply, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
          ← InducedCategory.comp_hom, kernel.condition]
        rfl
      refine GrothendieckTopology.superset_covering _ ?_
        (X.imageSieve_zmodToGmPresheaf_mem n f hζ₀ ζ hζ h _ hx)
      rintro V g ⟨t, ht⟩
      refine ⟨t, X.injective_kernelι_app n _ ?_⟩
      calc ι.hom.app _ ((toSheafify _ _ ≫ θ.hom).app _ t)
          = ((toSheafify _ _ ≫ θ.hom) ≫ ι.hom).app _ t := rfl
        _ = (X.zmodToGmPresheaf n ζ hζ).app _ t := by rw [fac]; rfl
        _ = X.gmPresheaf.map g.op (ι.hom.app _ s) := ht
        _ = ι.hom.app _ ((X.rootsOfUnitySheaf n).obj.map g.op s) :=
          (NatTrans.naturality_apply ι.hom g.op s).symm
    exact Presheaf.isLocallySurjective_of_isLocallySurjective _ (toSheafify _ _) θ.hom

/-- **The canonical trivialization `θ_ζ: ℤ/n ≅ μₙ`.** Let `X` be a scheme over a field `k` and
let `ζ ∈ k` be a primitive `n`-th root of unity. Then `a ↦ ζ ^ a` is an isomorphism of étale
sheaves from the constant sheaf `ℤ/n` to the sheaf `μₙ` of `n`-th roots of unity. -/
noncomputable def constantZModIsoRootsOfUnitySheaf [NeZero n] (f : X ⟶ Spec (.of k)) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) : X.constantZMod n ≅ X.rootsOfUnitySheaf n :=
  have hu : IsUnit (((ΓSpecIso (.of k)).inv ≫ f.appTop) ζ) :=
    (hζ.isUnit (NeZero.ne n)).map _
  have hu' : hu.unit ^ n = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec,
    ← map_pow, hζ.pow_eq_one, map_one, Units.val_one])
  haveI := X.isIso_constantZModToRootsOfUnitySheaf n f hζ hu.unit hu' hu.unit_spec
  asIso (X.constantZModToRootsOfUnitySheaf n hu.unit hu')

end AlgebraicGeometry.Scheme

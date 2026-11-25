/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Estimate
public import WeilConjectures.AlgebraicGeometry.Curve.GmCohomology
public import WeilConjectures.AlgebraicGeometry.Curve.Jacobian
public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
public import WeilConjectures.AlgebraicGeometry.Curve.BaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnityPullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback

/-!
# The cohomology of `μₙ` on a smooth proper curve

Let `C` be a smooth proper connected curve of genus `g` over an algebraically closed field `k`
and `n ≥ 1` prime to `char k`. The long exact sequence of the Kummer sequence
`0 → μₙ → 𝔾ₘ → 𝔾ₘ → 0`, with `H¹(C, 𝔾ₘ) = Pic(C)` and `Hᵠ(C, 𝔾ₘ) = 0` for `q ≥ 2`, gives
canonical identifications

* `H⁰(C, μₙ) = μₙ(k)`,
* `H¹(C, μₙ) = Pic(C)[n] = J[n](k)`, of order `n^{2g}`,
* `H²(C, μₙ) = ℤ/n`, the Kummer boundary of a line bundle `L` going to `deg L mod n`,
* `Hᵠ(C, μₙ) = 0` for `q > 2`.

## Main statements

- `AlgebraicGeometry.IsConnectedCurve.sheafH_rootsOfUnitySheaf_of_isProper`: the computation.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open AlgebraicGeometry.Etale

namespace AlgebraicGeometry

namespace Scheme

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- An integer which is nonzero in a field `k` is invertible on every `k`-scheme. -/
lemma isUnit_natCast_of_ne_zero (f : C ⟶ Spec (.of k)) {n : ℕ} (hn : (n : k) ≠ 0) :
    IsUnit (n : Γ(C, ⊤)) := by
  simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- The sheaf `μₙ` of `n`-th roots of unity is killed by `n`, so it is a torsion sheaf. -/
lemma isTorsion_rootsOfUnitySheaf (X : Scheme.{u}) {n : ℕ} (hn : 0 < n) :
    (X.rootsOfUnitySheaf n).IsTorsion := by
  refine isTorsion_of_nsmul_id_eq_zero hn ((cancel_mono (kernel.ι (n • 𝟙 X.gmSheaf))).1 ?_)
  rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp,
    ← Category.comp_id (kernel.ι (n • 𝟙 X.gmSheaf)), ← Preadditive.comp_nsmul, kernel.condition]

/-- `H⁰` of `μₙ` injects into `H⁰` of `𝔾ₘ`, the global units. -/
lemma injective_map_rootsOfUnitySheafι_zero (X : Scheme.{u}) (n : ℕ) :
    Function.Injective (Sheaf.H.map (X.rootsOfUnitySheafι n) 0) := by
  intro x y h
  obtain ⟨a, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
  obtain ⟨b, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 y
  rw [Sheaf.H.map_apply, Sheaf.H.map_apply, Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.mk₀_comp_mk₀] at h
  rw [(cancel_mono (X.rootsOfUnitySheafι n)).1 ((Abelian.Ext.mk₀_bijective _ _).1 h)]

lemma gmSection_one (X : Scheme.{u}) : gmSection (1 : Γ(X, ⊤)ˣ) = 0 := by
  simp only [gmSection, map_one, ofMul_one]
  rfl

lemma gmSection_pow {X : Scheme.{u}} (a : Γ(X, ⊤)ˣ) (n : ℕ) :
    gmSection (a ^ n) = n • gmSection a := by
  simp only [gmSection, map_pow, ofMul_pow]
  rfl

/-- The section of `𝔾ₘ` over the terminal object of `X_ét` determines the unit. -/
lemma gmSection_injective (X : Scheme.{u}) : Function.Injective (gmSection (X := X)) := by
  have : IsIso (⊤_ X.Etale).hom := by
    let e : ⊤_ X.Etale ≅ _ := (terminalIsTerminal : IsTerminal (⊤_ X.Etale)).uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
    have h : e.hom.left ≫ 𝟙 X = (⊤_ X.Etale).hom := by simpa using e.hom.w
    have : IsIso e.hom.left :=
      (MorphismProperty.Over.forget _ _ X ⋙ CategoryTheory.Over.forget X).map_isIso e.hom
    exact ((Category.comp_id _).symm.trans h : e.hom.left = _) ▸ this
  intro a b hab
  have hab' := congrArg (fun x ↦ (Additive.toMul x.down : Γ((⊤_ X.Etale).left, ⊤)ˣ)) hab
  ext
  exact (ConcreteCategory.bijective_of_isIso (⊤_ X.Etale).hom.appTop).1 (congrArg Units.val hab')

/-- `H⁰(X, μₙ) ⟶ H⁰(X, 𝔾ₘ) = Γ(X, 𝒪)ˣ` has image the `n`-th roots of unity, for `n` invertible
on `X`: this is exactness of the Kummer sequence on global sections. -/
lemma exists_equiv₀_map_rootsOfUnitySheafι_zero_iff (X : Scheme.{u}) {n : ℕ}
    (hn : IsUnit (n : Γ(X, ⊤))) (a : Γ(X, ⊤)ˣ) :
    (∃ x, Sheaf.H.equiv₀ _ terminalIsTerminal (Sheaf.H.map (X.rootsOfUnitySheafι n) 0 x) =
      gmSection a) ↔ a ^ n = 1 := by
  have key (y : Sheaf.H X.gmSheaf 0) :
      y ∈ Set.range (Sheaf.H.map (X.rootsOfUnitySheafι n) 0) ↔ n • y = 0 := by
    rw [← sheafH_map_kummerSequence_g_apply]
    exact (Sheaf.H.exact_map_map (X.kummerSequence_shortExact n hn) 0 y).symm
  let E := Sheaf.H.equiv₀ X.gmSheaf terminalIsTerminal
  calc (∃ x, E (Sheaf.H.map (X.rootsOfUnitySheafι n) 0 x) = gmSection a)
      ↔ E.symm (gmSection a) ∈ Set.range (Sheaf.H.map (X.rootsOfUnitySheafι n) 0) := by
        simp only [Set.mem_range, ← E.eq_symm_apply]
    _ ↔ n • gmSection a = 0 := by
        rw [key, ← E.map_eq_zero_iff, map_nsmul, AddEquiv.apply_symm_apply]
    _ ↔ a ^ n = 1 := by
        rw [← gmSection_pow, ← gmSection_one, (gmSection_injective X).eq_iff]

end Scheme

namespace IsConnectedCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- Blueprint `proposition-smooth-proper-curves-torsion-prime`, parts 1–4: the canonical
identifications of the cohomology of `μₙ` on a smooth proper curve.

Let `C` be a smooth proper connected curve of genus `g` over an algebraically closed field `k`
and `n ≥ 1` prime to `char k`. Write `δ² : Pic(C) = H¹(C, 𝔾ₘ) → H²(C, μₙ)` for the Kummer
boundary (`AlgebraicGeometry.Scheme.kummerδ₁`). Then

1. `H⁰(C, μₙ) = μₙ(k)`: the map `H⁰(C, μₙ) → H⁰(C, 𝔾ₘ) = 𝒪(C)ˣ` is injective with image the
   units `a` with `aⁿ = 1`, which are `μₙ(k)` as `𝒪(C) = k`;
2. the map `H¹(C, μₙ) → H¹(C, 𝔾ₘ) = Pic(C)` is injective with image `Pic(C)[n]`, a group of
   order `n^{2g}`;
3. `δ²` is surjective, and there is a unique isomorphism `degₙ : H²(C, μₙ) ≅ ℤ/n` with
   `degₙ (δ² [L]) = deg L mod n` for every line bundle `L`;
4. `Hᵠ(C, μₙ) = 0` for `q > 2`.

The Kummer sequence is exact, `H¹(C, 𝔾ₘ) = Pic(C)` and `Hᵠ(C, 𝔾ₘ) = 0` for `q ≥ 2`
(`AlgebraicGeometry.IsCurve.sheafH_gmSheaf_of_smooth`); global units are `n`-divisible, so the
long exact sequence gives `H¹(C, μₙ) = Pic(C)[n]` and `H²(C, μₙ) = Pic(C)/n`. The degree
sequence `0 → Pic⁰(C) → Pic(C) → ℤ → 0` with `Pic⁰(C) = J(k)` `n`-divisible with `n`-torsion
`(ℤ/n)^{2g}` gives the rest. -/
theorem sheafH_rootsOfUnitySheaf_of_isProper (f : C ⟶ Spec (.of k)) [IsConnectedCurve f]
    [Smooth f] [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    (Function.Injective (Sheaf.H.map (C.rootsOfUnitySheafι n) 0) ∧
        ∀ a : Γ(C, ⊤)ˣ, (∃ x, Sheaf.H.equiv₀ _ terminalIsTerminal
          (Sheaf.H.map (C.rootsOfUnitySheafι n) 0 x) = Scheme.gmSection a) ↔ a ^ n = 1) ∧
      (Function.Injective (Sheaf.H.map (C.rootsOfUnitySheafι n) 1) ∧
        (Sheaf.H.map (C.rootsOfUnitySheafι n) 1).range =
          AddSubgroup.torsionBy C.CohomologicalPicardGroup n ∧
        Nat.card (Sheaf.H (C.rootsOfUnitySheaf n) 1) = n ^ (2 * f.genus)) ∧
      (Function.Surjective (C.kummerδ₁ n (Scheme.isUnit_natCast_of_ne_zero f hn)) ∧
        ∃! d : Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+ ZMod n, ∀ L : C.Pic,
          d (C.kummerδ₁ n (Scheme.isUnit_natCast_of_ne_zero f hn)
            (Scheme.Pic.toCohomologicalPicardGroup C L)) = (f.picDegree L : ZMod n)) ∧
      ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H (C.rootsOfUnitySheaf n) q) := by
  have := IsConnectedCurve.connectedSpace (f := f)
  have hn' := Scheme.isUnit_natCast_of_ne_zero f hn
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
  have : NeZero n := ⟨hn0.ne'⟩
  have : NeZero (n : k) := ⟨hn⟩
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    IsConnectedCurve.smoothOfRelativeDimension_one f
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  refine ⟨⟨C.injective_map_rootsOfUnitySheafι_zero n, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact C.exists_equiv₀_map_rootsOfUnitySheafι_zero_iff hn'
  · -- the global units are `n`-divisible, so the Kummer map on them vanishes
    obtain ⟨hα, hαβ, -⟩ := C.exact_sheafH_rootsOfUnitySheaf_one n hn'
    let := (Scheme.globalSectionsRingHom k (X := C)).toAlgebra
    have : Module.Finite k Γ(C, ⊤) := Scheme.finite_globalSectionsRingHom_of_isProper
    have hdiv := IsAlgClosed.exists_pow_eq_of_finite (A := Γ(C, ⊤)) hn
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨u, rfl⟩ := (hαβ x).1 hx
    obtain ⟨v, hv⟩ := hdiv (Additive.toMul u)
    have hu : u ∈ (C.kummerδ₀ n hn').ker := by
      rw [hα]
      exact ⟨Additive.ofMul v, by simp [← ofMul_pow, hv]⟩
    exact hu
  · exact (C.exact_sheafH_rootsOfUnitySheaf_one n hn').2.2
  · -- `H¹(C, μₙ) ≅ H¹(C, ℤ/n) ≅ (ℤ/n)^{2g}`
    obtain ⟨e₁⟩ := Scheme.nonempty_addEquiv_sheafH_constantZMod_rootsOfUnitySheaf f n hn 1
    obtain ⟨e₂⟩ := IsCurve.nonempty_addEquiv_sheafH_constantZMod_one f n hn
    rw [Nat.card_congr (e₁.symm.trans e₂).toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  · -- `δ²` is surjective since `Br(C) = 0`
    obtain ⟨hker, hαβ, -⟩ := C.exact_sheafH_rootsOfUnitySheaf_two n hn'
    have := IsCurve.subsingleton_cohomologicalBrauerGroup_of_smooth f
    have hsurj : Function.Surjective (C.kummerδ₁ n hn') :=
      fun y ↦ (hαβ y).1 (Subsingleton.elim _ _)
    refine ⟨hsurj, ?_⟩
    -- the degree modulo `n` on `H¹(C, 𝔾ₘ) = Pic(C)`
    let eP := Scheme.Pic.toCohomologicalPicardGroupAddEquiv C
    let D : C.CohomologicalPicardGroup →+ ZMod n :=
      { toFun := fun c ↦ ((Scheme.picDegreeHom k C (eP.symm c).toMul).toAdd : ZMod n)
        map_zero' := by simp
        map_add' := fun a b ↦ by simp [Int.cast_add] }
    have hD (L : C.Pic) :
        D (Scheme.Pic.toCohomologicalPicardGroup C L) = (f.picDegree L : ZMod n) := by
      have : eP.symm (Scheme.Pic.toCohomologicalPicardGroup C L) = .ofMul L :=
        eP.symm_apply_eq.2 rfl
      simp only [D, AddMonoidHom.coe_mk, ZeroHom.coe_mk, this, toMul_ofMul]
      rfl
    obtain ⟨-, -, hdiv⟩ := Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient (C := C) hn
    have : Nonempty C := IsConnectedCurve.nonempty f
    obtain ⟨L₁, hL₁⟩ := Scheme.surjective_picDegreeHom (k := k) (C := C) (Multiplicative.ofAdd 1)
    have hdegL₁ : (Scheme.picDegreeHom k C L₁).toAdd = 1 := by rw [hL₁]; rfl
    have hDe (x : Additive C.Pic) :
        D (eP x) = ((Scheme.picDegreeHom k C x.toMul).toAdd : ZMod n) := by
      simp [D]
    have hDker : D.ker = (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (n : ℤ)).range := by
      ext c
      obtain ⟨x, rfl⟩ := eP.surjective c
      rw [AddMonoidHom.mem_ker, hDe, ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [AddMonoidHom.mem_range, zsmulAddGroupHom_apply]
      constructor
      · rintro ⟨m, hm⟩
        have hy : x.toMul * L₁ ^ (-((n : ℤ) * m)) ∈ picardZero k C := by
          rw [MonoidHom.mem_ker, map_mul, map_zpow]
          apply Multiplicative.toAdd.injective
          rw [toAdd_mul, toAdd_zpow, hm, hdegL₁]
          simp
        obtain ⟨z, hz⟩ := hdiv ⟨_, hy⟩
        have hz' : (z : C.Pic) ^ n = x.toMul * L₁ ^ (-((n : ℤ) * m)) :=
          congrArg Subtype.val hz
        refine ⟨eP (.ofMul ((z : C.Pic) * L₁ ^ m)), ?_⟩
        rw [← map_zsmul]
        congr 1
        apply Additive.toMul.injective
        rw [toMul_zsmul, toMul_ofMul, mul_zpow, zpow_natCast, hz', ← zpow_mul, mul_assoc,
          ← zpow_add, mul_comm (m : ℤ), neg_add_cancel, zpow_zero, mul_one]
      · rintro ⟨c, hc⟩
        obtain ⟨y, rfl⟩ := eP.surjective c
        rw [← map_zsmul] at hc
        rw [← eP.injective hc, toMul_zsmul, map_zpow, toAdd_zpow]
        exact ⟨_, zsmul_eq_mul _ _⟩
    have hDsurj : Function.Surjective D := by
      intro a
      refine ⟨eP (.ofMul (L₁ ^ (a.val : ℤ))), ?_⟩
      rw [hDe, toMul_ofMul, map_zpow, toAdd_zpow, hdegL₁, smul_eq_mul, mul_one, Int.cast_natCast,
        ZMod.natCast_zmod_val]
    let eα := QuotientAddGroup.quotientKerEquivOfSurjective _ hsurj
    let eD := QuotientAddGroup.quotientKerEquivOfSurjective D hDsurj
    let d : Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+ ZMod n :=
      eα.symm.trans ((QuotientAddGroup.quotientAddEquivOfEq (hker.trans hDker.symm)).trans eD)
    have hd (c : C.CohomologicalPicardGroup) : d (C.kummerδ₁ n hn' c) = D c := by
      simp only [d, AddEquiv.trans_apply]
      rw [show eα.symm (C.kummerδ₁ n hn' c) = (c : _ ⧸ _) from eα.symm_apply_eq.2 rfl]
      rfl
    refine ⟨d, fun L ↦ (hd _).trans (hD L), fun d' hd' ↦ ?_⟩
    ext y
    obtain ⟨c, rfl⟩ := hsurj y
    obtain ⟨L, rfl⟩ := (Scheme.Pic.toCohomologicalPicardGroup C).surjective c
    rw [hd', hd, hD]
  · intro q hq
    exact IsCurve.subsingleton_sheafH_of_three_le f _ (C.isTorsion_rootsOfUnitySheaf hn0) q hq

/-- Blueprint `proposition-smooth-proper-curves-torsion-prime`, part 5: invariance under extension
of algebraically closed fields.

Let `C` be a smooth proper connected curve over an algebraically closed field `k`, let
`k ⊆ k'` be an extension of algebraically closed fields, `π : C_{k'} ⟶ C` the projection and
`n ≥ 1` prime to `char k`. Then the pullback maps `ρᵠ : Hᵠ(C, μₙ) ⟶ Hᵠ(C_{k'}, μₙ)`
(`AlgebraicGeometry.Scheme.rootsOfUnityCohomologyMap`) are bijective, and under the
identifications of `AlgebraicGeometry.IsConnectedCurve.sheafH_rootsOfUnitySheaf_of_isProper`

* `ρ⁰` is the inclusion `μₙ(k) ⟶ μₙ(k')`: on the global units it is the pullback of units
  along `π`;
* `ρ¹` is the restriction of the base change map `π^* : Pic(C) ⟶ Pic(C_{k'})` to `n`-torsion,
  which on `Pic⁰(C) = J(k)` is the base change map `J[n](k) ⟶ J[n](k')`;
* `ρ²` is the identity of `ℤ/n`: `degₙ' ∘ ρ² = degₙ` for the isomorphisms `degₙ` and `degₙ'`
  characterised by `degₙ (δ² [L]) = deg L mod n`.

The pullback commutes with the Kummer sequences, hence with all maps of their long exact
sequences (`AlgebraicGeometry.Scheme.map_kernelι_rootsOfUnityCohomologyMap`,
`AlgebraicGeometry.Scheme.rootsOfUnityCohomologyMap_kummerδ₁`), the identification
`Pic = H¹(-, 𝔾ₘ)` is natural (`AlgebraicGeometry.Scheme.gmCohomologyMap_toCohomologicalPicardGroup`)
and pullback preserves degrees (`AlgebraicGeometry.Scheme.Hom.picDegree_map_baseChangeField`).
Bijectivity follows from the comparison `π^* μₙ ≅ μₙ` and the invariance of the cohomology of
`ℤ/n ≅ μₙ` (`AlgebraicGeometry.IsConnectedCurve.bijective_fieldExtensionCohomologyMap_of_isProper`).
-/
theorem rootsOfUnityCohomologyMap_baseChangeField (f : C ⟶ Spec (.of k)) [IsConnectedCurve f]
    [Smooth f] [IsProper f] (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k'] (n : ℕ)
    (hn : (n : k) ≠ 0) :
    (∀ q, Function.Bijective (Scheme.rootsOfUnityCohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) n q)) ∧
    (∀ (x : Sheaf.H (C.rootsOfUnitySheaf n) 0) (a : Γ(C, ⊤)ˣ),
      Sheaf.H.equiv₀ _ terminalIsTerminal (Sheaf.H.map (C.rootsOfUnitySheafι n) 0 x) =
        Scheme.gmSection a →
      Sheaf.H.equiv₀ _ terminalIsTerminal
          (Sheaf.H.map (Scheme.rootsOfUnitySheafι _ n) 0 (Scheme.rootsOfUnityCohomologyMap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) n 0 x)) =
        Scheme.gmSection (Units.map (pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop.hom.toMonoidHom a)) ∧
    (∀ (x : Sheaf.H (C.rootsOfUnitySheaf n) 1) (L : C.Pic),
      Sheaf.H.map (C.rootsOfUnitySheafι n) 1 x = Scheme.Pic.toCohomologicalPicardGroup C L →
      Sheaf.H.map (Scheme.rootsOfUnitySheafι _ n) 1 (Scheme.rootsOfUnityCohomologyMap
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) n 1 x) =
        Scheme.Pic.toCohomologicalPicardGroup _ (Scheme.Pic.map
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) L)) ∧
    ∀ (hC : IsUnit (n : Γ(C, ⊤)))
      (hC' : IsUnit (n : Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)))
      (d : Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+ ZMod n)
      (d' : Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).rootsOfUnitySheaf
        n) 2 ≃+ ZMod n),
      (∀ L : C.Pic, d (C.kummerδ₁ n hC (Scheme.Pic.toCohomologicalPicardGroup C L)) =
        (f.picDegree L : ZMod n)) →
      (∀ L, d' (Scheme.kummerδ₁ _ n hC' (Scheme.Pic.toCohomologicalPicardGroup _ L)) =
        ((f.baseChangeField k').picDegree L : ZMod n)) →
      ∀ y, d' (Scheme.rootsOfUnityCohomologyMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) n 2 y) = d y := by
  set π := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  have hn0 : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  have hnC := Scheme.isUnit_natCast_of_ne_zero f hn
  refine ⟨fun q ↦ ?_, fun x a hx ↦ ?_, fun x L hx ↦ ?_, fun hC hC' d d' hd hd' y ↦ ?_⟩
  · -- `π^* μₙ ≅ μₙ`, and the cohomology of `μₙ ≅ ℤ/n` is invariant
    have : IsIso (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf n π) :=
      Scheme.isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit n π hnC
    have : NeZero (n : k) := ⟨hn⟩
    obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k n
    let θ := C.constantZModIsoRootsOfUnitySheaf n f hζ
    have hZ := IsConnectedCurve.bijective_fieldExtensionCohomologyMap_of_isProper f k' n hn q
    have hμ : Function.Bijective (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) q) := by
      have h : ⇑(Etale.cohomologyMap π (C.rootsOfUnitySheaf n) q) =
          Sheaf.H.map ((Etale.upperStar AddCommGrpCat.{u + 1} π).map θ.hom) q ∘
            Etale.cohomologyMap π (C.constantZMod n) q ∘ Sheaf.H.map θ.inv q := by
        ext z
        simp only [Function.comp_apply]
        rw [← Etale.cohomologyMap_map, ← Sheaf.H.map_comp_apply, Iso.inv_hom_id,
          Sheaf.H.map_id_apply]
      rw [h]
      exact (Sheaf.H.bijective_map_of_isIso _ q).comp
        (hZ.comp (Sheaf.H.bijective_map_of_isIso _ q))
    exact (Sheaf.H.bijective_map_of_isIso _ q).comp hμ
  · rw [Scheme.map_kernelι_rootsOfUnityCohomologyMap, Scheme.equiv₀_gmCohomologyMap_zero, hx,
      Scheme.gmSectionsPullback_gmSection]
  · rw [Scheme.map_kernelι_rootsOfUnityCohomologyMap, hx,
      Scheme.gmCohomologyMap_toCohomologicalPicardGroup]
  · obtain ⟨-, -, ⟨hsurj, -⟩, -⟩ := sheafH_rootsOfUnitySheaf_of_isProper f n hn
    obtain ⟨c, rfl⟩ := hsurj y
    obtain ⟨L, rfl⟩ := (Scheme.Pic.toCohomologicalPicardGroup C).surjective c
    rw [Scheme.rootsOfUnityCohomologyMap_kummerδ₁ π n _ hC',
      Scheme.gmCohomologyMap_toCohomologicalPicardGroup, hd', hd,
      Scheme.Hom.picDegree_map_baseChangeField]

/-- The canonical identification `Pic = H¹(-, 𝔾ₘ)` is compatible with powers. -/
lemma _root_.AlgebraicGeometry.Scheme.Pic.toCohomologicalPicardGroup_pow (X : Scheme.{u})
    (L : X.Pic) (n : ℕ) :
    Scheme.Pic.toCohomologicalPicardGroup X (L ^ n) =
      n • Scheme.Pic.toCohomologicalPicardGroup X L :=
  map_nsmul (Scheme.Pic.toCohomologicalPicardGroupAddEquiv X) n (Additive.ofMul L)

open MonoidalCategory MonObj in
/-- Blueprint `proposition-smooth-proper-curves-torsion-prime`, the identification
`H¹(C, μₙ) = J[n](k)`.

Let `C` be a smooth proper connected curve of genus `g` over an algebraically closed field `k`
and `n ≥ 1` prime to `char k`. The Jacobian `J` of `C` is an abelian variety of dimension `g`
whose group of `k`-points is `Pic⁰(C)` (`AlgebraicGeometry.Scheme.exists_jacobian_addEquiv_prod`).
The injection `H¹(C, μₙ) ⟶ H¹(C, 𝔾ₘ) = Pic(C)` of the Kummer sequence has image `Pic(C)[n]`
(`AlgebraicGeometry.IsConnectedCurve.sheafH_rootsOfUnitySheaf_of_isProper`), which lies in
`Pic⁰(C)` since `ℤ` is torsion-free; hence `H¹(C, μₙ) ≅ J[n](k)`, compatibly with the maps to
`Pic(C)`. -/
theorem exists_addEquiv_sheafH_rootsOfUnitySheaf_one_jacobian (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    letI : C.Over (Spec (.of k)) := ⟨f⟩
    letI : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
      IsConnectedCurve.smoothOfRelativeDimension_one f
    haveI : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
    ∃ (J : Over (Spec (.of k))) (_ : CommGrpObj J) (_ : IsAbelianVariety J)
      (ψ : picardZero k C ≃* (𝟙_ (Over (Spec (.of k))) ⟶ J)),
      IsAbelianVariety.dim J = f.genus ∧
      ∃ E : Sheaf.H (C.rootsOfUnitySheaf n) 1 ≃+
          AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)) n,
        ∀ x, Sheaf.H.map (C.rootsOfUnitySheafι n) 1 x =
          Scheme.Pic.toCohomologicalPicardGroup C
            (ψ.symm (Additive.toMul (E x : Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)))) := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have := IsConnectedCurve.connectedSpace (f := f)
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    IsConnectedCurve.smoothOfRelativeDimension_one f
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  obtain ⟨J, _, -, _, -, hdim, ⟨ψ⟩, -⟩ := Scheme.exists_jacobian_addEquiv_prod k C
  obtain ⟨-, ⟨hinj, hrange, -⟩, -⟩ := sheafH_rootsOfUnitySheaf_of_isProper f n hn
  let e := Scheme.Pic.toCohomologicalPicardGroup C
  let incl := Sheaf.H.map (C.rootsOfUnitySheafι n) 1
  -- the class in `Pic(C)` of the image of `x`
  let P (x : Sheaf.H (C.rootsOfUnitySheaf n) 1) : C.Pic := e.symm (incl x)
  have hP (x) : e (P x) = incl x := e.apply_symm_apply _
  have hPadd (x y) : P (x + y) = P x * P y := by
    apply e.injective
    rw [Scheme.Pic.toCohomologicalPicardGroup_mul, hP, hP, hP, map_add]
  have htors {L : C.Pic} : e L ∈ AddSubgroup.torsionBy C.CohomologicalPicardGroup n ↔
      L ^ n = 1 := by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← Scheme.Pic.toCohomologicalPicardGroup_pow,
      ← (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C).map_zero]
    exact e.injective.eq_iff.trans ⟨fun h ↦ h, fun h ↦ h⟩
  have hPn (x) : P x ^ n = 1 := htors.1 (hP x ▸ hrange ▸ ⟨x, rfl⟩)
  have hdeg {L : C.Pic} (hL : L ^ n = 1) : L ∈ picardZero k C := by
    rw [MonoidHom.mem_ker]
    have h := congrArg (Scheme.picDegreeHom k C) hL
    rw [map_pow, map_one] at h
    apply Multiplicative.toAdd.injective
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_pow, toAdd_one, smul_eq_zero] at h'
    exact h'.resolve_left hn0
  -- the map `H¹(C, μₙ) ⟶ J[n](k)`
  let h : Sheaf.H (C.rootsOfUnitySheaf n) 1 →+
      AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)) n :=
    { toFun x := ⟨Additive.ofMul (ψ ⟨P x, hdeg (hPn x)⟩), by
        rw [AddSubgroup.torsionBy.nsmul_iff, ← ofMul_pow, ← map_pow]
        have : (⟨P x, hdeg (hPn x)⟩ : picardZero k C) ^ n = 1 :=
          Subtype.ext (hPn x)
        rw [this, map_one, ofMul_one]⟩
      map_zero' := by
        apply Subtype.ext
        change Additive.ofMul (ψ ⟨P 0, _⟩) = 0
        have : (⟨P 0, hdeg (hPn 0)⟩ : picardZero k C) = 1 := by
          apply Subtype.ext
          apply e.injective
          rw [hP, map_zero]
          exact ((Scheme.Pic.toCohomologicalPicardGroupAddEquiv C).map_zero).symm
        rw [this, map_one, ofMul_one]
      map_add' x y := by
        apply Subtype.ext
        change Additive.ofMul (ψ ⟨P (x + y), _⟩) =
          Additive.ofMul (ψ ⟨P x, _⟩) + Additive.ofMul (ψ ⟨P y, _⟩)
        have : (⟨P (x + y), hdeg (hPn (x + y))⟩ : picardZero k C) =
            ⟨P x, hdeg (hPn x)⟩ * ⟨P y, hdeg (hPn y)⟩ :=
          Subtype.ext (hPadd x y)
        rw [this, map_mul, ofMul_mul] }
  have hbij : Function.Bijective h := by
    refine ⟨fun x y hxy ↦ hinj ?_, fun t ↦ ?_⟩
    · have h1 := congrArg
        (fun z : AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)) n ↦
          Additive.toMul (z : Additive (𝟙_ (Over (Spec (.of k))) ⟶ J))) hxy
      have h2 := congrArg Subtype.val (ψ.injective h1)
      rw [← hP x, ← hP y]
      exact congrArg e h2
    · let L := ψ.symm (Additive.toMul (t : Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)))
      have hLn : (L : C.Pic) ^ n = 1 := by
        have ht := AddSubgroup.torsionBy.nsmul t
        have := congrArg
          (fun z : AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)) n ↦
            ψ.symm (Additive.toMul (z : Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)))) ht
        simp only [AddSubgroup.coe_nsmul, toMul_nsmul, map_pow, ZeroMemClass.coe_zero,
          toMul_zero, map_one] at this
        exact congrArg Subtype.val this
      obtain ⟨x, hx⟩ : e (L : C.Pic) ∈ incl.range := hrange ▸ htors.2 hLn
      refine ⟨x, Subtype.ext ?_⟩
      have hPx : P x = L := e.injective ((hP x).trans hx)
      change Additive.ofMul (ψ ⟨P x, _⟩) = _
      have : (⟨P x, hdeg (hPn x)⟩ : picardZero k C) = L := Subtype.ext hPx
      rw [this, MulEquiv.apply_symm_apply]
      rfl
  refine ⟨J, inferInstance, inferInstance, ψ, hdim, AddEquiv.ofBijective h hbij, fun x ↦ ?_⟩
  change incl x = e (ψ.symm (ψ ⟨P x, hdeg (hPn x)⟩))
  rw [MulEquiv.symm_apply_apply]
  exact (hP x).symm


open MonoidalCategory MonObj in
/-- Blueprint `proposition-smooth-proper-curves-torsion-prime`: smooth proper curves with invertible
torsion.

Let `C` be a smooth, proper and connected curve of genus `g` over an algebraically closed field
`k`, let `n ≥ 1` be invertible in `k` and let `J` be the Jacobian of `C`. There are canonical
identifications

`H⁰(C, μₙ) = μₙ(k)`, `H¹(C, μₙ) = J[n](k)`, `H²(C, μₙ) = ℤ/n`, `Hᵠ(C, μₙ) = 0` for `q > 2`.

The degree-two isomorphism sends the Kummer boundary of a line bundle `L` to `deg L mod n`, and
these identifications commute with extension of algebraically closed fields. Precisely:

1. parts 1–4 of blueprint `proposition-smooth-proper-curves-torsion-prime`
   (`AlgebraicGeometry.IsConnectedCurve.sheafH_rootsOfUnitySheaf_of_isProper`): the maps
   `H⁰(C, μₙ) → 𝒪(C)ˣ` and `H¹(C, μₙ) → Pic(C)` of the Kummer sequence are injective, the
   first with image `μₙ(k)` and the second with image `Pic(C)[n]`, of order `n^{2g}`; the
   Kummer boundary `δ²` is surjective and there is a unique `degₙ : H²(C, μₙ) ≃ ℤ/n` with
   `degₙ (δ² [L]) = deg L mod n`; and `Hᵠ(C, μₙ) = 0` for `q > 2`;
2. `H¹(C, μₙ) ≅ J[n](k)` compatibly with `Pic⁰(C) = J(k)`
   (`AlgebraicGeometry.IsConnectedCurve.exists_addEquiv_sheafH_rootsOfUnitySheaf_one_jacobian`);
3. part 5 of blueprint `proposition-smooth-proper-curves-torsion-prime`
   (`AlgebraicGeometry.IsConnectedCurve.rootsOfUnityCohomologyMap_baseChangeField`): for every
   extension `k ⊆ k'` of algebraically closed fields the pullback maps are bijective and are the
   inclusion `μₙ(k) ⟶ μₙ(k')`, the base change of line bundles and the identity of `ℤ/n`.

These are statements about the small étale site; the comparison with the pro-étale site
(blueprint `theorem-bounded-below-cohomology-comparison`) identifies them with the pro-étale
cohomology of `ν^* μₙ`. (In the split chapter of the sketch blueprint this statement is labelled
`proposition-smooth-proper-curves-torsion-prime`, blueprint
`sk-the-final-theorem-the-curve-estimate--remark-2`.) -/
theorem sheafH_rootsOfUnitySheaf_canonical_of_isProper (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    ((Function.Injective (Sheaf.H.map (C.rootsOfUnitySheafι n) 0) ∧
        ∀ a : Γ(C, ⊤)ˣ, (∃ x, Sheaf.H.equiv₀ _ terminalIsTerminal
          (Sheaf.H.map (C.rootsOfUnitySheafι n) 0 x) = Scheme.gmSection a) ↔ a ^ n = 1) ∧
      (Function.Injective (Sheaf.H.map (C.rootsOfUnitySheafι n) 1) ∧
        (Sheaf.H.map (C.rootsOfUnitySheafι n) 1).range =
          AddSubgroup.torsionBy C.CohomologicalPicardGroup n ∧
        Nat.card (Sheaf.H (C.rootsOfUnitySheaf n) 1) = n ^ (2 * f.genus)) ∧
      (Function.Surjective (C.kummerδ₁ n (Scheme.isUnit_natCast_of_ne_zero f hn)) ∧
        ∃! d : Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+ ZMod n, ∀ L : C.Pic,
          d (C.kummerδ₁ n (Scheme.isUnit_natCast_of_ne_zero f hn)
            (Scheme.Pic.toCohomologicalPicardGroup C L)) = (f.picDegree L : ZMod n)) ∧
      ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H (C.rootsOfUnitySheaf n) q)) ∧
    (letI : C.Over (Spec (.of k)) := ⟨f⟩
     letI : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
       IsConnectedCurve.smoothOfRelativeDimension_one f
     haveI : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
     ∃ (J : Over (Spec (.of k))) (_ : CommGrpObj J) (_ : IsAbelianVariety J)
       (ψ : picardZero k C ≃* (𝟙_ (Over (Spec (.of k))) ⟶ J)),
       IsAbelianVariety.dim J = f.genus ∧
       ∃ E : Sheaf.H (C.rootsOfUnitySheaf n) 1 ≃+
           AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)) n,
         ∀ x, Sheaf.H.map (C.rootsOfUnitySheafι n) 1 x =
           Scheme.Pic.toCohomologicalPicardGroup C
             (ψ.symm (Additive.toMul (E x : Additive (𝟙_ (Over (Spec (.of k))) ⟶ J))))) ∧
    ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k'],
      (∀ q, Function.Bijective (Scheme.rootsOfUnityCohomologyMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) n q)) ∧
      (∀ (x : Sheaf.H (C.rootsOfUnitySheaf n) 0) (a : Γ(C, ⊤)ˣ),
        Sheaf.H.equiv₀ _ terminalIsTerminal (Sheaf.H.map (C.rootsOfUnitySheafι n) 0 x) =
          Scheme.gmSection a →
        Sheaf.H.equiv₀ _ terminalIsTerminal
            (Sheaf.H.map (Scheme.rootsOfUnitySheafι _ n) 0 (Scheme.rootsOfUnityCohomologyMap
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) n 0 x)) =
          Scheme.gmSection (Units.map (pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop.hom.toMonoidHom a)) ∧
      (∀ (x : Sheaf.H (C.rootsOfUnitySheaf n) 1) (L : C.Pic),
        Sheaf.H.map (C.rootsOfUnitySheafι n) 1 x = Scheme.Pic.toCohomologicalPicardGroup C L →
        Sheaf.H.map (Scheme.rootsOfUnitySheafι _ n) 1 (Scheme.rootsOfUnityCohomologyMap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) n 1 x) =
          Scheme.Pic.toCohomologicalPicardGroup _ (Scheme.Pic.map
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) L)) ∧
      ∀ (hC : IsUnit (n : Γ(C, ⊤)))
        (hC' : IsUnit (n : Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)))
        (d : Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+ ZMod n)
        (d' : Sheaf.H
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).rootsOfUnitySheaf n) 2 ≃+
            ZMod n),
        (∀ L : C.Pic, d (C.kummerδ₁ n hC (Scheme.Pic.toCohomologicalPicardGroup C L)) =
          (f.picDegree L : ZMod n)) →
        (∀ L, d' (Scheme.kummerδ₁ _ n hC' (Scheme.Pic.toCohomologicalPicardGroup _ L)) =
          ((f.baseChangeField k').picDegree L : ZMod n)) →
        ∀ y, d' (Scheme.rootsOfUnityCohomologyMap
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) n 2 y) = d y :=
  ⟨sheafH_rootsOfUnitySheaf_of_isProper f n hn,
    exists_addEquiv_sheafH_rootsOfUnitySheaf_one_jacobian f n hn,
    fun k' _ _ _ ↦ rootsOfUnityCohomologyMap_baseChangeField f k' n hn⟩

end IsConnectedCurve

end AlgebraicGeometry

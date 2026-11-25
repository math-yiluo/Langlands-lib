/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# The Kummer sequence

For a scheme `X` and `n ≥ 1` the *Kummer sequence* is the sequence of étale sheaves

```
  0 ──▶ μₙ ──kernel.ι──▶ 𝔾ₘ ──n • 𝟙──▶ 𝔾ₘ ──▶ 0
```

whose right hand map is the `n`-th power map (written additively as `n • 𝟙`) and whose sheaf
`μₙ` of `n`-th roots of unity is by definition its kernel. It is exact as soon as `n` is
invertible on `X`: for a unit `t` on `U`, the scheme `U ×_{Spec Γ(U, 𝒪)} Spec Γ(U, 𝒪)[T]/(Tⁿ - t)`
is a surjective étale cover of `U` on which `t` has an `n`-th root. Its long exact
cohomology sequence

```
  Γ(X, 𝒪)ˣ ──(·)ⁿ──▶ Γ(X, 𝒪)ˣ ──▶ H¹(X, μₙ) ──▶ H¹(X, 𝔾ₘ) ──n·──▶ H¹(X, 𝔾ₘ)
           ──▶ H²(X, μₙ) ──▶ H²(X, 𝔾ₘ) ──n·──▶ H²(X, 𝔾ₘ)
```

computes `H¹` and `H²` of `μₙ` in terms of the Picard and Brauer groups of `X`. The group of
units `Γ(X, 𝒪)ˣ` is written additively, as `Additive Γ(X, ⊤)ˣ`, so that its `n`-th power map
is `n • ·`.

This file also defines the constant étale sheaf `ℤ/n`, which is `μₙ` after the choice of a
primitive `n`-th root of unity.

## Main definitions

- `AlgebraicGeometry.Scheme.rootsOfUnitySheaf`: the sheaf `μₙ` of `n`-th roots of unity.
- `AlgebraicGeometry.Scheme.kummerSequence`: the Kummer sequence, as a short complex.
- `AlgebraicGeometry.Scheme.kummerδ₀` and `AlgebraicGeometry.Scheme.kummerδ₁`: the connecting
  homomorphisms `Γ(X, 𝒪)ˣ → H¹(X, μₙ)` and `H¹(X, 𝔾ₘ) → H²(X, μₙ)` of its long exact sequence.
- `AlgebraicGeometry.Scheme.constantZMod`: the constant étale sheaf `ℤ/n`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_etale_surjective_pow_eq_appTop`: a unit on a scheme on which
  `n` is invertible has an `n`-th root on a surjective étale cover.
- `AlgebraicGeometry.Scheme.isLocallySurjective_nsmul_gmSheaf`: the `n`-th power map on `𝔾ₘ` is
  locally surjective for the étale topology.
- `AlgebraicGeometry.Scheme.kummerSequence_shortExact`: the Kummer sequence is short exact
  when `n` is invertible on `X`.
- `AlgebraicGeometry.Scheme.exact_sheafH_rootsOfUnitySheaf_one`: the short exact
  sequence `0 → Γ(X, 𝒪)ˣ/n → H¹(X, μₙ) → H¹(X, 𝔾ₘ)[n] → 0`, whose maps are the connecting
  homomorphism `AlgebraicGeometry.Scheme.kummerδ₀` and the map induced by `μₙ ⟶ 𝔾ₘ`.
- `AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one`:
  `H¹(X, μₙ) ≅ H¹(X, 𝔾ₘ)[n]` when every unit on `X` is an `n`-th power.
- `AlgebraicGeometry.Scheme.exact_sheafH_rootsOfUnitySheaf_two`: the short exact
  sequence `0 → H¹(X, 𝔾ₘ)/n → H²(X, μₙ) → H²(X, 𝔾ₘ)[n] → 0`, whose maps are the connecting
  homomorphism `AlgebraicGeometry.Scheme.kummerδ₁` and the map induced by `μₙ ⟶ 𝔾ₘ`.
- `AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_zero_constantZMod`:
  `H⁰(X, ℤ/n) ≅ ℤ/n` for a connected scheme `X`.

## Implementation details

Some auxiliary lemmas take the terminal object of `X.Etale` as a variable, since `rw` fails on
terms mentioning the canonical one.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry.Scheme

/-- An element `t` of `Γ(U, ⊤)` whose image under `φ : Γ(U, ⊤) ⟶ R` is an `n`-th power has an
`n`-th root on the base change of `Spec R ⟶ Spec Γ(U, ⊤)` along `U ⟶ Spec Γ(U, ⊤)`. -/
private lemma exists_pow_eq_pullback_fst_toSpecΓ_appTop {U : Scheme.{u}} {R : CommRingCat.{u}}
    (φ : Γ(U, ⊤) ⟶ R) {n : ℕ} {t : Γ(U, ⊤)} {r : R} (h : φ t = r ^ n) :
    ∃ ω : Γ(pullback U.toSpecΓ (Spec.map φ), ⊤),
      ω ^ n = (pullback.fst U.toSpecΓ (Spec.map φ)).appTop t := by
  refine ⟨(pullback.snd U.toSpecΓ (Spec.map φ)).appTop ((ΓSpecIso R).inv r), ?_⟩
  rw [pullback_fst_toSpecΓ_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply, h, map_pow,
    map_pow]

/-- **Kummer covers.** Let `U` be a scheme, `n ≠ 0` invertible on `U` and `t` a unit on `U`.
Then `t` has an `n`-th root on a surjective étale cover of `U`: there is an étale surjective
`f: V ⟶ U` and `ω ∈ Γ(V, 𝒪_V)` with `ωⁿ = f^* t`. -/
theorem exists_etale_surjective_pow_eq_appTop {U : Scheme.{u}} {n : ℕ} (hn₀ : n ≠ 0)
    (hn : IsUnit (n : Γ(U, ⊤))) {t : Γ(U, ⊤)} (ht : IsUnit t) :
    ∃ (V : Scheme.{u}) (f : V ⟶ U), Etale f ∧ Surjective f ∧
      ∃ ω : Γ(V, ⊤), ω ^ n = f.appTop t := by
  let φ : Γ(U, ⊤) ⟶ CommRingCat.of (AdjoinRoot (X ^ n - C t)) :=
    CommRingCat.ofHom (algebraMap _ _)
  have : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr (AdjoinRoot.etale_X_pow_sub_C hn₀ hn ht)
  have hdeg : (X ^ n - C t).degree ≠ 0 := by
    nontriviality Γ(U, ⊤)
    rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hn₀)]
    exact_mod_cast hn₀
  have : Surjective (Spec.map φ) :=
    ((flat_and_surjective_SpecMap_iff φ).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr
      (AdjoinRoot.faithfullyFlat_of_monic (monic_X_pow_sub_C t hn₀)
        hdeg))).2
  have hφ : φ t = AdjoinRoot.root (X ^ n - C t) ^ n := by
    have := AdjoinRoot.eval₂_root (X ^ n - C t)
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
    exact this.symm
  exact ⟨_, _, inferInstance, inferInstance, exists_pow_eq_pullback_fst_toSpecΓ_appTop φ hφ⟩

variable (X : Scheme.{u}) (n : ℕ)

/-- The sheaf `μₙ` of `n`-th roots of unity on the small étale site of `X`: the kernel of the
`n`-th power map `n • 𝟙` on `𝔾ₘ`. -/
noncomputable def rootsOfUnitySheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (n • 𝟙 X.gmSheaf)

/-- The *Kummer sequence* of a scheme `X` and an integer `n`: the sequence of étale sheaves

```
  0 ──▶ μₙ ──kernel.ι──▶ 𝔾ₘ ──n • 𝟙──▶ 𝔾ₘ ──▶ 0
```

on `X`, the second map being `ω ↦ ωⁿ` and `μₙ = ker(n)` the sheaf of `n`-th roots of unity.
-/
noncomputable def kummerSequence :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (kernel.ι (n • 𝟙 X.gmSheaf)) (n • 𝟙 X.gmSheaf) (kernel.condition _)

/-- The `n`-th power map `n • 𝟙` on `𝔾ₘ` is locally surjective for the étale topology when `n` is
invertible on `X`. -/
theorem isLocallySurjective_nsmul_gmSheaf (hn : IsUnit (n : Γ(X, ⊤))) :
    Sheaf.IsLocallySurjective (n • 𝟙 X.gmSheaf) where
  imageSieve_mem {U} s := by
    have hnU : IsUnit (n : Γ(U.left, ⊤)) := by
      have := hn.map U.hom.appTop.hom
      rwa [map_natCast] at this
    rcases eq_or_ne n 0 with rfl | hn₀
    · -- If `0` is invertible then `Γ(U, 𝒪)` is zero, so every section is in the image.
      have : Subsingleton Γ(U.left, ⊤) := subsingleton_of_zero_eq_one (by simpa using hnU)
      have hs : s = 0 := by
        apply ULift.ext
        apply Additive.toMul.injective
        exact Subsingleton.elim (α := Γ(U.left, ⊤)ˣ) _ _
      rw [show s = (0 • 𝟙 X.gmSheaf).hom.app (Opposite.op U) 0 by rw [hs, map_zero],
        Presheaf.imageSieve_app]
      exact GrothendieckTopology.top_mem _ _
    obtain ⟨V, f, hf, hsurj, ω, hω⟩ :=
      exists_etale_surjective_pow_eq_appTop hn₀ hnU (Units.isUnit (Additive.toMul s.down))
    have : Etale (f ≫ U.hom) := by have := U.prop; infer_instance
    let g : MorphismProperty.Over.mk ⊤ (f ≫ U.hom) this ⟶ U :=
      MorphismProperty.Over.homMk f rfl
    refine GrothendieckTopology.superset_covering _ ?_
      ((ofArrows_mem_smallEtaleTopology_iff (fun _ : Unit ↦ g)).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨⟩
      have hωu : IsUnit ω := (isUnit_pow_iff hn₀).mp (hω ▸ (Units.isUnit _).map _)
      refine ⟨⟨Additive.ofMul hωu.unit⟩, ?_⟩
      have e : (n • 𝟙 X.gmSheaf).hom = n • 𝟙 X.gmSheaf.obj :=
        (sheafToPresheaf _ _).map_nsmul (f := 𝟙 X.gmSheaf) (n := n)
      have e' (A : AddCommGrpCat.{u + 1}) (x : A) : ConcreteCategory.hom (n • 𝟙 A) x = n • x :=
        rfl
      rw [e, NatTrans.app_nsmul, NatTrans.id_app, e']
      apply ULift.ext
      apply Additive.toMul.injective
      apply Units.ext
      change ((Additive.toMul (n • Additive.ofMul hωu.unit : Additive Γ(V, ⊤)ˣ) : Γ(V, ⊤)ˣ) :
        Γ(V, ⊤)) = f.appTop.hom
          ((Additive.toMul (s.down : Additive Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤))
      rw [toMul_nsmul, toMul_ofMul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, hω]
      rfl
    · simp only [Set.iUnion_const]
      exact Set.range_eq_univ.mpr hsurj.surj

/-- **Exactness of the Kummer sequence.** Let `X` be a scheme and let `n ≥ 1` be invertible on
`X`. Then the Kummer sequence `AlgebraicGeometry.Scheme.kummerSequence` is a short exact
sequence of sheaves on `X_ét`. -/
theorem kummerSequence_shortExact (hn : IsUnit (n : Γ(X, ⊤))) :
    (X.kummerSequence n).ShortExact :=
  have := X.isLocallySurjective_nsmul_gmSheaf n hn
  { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
    mono_f := by dsimp [kummerSequence]; infer_instance
    epi_g := Sheaf.epi_of_isLocallySurjective (n • 𝟙 X.gmSheaf) }

/-- On sections, the second map of the Kummer sequence is multiplication by `n` in the
additively written group of units. -/
lemma kummerSequence_g_app_apply (U : X.Etaleᵒᵖ) (x : (X.kummerSequence n).X₂.obj.obj U) :
    (X.kummerSequence n).g.hom.app U x = n • x := by
  have e : (n • 𝟙 X.gmSheaf).hom = n • 𝟙 X.gmSheaf.obj :=
    (sheafToPresheaf _ _).map_nsmul (f := 𝟙 X.gmSheaf) (n := n)
  change (n • 𝟙 X.gmSheaf).hom.app U x = n • x
  rw [e, NatTrans.app_nsmul, NatTrans.id_app]
  rfl

/-- The connecting homomorphism `α: Γ(X, 𝒪)ˣ = H⁰(X, 𝔾ₘ) → H¹(X, μₙ)` of the long exact
cohomology sequence of the Kummer sequence, for `n` invertible on `X`
(`AlgebraicGeometry.Scheme.kummerSequence_shortExact`). The group of units is written
additively. -/
noncomputable def kummerδ₀ (hn : IsUnit (n : Γ(X, ⊤))) :
    Additive Γ(X, ⊤)ˣ →+ Sheaf.H (X.rootsOfUnitySheaf n) 1 :=
  (Sheaf.H.δSections (X.kummerSequence_shortExact n hn)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).comp
      AddEquiv.ulift.symm.toAddMonoidHom

/-- The connecting homomorphism `α: H¹(X, 𝔾ₘ) → H²(X, μₙ)` of the long exact cohomology
sequence of the Kummer sequence, for `n` invertible on `X`
(`AlgebraicGeometry.Scheme.kummerSequence_shortExact`). -/
noncomputable def kummerδ₁ (hn : IsUnit (n : Γ(X, ⊤))) :
    X.CohomologicalPicardGroup →+ Sheaf.H (X.rootsOfUnitySheaf n) 2 :=
  Sheaf.H.δSucc (X.kummerSequence_shortExact n hn) 1

/-- On cohomology, the map induced by the multiplication by `n` on `𝔾ₘ` is the multiplication
by `n`. -/
lemma sheafH_map_kummerSequence_g_apply (q : ℕ) (y : Sheaf.H X.gmSheaf q) :
    Sheaf.H.map (X.kummerSequence n).g q y = n • y := by
  change Sheaf.H.map (n • 𝟙 X.gmSheaf) q y = n • y
  rw [Sheaf.H.map_nsmul_apply, Sheaf.H.map_id_apply]

/-- The exactness statements of `AlgebraicGeometry.Scheme.exact_sheafH_rootsOfUnitySheaf_one`,
for an arbitrary terminal object `T` of `X.Etale` and identification `e` of the units of `X`
with the sections of `𝔾ₘ` over `T`. -/
private lemma exact_sheafH_rootsOfUnitySheaf_one_aux (hS : (X.kummerSequence n).ShortExact)
    {T : X.Etale} (hT : IsTerminal T)
    (e : Additive Γ(X, ⊤)ˣ ≃+ (X.kummerSequence n).X₃.obj.obj (Opposite.op T)) :
    ((Sheaf.H.δSections hS hT).comp e.toAddMonoidHom).ker =
        (zsmulAddGroupHom (α := Additive Γ(X, ⊤)ˣ) (n : ℤ)).range ∧
      Function.Exact ((Sheaf.H.δSections hS hT).comp e.toAddMonoidHom)
        (Sheaf.H.map (X.kummerSequence n).f 1) ∧
      (Sheaf.H.map (X.kummerSequence n).f 1).range =
        AddSubgroup.torsionBy (Sheaf.H (X.kummerSequence n).X₂ 1) n := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, ← AddMonoidHom.mem_ker, Sheaf.H.ker_δ]
    simp only [AddMonoidHom.mem_range, kummerSequence_g_app_apply, zsmulAddGroupHom_apply,
      natCast_zsmul]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨e.symm y, by rw [← map_nsmul, hy]; simp⟩
    · rintro ⟨y, rfl⟩
      exact ⟨(e y : (X.kummerSequence n).X₂.obj.obj (Opposite.op T)), (map_nsmul e n y).symm⟩
  · intro x
    rw [Sheaf.H.exact_δ_map hS hT x]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨e.symm y, by simpa using hy⟩, fun ⟨y, hy⟩ ↦ ⟨e y, hy⟩⟩
  · ext x
    rw [AddSubgroup.torsionBy.nsmul_iff, AddMonoidHom.mem_range,
      ← X.sheafH_map_kummerSequence_g_apply n 1]
    exact (Sheaf.H.exact_map_map hS 1 x).symm

/-- **`H¹` via the Kummer sequence.** For a scheme `X` and `n` invertible on `X` the sequence

```
  Γ(X, 𝒪)ˣ ──(·)ⁿ──▶ Γ(X, 𝒪)ˣ ──α──▶ H¹(X, μₙ) ──β──▶ H¹(X, 𝔾ₘ)[n] ⟶ 0
```

is exact, that is, `0 → Γ(X, 𝒪)ˣ/n → H¹(X, μₙ) → H¹(X, 𝔾ₘ)[n] → 0`. Here `α` is the
connecting homomorphism `AlgebraicGeometry.Scheme.kummerδ₀` and `β` is induced by the inclusion
`μₙ ⟶ 𝔾ₘ`: the statement is `ker α = (Γ(X, 𝒪)ˣ)ⁿ`, `ker β = im α` and `im β = H¹(X, 𝔾ₘ)[n]`.
-/
theorem exact_sheafH_rootsOfUnitySheaf_one (hn : IsUnit (n : Γ(X, ⊤))) :
    (X.kummerδ₀ n hn).ker = (zsmulAddGroupHom (α := Additive Γ(X, ⊤)ˣ) (n : ℤ)).range ∧
      Function.Exact (X.kummerδ₀ n hn) (Sheaf.H.map (kernel.ι (n • 𝟙 X.gmSheaf)) 1) ∧
      (Sheaf.H.map (kernel.ι (n • 𝟙 X.gmSheaf)) 1).range =
        AddSubgroup.torsionBy X.CohomologicalPicardGroup n :=
  X.exact_sheafH_rootsOfUnitySheaf_one_aux n (X.kummerSequence_shortExact n hn)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X) AddEquiv.ulift.symm

/-- The short exact sequence `0 → Γ(X, 𝒪)ˣ/n → H¹(X, μₙ) → H¹(X, 𝔾ₘ)[n] → 0` of
`AlgebraicGeometry.Scheme.exact_sheafH_rootsOfUnitySheaf_one`, with the maps forgotten. -/
theorem exists_exact_sheafH_rootsOfUnitySheaf_one (hn : IsUnit (n : Γ(X, ⊤))) :
    ∃ (α : Additive Γ(X, ⊤)ˣ →+ Sheaf.H (X.rootsOfUnitySheaf n) 1)
      (β : Sheaf.H (X.rootsOfUnitySheaf n) 1 →+ X.CohomologicalPicardGroup),
      α.ker = (zsmulAddGroupHom (α := Additive Γ(X, ⊤)ˣ) (n : ℤ)).range ∧
        Function.Exact α β ∧ β.range = AddSubgroup.torsionBy X.CohomologicalPicardGroup n :=
  ⟨_, _, X.exact_sheafH_rootsOfUnitySheaf_one n hn⟩

/-- **`H¹(X, μₙ) = H¹(X, 𝔾ₘ)[n]`.** If `n` is invertible on `X` and every unit on `X` is an
`n`-th power, then `H¹(X, μₙ) ≅ H¹(X, 𝔾ₘ)[n]`. -/
theorem nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one (hn : IsUnit (n : Γ(X, ⊤)))
    (hdiv : ∀ u : Γ(X, ⊤)ˣ, ∃ v : Γ(X, ⊤)ˣ, v ^ n = u) :
    Nonempty (Sheaf.H (X.rootsOfUnitySheaf n) 1 ≃+
      AddSubgroup.torsionBy X.CohomologicalPicardGroup n) := by
  obtain ⟨α, β, hα, hαβ, hβ⟩ := X.exists_exact_sheafH_rootsOfUnitySheaf_one n hn
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨u, rfl⟩ := (hαβ x).1 hx
    obtain ⟨v, hv⟩ := hdiv (Additive.toMul u)
    have hu : u ∈ α.ker := by
      rw [hα]
      exact ⟨Additive.ofMul v, by simp [← ofMul_pow, hv]⟩
    exact hu
  rw [← hβ]
  exact ⟨AddMonoidHom.ofInjective hinj⟩

/-- **`H²` via the Kummer sequence.** For a scheme `X` and `n` invertible on `X` the sequence

```
  H¹(X, 𝔾ₘ) ──n·──▶ H¹(X, 𝔾ₘ) ──α──▶ H²(X, μₙ) ──β──▶ H²(X, 𝔾ₘ)[n] ⟶ 0
```

is exact, that is, `0 → H¹(X, 𝔾ₘ)/n → H²(X, μₙ) → H²(X, 𝔾ₘ)[n] → 0`. Here `α` is the
connecting homomorphism `AlgebraicGeometry.Scheme.kummerδ₁` and `β` is induced by the inclusion
`μₙ ⟶ 𝔾ₘ`: the statement is `ker α = n · H¹(X, 𝔾ₘ)`, `ker β = im α` and
`im β = H²(X, 𝔾ₘ)[n]`. -/
theorem exact_sheafH_rootsOfUnitySheaf_two (hn : IsUnit (n : Γ(X, ⊤))) :
    (X.kummerδ₁ n hn).ker = (zsmulAddGroupHom (α := X.CohomologicalPicardGroup) (n : ℤ)).range ∧
      Function.Exact (X.kummerδ₁ n hn) (Sheaf.H.map (kernel.ι (n • 𝟙 X.gmSheaf)) 2) ∧
      (Sheaf.H.map (kernel.ι (n • 𝟙 X.gmSheaf)) 2).range =
        AddSubgroup.torsionBy X.CohomologicalBrauerGroup n := by
  have hS := X.kummerSequence_shortExact n hn
  change _ ∧ Function.Exact _ (Sheaf.H.map (X.kummerSequence n).f 2) ∧
    (Sheaf.H.map (X.kummerSequence n).f 2).range = AddSubgroup.torsionBy _ n
  refine ⟨?_, Sheaf.H.exact_δSucc_map hS 1, ?_⟩
  · ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    simp only [zsmulAddGroupHom_apply, natCast_zsmul,
      ← X.sheafH_map_kummerSequence_g_apply n 1]
    exact (Sheaf.H.exact_map_δSucc hS 1 x)
  · ext x
    rw [AddSubgroup.torsionBy.nsmul_iff, AddMonoidHom.mem_range,
      ← X.sheafH_map_kummerSequence_g_apply n 2]
    exact (Sheaf.H.exact_map_map hS 2 x).symm

/-- The short exact sequence `0 → H¹(X, 𝔾ₘ)/n → H²(X, μₙ) → H²(X, 𝔾ₘ)[n] → 0` of
`AlgebraicGeometry.Scheme.exact_sheafH_rootsOfUnitySheaf_two`, with the maps forgotten. -/
theorem exists_exact_sheafH_rootsOfUnitySheaf_two (hn : IsUnit (n : Γ(X, ⊤))) :
    ∃ (α : X.CohomologicalPicardGroup →+ Sheaf.H (X.rootsOfUnitySheaf n) 2)
      (β : Sheaf.H (X.rootsOfUnitySheaf n) 2 →+ X.CohomologicalBrauerGroup),
      α.ker = (zsmulAddGroupHom (α := X.CohomologicalPicardGroup) (n : ℤ)).range ∧
        Function.Exact α β ∧ β.range = AddSubgroup.torsionBy X.CohomologicalBrauerGroup n :=
  ⟨_, _, X.exact_sheafH_rootsOfUnitySheaf_two n hn⟩

/-- The constant étale sheaf `ℤ/n` on a scheme `X`, valued in abelian groups of the universe of
the small étale site. -/
noncomputable abbrev constantZMod : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))

/-- The global sections of the constant sheaf `ℤ/n` on a connected scheme are `ℤ/n`:
`H⁰(X_ét, ℤ/n) ≅ ℤ/n`. -/
theorem nonempty_addEquiv_sheafH_zero_constantZMod [ConnectedSpace X] :
    Nonempty (Sheaf.H (X.constantZMod n) 0 ≃+ ZMod n) := by
  -- the sections of a constant étale sheaf over `X` are the locally constant functions
  -- `X → ℤ/n` (`AlgebraicGeometry.Scheme.bijective_toSheafify_app_terminal`), and these are
  -- constant since `X` is connected
  have hT : IsTerminal (Etale.mk (𝟙 X)) :=
    MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  exact ⟨(Sheaf.H.equiv₀ _ hT).trans ((AddEquiv.ofBijective _
    (X.bijective_toSheafify_app_terminal (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))).symm.trans
      AddEquiv.ulift)⟩

end AlgebraicGeometry.Scheme

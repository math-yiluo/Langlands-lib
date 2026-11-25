/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.CoherentSheaf
public import WeilConjectures.Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Riemann–Roch for coherent sheaves on a curve

Let `X` be a smooth proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`, of genus `g`. For a
coherent `𝒪_X`-module `ℱ` with torsion subsheaf `𝒯` and torsion-free quotient `ℰ = ℱ / 𝒯`, which
is finite locally free of rank `rk ℱ`, we define the degree
`deg ℱ = dim_k H⁰(X, 𝒯) + deg (det ℰ)` (`AlgebraicGeometry.Scheme.Modules.coherentDegree`), where
`det ℰ = ⋀^{rk ℱ} ℰ` and the degree of a line bundle is `AlgebraicGeometry.Scheme.Modules.degree`,
and prove Riemann–Roch `χ(ℱ) = deg ℱ + rk ℱ (1 - g)`
(`AlgebraicGeometry.Scheme.Modules.eulerChar_eq_coherentDegree_add`).

The proof follows the blueprint.

* The torsion subsheaf `𝒯` is killed by its annihilator ideal sheaf, which is nonzero on every
  nonempty affine open, so `𝒯` is the pushforward of a module on a closed subscheme which is
  finite over `k`, hence affine. Therefore `H¹(X, 𝒯) = 0`
  (`AlgebraicGeometry.Scheme.Modules.subsingleton_H_one_torsion`) and `χ(𝒯) = h⁰(𝒯)`.
* For `ℰ` finite locally free of rank `r`, `χ(ℰ) = deg (⋀ʳ ℰ) + r (1 - g)`
  (`AlgebraicGeometry.Scheme.Modules.eulerChar_eq_degree_exteriorPower_add`), by induction on `r`.
  For `r ≥ 1`, Serre's theorem A for an ample line bundle `𝒪_X(x)` gives a nonzero morphism
  `ℳ ⟶ ℰ` from an invertible module. Its saturation, the kernel `ℒ` of `ℰ ⟶ coker / torsion`,
  is a line subbundle with locally free quotient `ℰ'` of rank `r - 1`, and
  `⋀ʳ ℰ ≅ ℒ ⊗ ⋀^{r-1} ℰ'` (`AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_iso_tensorObj`).
  Additivity of `χ` and of the degree, Riemann–Roch for line bundles and the induction
  hypothesis conclude.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.coherentDegree`: the degree of a coherent module on a curve.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_one_torsion`: `H¹(X, 𝒯) = 0`.
- `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_degree_exteriorPower_add`: Riemann–Roch for
  finite locally free modules.
- `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_coherentDegree_add`: Riemann–Roch for coherent
  modules.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`,
`theorem-riemann-roch-coherent-serre-duality`)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory

open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.Modules

section General

variable {X : Scheme.{u}}

/-- The empty wedge product is a free generator of `⋀⁰ M`, since `⋀⁰_R N ≅ R`. -/
lemma isFreeGenerator_wedge_elim0 (M : X.Modules) (U : X.Opens) :
    IsFreeGenerator (wedge (M := M) (U := U) (Fin.elim0 : Fin 0 → Γ(M, U))) := by
  refine isFreeGenerator_toSheafificationObj_app _ _ fun V hV x hx ↦ ⟨V, le_rfl, hx, ?_⟩
  erw [PresheafOfModules.exteriorPower_map_ιMulti]
  generalize (fun k ↦ M.val.restrictₛₗ (homOfLE (le_rfl.trans hV)).op (Fin.elim0 k)) = v
  have h (a : Γ(X, V)) : a • exteriorPower.ιMulti Γ(X, V) 0 v =
      (exteriorPower.zeroEquiv Γ(X, V) Γ(M, V)).symm a := by
    apply (exteriorPower.zeroEquiv Γ(X, V) Γ(M, V)).injective
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.map_smul]
    erw [exteriorPower.zeroEquiv_ιMulti]
    rw [smul_eq_mul, mul_one]
  convert (exteriorPower.zeroEquiv Γ(X, V) Γ(M, V)).symm.bijective using 1
  exact funext h

/-- **The zeroth exterior power is the structure sheaf**: `⋀⁰ M ≅ 𝒪_X`, the empty wedge product
and `1` being global free generators. -/
theorem nonempty_exteriorPower_zero_iso (M : X.Modules) :
    Nonempty (M.exteriorPower 0 ≅ 𝟙_ X.Modules) := by
  refine nonempty_iso_of_isFreeGenerator (U := fun _ : Unit ↦ (⊤ : X.Opens))
    (e := fun _ ↦ wedge (M := M) (Fin.elim0 : Fin 0 → Γ(M, ⊤)))
    (f := fun _ ↦ (1 : Γ(X, ⊤))) (iSup_const) (fun _ ↦ isFreeGenerator_wedge_elim0 M ⊤)
    ?_ (fun _ ↦ isFreeGenerator_one ⊤)
  intro i j W hi hj a b hab
  have he := (isFreeGenerator_wedge_elim0 M ⊤).map hi
  have : a = b := he.smul_left_injective hab
  subst this
  rfl

/-- A finite locally free module of rank zero is zero. -/
lemma isZero_of_isFiniteLocallyFreeOfRank_zero (M : X.Modules) [M.IsFiniteLocallyFreeOfRank 0] :
    IsZero M := by
  refine (isZero_iff_forall_subsingleton M).mpr fun U ↦ ⟨fun s t ↦ ?_⟩
  suffices h : ∀ s : Γ(M, U), s = 0 from (h s).trans (h t).symm
  intro s
  refine eq_zero_of_forall_exists s fun x hx ↦ ?_
  obtain ⟨V, v, hxV, hv⟩ := exists_isLocalFrame (r := 0) M x
  obtain ⟨b, -⟩ := hv (U ⊓ V) inf_le_right
  have : Subsingleton Γ(M, U ⊓ V) := b.repr.toEquiv.subsingleton
  exact ⟨U ⊓ V, inf_le_left, ⟨hx, hxV⟩, Subsingleton.elim _ _⟩

end General

section Integral

variable {X : Scheme.{u}} [IsIntegral X]

/-- **Finite locally free modules are torsion-free.** On an integral scheme, every torsion
section of a finite locally free module vanishes: locally it is killed by a nonzero function,
and the sections over affine opens are projective, hence flat, so have no torsion. -/
lemma eq_zero_of_isTorsionSection {M : X.Modules} [M.IsFiniteLocallyFree] {U : X.Opens}
    {s : Γ(M, U)} (hs : IsTorsionSection M s) : s = 0 := by
  refine eq_zero_of_forall_exists s fun x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (U := U) hx
  refine ⟨V, hVU, hxV, ?_⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  obtain ⟨a, ha, has⟩ :=
    (isTorsionSection_iff_exists_smul_eq_zero hV ⟨x, hxV⟩ _).1 (hs.map hVU)
  have := (finitePresentation_projective_sections M hV).2
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha)
    (has.trans (smul_zero a).symm)

/-- **Nonzero morphisms to a torsion-free module are nonzero at the generic point.** If every
torsion section of `E` vanishes, a morphism `φ : M ⟶ E` whose stalk at the generic point is zero
is zero: `φ(m)` has zero germ at the generic point, so vanishes on a nonempty open, so is a
torsion section. -/
lemma eq_zero_of_stalkLinearMap_genericPoint_eq_zero {M E : X.Modules}
    (hE : ∀ (U : X.Opens) (s : Γ(E, U)), IsTorsionSection E s → s = 0) (φ : M ⟶ E)
    (hφ : φ.stalkLinearMap (genericPoint X) = 0) : φ = 0 := by
  refine hom_ext _ _ fun U ↦ ?_
  ext m
  change φ.app U m = 0
  by_cases hU : (U : Set X).Nonempty
  · have hη : genericPoint X ∈ U := genericPoint_mem hU.some_mem
    have h0 : E.presheaf.germ U _ hη (φ.app U m) = E.presheaf.germ U _ hη 0 := by
      rw [← Hom.stalkLinearMap_germ, hφ, map_zero]
      rfl
    obtain ⟨W, hηW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq E.presheaf _ hη hη _ _ h0
    refine hE U _ (isTorsionSection_of_presheaf_map_eq_zero (leOfHom iU) ⟨_, hηW⟩ ?_)
    rw [show homOfLE (leOfHom iU) = iU from rfl, hW, map_zero]
  · exact eq_zero_of_forall_exists _ fun x hx ↦ (hU ⟨x, hx⟩).elim

end Integral


section Torsion

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsIntegral X]

variable (k) in
include k in
/-- The torsion subsheaf of a coherent module on a smooth curve is coherent: it is the kernel of
`ℱ ⟶ ℱ / ℱ_tors`. -/
lemma isFinitePresentation_torsion (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (torsion ℱ) := by
  have := isLocallyNoetherian_of_smoothOfRelativeDimension_one k (X := X)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (torsionQuotient ℱ) :=
    isQuasicoherent_cokernel _
  have := isFinitePresentation_kernel (torsionπ ℱ)
  let e : torsion ℱ ≅ kernel (torsionπ ℱ) :=
    IsLimit.conePointUniqueUpToIso (shortExact_torsionShortComplex ℱ).fIsKernel
      (limit.isLimit _)
  exact isFinitePresentation_of_iso e.symm

omit [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] in
/-- The sections of the torsion subsheaf over a nonempty affine open form a torsion module. -/
lemma isTorsion_sections_torsion (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : Module.IsTorsion Γ(X, U) Γ(torsion ℱ, U) := by
  intro t
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U›
    exact ⟨x.1, x.2⟩
  obtain ⟨a, ha, hat⟩ := (isTorsionSection_iff_exists_smul_eq_zero hU hne t.1).1 t.2
  exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, Subtype.ext hat⟩

variable (k) in
/-- **The support of the torsion is finite over `k`.** The closed subscheme cut out by the
annihilator of the torsion subsheaf of a coherent module on a smooth curve is quasi-finite over
`k`: on a nonempty affine open the annihilator contains a nonzero function, since the sections
of the torsion form a finite torsion module, and a nonzero function on a curve cuts out a
zero-dimensional subscheme. -/
lemma locallyQuasiFinite_annihilatorIdealSheaf_torsion (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] :
    have := isFinitePresentation_torsion k ℱ
    LocallyQuasiFinite ((annihilatorIdealSheaf (torsion ℱ)).subschemeι ≫ X ↘ Spec (.of k)) := by
  have := isFinitePresentation_torsion k ℱ
  set J := annihilatorIdealSheaf (torsion ℱ)
  set p := X ↘ Spec (.of k)
  have := SmoothOfRelativeDimension.smooth 1 p
  have hdim := topologicalKrullDim_le_of_smoothOfRelativeDimension p 1
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyQuasiFinite)
    (RingHom.QuasiFinite.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.QuasiFinite.holdsForLocalizationAway).left]
  intro d
  obtain ⟨U, hU, hdU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := J.subschemeι d) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨_, hdU⟩⟩
  have := finite_sections_of_isFinitePresentation (torsion ℱ) hU
  obtain ⟨f, hfJ, hf⟩ :=
    Submodule.annihilator_top_inter_nonZeroDivisors (isTorsion_sections_torsion ℱ hU)
  let U' : X.affineOpens := ⟨U, hU⟩
  refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨_, U'.2.preimage J.subschemeι⟩, hdU, le_top, ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ U'.1 _ le_top le_rfl, CommRingCat.hom_comp,
    ← Scheme.Hom.app_eq_appLE]
  refine RingHom.QuasiFinite.comp_of_ringKrullDim_le_one ?_ _ ?_ ?_ _
    (J.subschemeι_app_surjective U') hf ?_
  · exact MulEquiv.isField (Field.toIsField k)
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv
  · exact HasRingHomProperty.appLE (P := @LocallyOfFiniteType) p inferInstance
      ⟨⊤, isAffineOpen_top _⟩ U' le_top
  · rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      hU.isoSpec.hom.homeomorph.isHomeomorph).symm.le.trans
        ((topologicalKrullDim_subspace_le X U).trans (by exact_mod_cast hdim))
  · rw [← RingHom.mem_ker, IdealSheafData.ker_subschemeι_app _ U', annihilatorIdealSheaf_ideal,
      ← Submodule.annihilator_top]
    exact hfJ

variable [IsProper (X ↘ Spec (.of k))]

variable (k) in
include k in
/-- **The torsion has no `H¹`.** For a coherent module `ℱ` on a smooth proper curve, the torsion
subsheaf `𝒯` is killed by its annihilator `I`, so `𝒯 ≅ ι_* ι^* 𝒯` for the closed immersion
`ι : V(I) ⟶ X`. The scheme `V(I)` is finite over `k`
(`AlgebraicGeometry.Scheme.Modules.locallyQuasiFinite_annihilatorIdealSheaf_torsion`), hence
affine, and `ι` is affine, so `H¹(X, 𝒯) ≅ H¹(V(I), ι^* 𝒯) = 0`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem subsingleton_H_one_torsion (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] :
    Subsingleton ((torsion ℱ).H 1) := by
  have := isFinitePresentation_torsion k ℱ
  set J := annihilatorIdealSheaf (torsion ℱ)
  have hiso : IsIso (pullbackUnit J.subschemeι (torsion ℱ)) :=
    isIso_pullbackUnit_subschemeι_of_smul_eq_zero _ J fun U a ha m ↦
      Module.mem_annihilator.1 ha m
  have := locallyQuasiFinite_annihilatorIdealSheaf_torsion k ℱ
  have : IsFinite (J.subschemeι ≫ X ↘ Spec (.of k)) :=
    IsFinite.of_isProper_of_locallyQuasiFinite _
  have : IsAffine J.subscheme := isAffine_of_isAffineHom (J.subschemeι ≫ X ↘ Spec (.of k))
  let : J.subscheme.Over (Spec (.of k)) := ⟨J.subschemeι ≫ X ↘ Spec (.of k)⟩
  have : J.subschemeι.IsOver (Spec (.of k)) := ⟨rfl⟩
  have h0 : Subsingleton (((pullback J.subschemeι).obj (torsion ℱ)).H 1) :=
    subsingleton_H_succ_of_isAffine ((pullback J.subschemeι).obj (torsion ℱ)) 0
  obtain ⟨e'⟩ := nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom k J.subschemeι 1
  let e₁ := (cohomologyFunctor k 1).mapIso (asIso (pullbackUnit J.subschemeι (torsion ℱ)))
  let e₂ := e'.app ⟨(pullback J.subschemeι).obj (torsion ℱ), inferInstance⟩
  exact @Equiv.subsingleton _ _ (e₁ ≪≫ e₂.symm).toLinearEquiv.toEquiv h0

variable (k) in
/-- **The Euler characteristic of the torsion is its number of sections**: `χ(𝒯) = h⁰(𝒯)`, as
`H¹(X, 𝒯) = 0`. -/
theorem eulerChar_torsion (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] :
    (torsion ℱ).eulerChar k = (torsion ℱ).finrankH k 0 := by
  have := subsingleton_H_one_torsion k ℱ
  have h₁ : (torsion ℱ).finrankH k 1 = 0 := Module.finrank_zero_of_subsingleton
  rw [eulerChar_eq_finrankH_zero_sub_finrankH_one, h₁]
  simp

end Torsion

section Additivity

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

variable (k) in
/-- **Additivity of the Euler characteristic on a curve.** For a short exact sequence of
coherent modules on a smooth proper curve, `χ(ℱ₂) = χ(ℱ₁) + χ(ℱ₃)`: the cohomology is
finite-dimensional and vanishes in degrees `≥ 2`. -/
theorem eulerChar_eq_add_of_shortExact_of_isCoherent {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₁]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) S.X₁]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₂]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) S.X₂]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₃]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) S.X₃] :
    S.X₂.eulerChar k = S.X₁.eulerChar k + S.X₃.eulerChar k := by
  have := fun q ↦ finiteDimensional_H_of_isProper (k := k) S.X₁ q
  have := fun q ↦ finiteDimensional_H_of_isProper (k := k) S.X₂ q
  have := fun q ↦ finiteDimensional_H_of_isProper (k := k) S.X₃ q
  exact eulerChar_eq_add_of_shortExact k hS 1 (fun q hq ↦ subsingleton_H_of_two_le k _ hq)
    (fun q hq ↦ subsingleton_H_of_two_le k _ hq) (fun q hq ↦ subsingleton_H_of_two_le k _ hq)

end Additivity

section LineSubbundle

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsIntegral X]

variable (k) in
include k in
/-- **Saturation of a line subsheaf.** Let `E` be finite locally free of rank `r + 1` on a smooth
curve and `φ : ℳ ⟶ E` a morphism from an invertible module which is nonzero at the generic
point. Let `C` be the cokernel of `φ`, `Q = C / C_tors` and `L` the kernel of `E ⟶ Q`. Then
`0 ⟶ L ⟶ E ⟶ Q ⟶ 0` is short exact with `L` invertible and `Q` finite locally free of rank `r`.

`Q` is locally free of rank `rk C` (`isFiniteLocallyFreeOfRank_torsionQuotient`) and `L` is
locally free as a coherent submodule of the torsion-free `E`. The image of `φ` has rank one,
being nonzero at the generic point and a quotient of `ℳ`, so `rk C = r` and `rk L = 1`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem exists_shortExact_of_stalkLinearMap_ne_zero {r : ℕ} (E ℳ : X.Modules)
    [E.IsFiniteLocallyFreeOfRank (r + 1)] [ℳ.IsInvertible] (φ : ℳ ⟶ E)
    (hφ : φ.stalkLinearMap (genericPoint X) ≠ 0) :
    ∃ (L Q : X.Modules) (f : L ⟶ E) (g : E ⟶ Q) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧ L.IsFiniteLocallyFreeOfRank 1 ∧
        Q.IsFiniteLocallyFreeOfRank r := by
  have := isLocallyNoetherian_of_smoothOfRelativeDimension_one k (X := X)
  have : E.IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have : SheafOfModules.IsInvertible.{u, u, u} ℳ := IsInvertible.sheafOfModules_isInvertible ℳ
  have hℳ1 : ℳ.IsFiniteLocallyFreeOfRank 1 :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one ℳ).1 inferInstance
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (cokernel φ) :=
    isQuasicoherent_cokernel φ
  have : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (cokernel φ) :=
    isFinitePresentation_cokernel φ
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (torsionQuotient (cokernel φ)) :=
    isQuasicoherent_cokernel _
  have : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf)
      (torsionQuotient (cokernel φ)) :=
    isFinitePresentation_cokernel _
  have hQ := isFiniteLocallyFreeOfRank_torsionQuotient k (cokernel φ)
  let g : E ⟶ torsionQuotient (cokernel φ) := cokernel.π φ ≫ torsionπ (cokernel φ)
  have : Epi (torsionπ (cokernel φ)) := inferInstanceAs (Epi (cokernel.π _))
  have : Epi g := epi_comp _ _
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (kernel g) :=
    isQuasicoherent_kernel g
  have : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (kernel g) :=
    isFinitePresentation_kernel g
  have hS : (ShortComplex.mk (kernel.ι g) g (kernel.condition g)).ShortExact :=
    .mk' (ShortComplex.exact_kernel g) inferInstance inferInstance
  -- the kernel `L` is torsion-free, hence locally free
  have hLtf (W : X.Opens) (hW : IsAffineOpen W) (hne : Nonempty W) :
      Submodule.torsion Γ(X, W) Γ(kernel g, W) = ⊥ := by
    have hne' : (W : Set X).Nonempty := by
      obtain ⟨x⟩ := hne
      exact ⟨x.1, x.2⟩
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨⟨a, ha⟩, hat⟩ := (Submodule.mem_torsion_iff t).mp ht
    have hat' : a • t = 0 := hat
    have h1 : IsTorsionSection E ((kernel.ι g).app W t) := by
      rw [isTorsionSection_iff_exists_smul_eq_zero hW hne']
      exact ⟨a, nonZeroDivisors.ne_zero ha, by rw [← Hom.app_smul, hat', map_zero]⟩
    have h2 := eq_zero_of_isTorsionSection h1
    rw [Submodule.mem_bot]
    exact injective_map_kernelι (U := W) (f := g) (h2.trans (map_zero _).symm)
  have : (kernel g).IsFiniteLocallyFree := isFiniteLocallyFree_of_torsion_eq_bot k _ hLtf
  have hL := isFiniteLocallyFreeOfRank_rank (kernel g)
  -- ranks
  have hrE : E.rank = r + 1 := rank_eq_of_isFiniteLocallyFreeOfRank E
  have hrℳ : ℳ.rank = 1 := rank_eq_of_isFiniteLocallyFreeOfRank ℳ
  have hrQ : (torsionQuotient (cokernel φ)).rank = (cokernel φ).rank :=
    rank_eq_of_isFiniteLocallyFreeOfRank _
  have := finiteDimensional_stalk_of_isFiniteLocallyFree E
  have := finiteDimensional_stalk_of_isFiniteLocallyFree ℳ
  have h1 : E.rank = (kernel g).rank + (torsionQuotient (cokernel φ)).rank :=
    rank_eq_add_of_shortExact (S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)) hS
  let S₁ := ShortComplex.mk (kernel.ι (Abelian.factorThruImage φ)) (Abelian.factorThruImage φ)
    (kernel.condition _)
  have hS₁ : S₁.ShortExact := .mk' (ShortComplex.exact_kernel _) inferInstance inferInstance
  let S₂ := ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ) (kernel.condition _)
  have hS₂ : S₂.ShortExact := .mk' (ShortComplex.exact_kernel _) inferInstance inferInstance
  have h2 : ℳ.rank = (kernel (Abelian.factorThruImage φ)).rank + (Abelian.image φ).rank :=
    rank_eq_add_of_shortExact (S := S₁) hS₁
  have h3 : E.rank = (Abelian.image φ).rank + (cokernel φ).rank :=
    rank_eq_add_of_shortExact (S := S₂) hS₂
  have hI : (Abelian.image φ).rank ≠ 0 := by
    intro h0
    obtain ⟨hinj, -, -⟩ := injective_surjective_exact_stalkLinearMap hS₂ (genericPoint X)
    have : FiniteDimensional X.functionField
        ((Abelian.image φ).presheaf.stalk (genericPoint X)) :=
      FiniteDimensional.of_injective (S₂.f.stalkLinearMap (genericPoint X)) hinj
    have : Subsingleton ((Abelian.image φ).presheaf.stalk (genericPoint X)) :=
      Module.finrank_zero_iff.mp h0
    apply hφ
    ext x
    obtain ⟨U, hU, m, rfl⟩ := ℳ.presheaf.exists_germ_eq x
    have key : φ.app U m = (Abelian.image.ι φ).app U ((Abelian.factorThruImage φ).app U m) := by
      conv_lhs => rw [← Abelian.image.fac φ]
      rfl
    rw [LinearMap.zero_apply, Hom.stalkLinearMap_germ, key, ← Hom.stalkLinearMap_germ,
      Subsingleton.elim ((Abelian.image φ).presheaf.germ U _ hU _) 0, map_zero]
  have hC : (cokernel φ).rank = r := by omega
  refine ⟨kernel g, torsionQuotient (cokernel φ), kernel.ι g, g, kernel.condition g, hS, ?_, ?_⟩
  · have : (kernel g).rank = 1 := by omega
    rwa [this] at hL
  · rwa [hC] at hQ

end LineSubbundle

section LocallyFree

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GlobalSectionsBijective k X]

variable (k X) in
include k in
/-- A smooth curve over `k` with `H⁰(X, 𝒪_X) = k` is integral: it is connected and regular. -/
lemma isIntegral_of_globalSectionsBijective : IsIntegral X := by
  have := GlobalSectionsBijective.connectedSpace (k := k) (X := X)
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  exact IsRegular.isIntegral X

variable (k X) in
/-- **Curves have ample line bundles.** On a smooth proper curve with `H⁰(X, 𝒪_X) = k`, the line
bundle `𝒪_X(x)` of a closed point `x` has positive degree, hence is ample. -/
lemma exists_isAmple : ∃ ℒ : X.Modules, IsAmple (X ↘ Spec (.of k)) ℒ := by
  have := GlobalSectionsBijective.nonempty (k := k) (X := X)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := X)).exists_closed_singleton Set.univ_nonempty
  set J := IdealSheafData.vanishingIdeal ⟨{x}, hx⟩
  have hJ : J.IsInvertible :=
    isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one (X ↘ Spec (.of k)) hx
  have := hJ.isInvertible_dual_toModules
  refine ⟨J.toModulesᵛ, isAmple_of_degree_pos _ ?_⟩
  rw [hJ.degree_dual_toModules]
  have := hJ.isFinite_subschemeι_comp (k := k)
  have : Nonempty J.subscheme := by
    have hxJ : x ∈ J.support :=
      IdealSheafData.le_support_iff_le_vanishingIdeal.mpr le_rfl rfl
    rw [← SetLike.mem_coe, ← IdealSheafData.range_subschemeι] at hxJ
    obtain ⟨y, -⟩ := hxJ
    exact ⟨y⟩
  exact_mod_cast Scheme.Hom.finrankΓ_pos_of_isFinite _

variable (k) in
include k in
/-- **A nonzero coherent module receives a nonzero morphism from a line bundle.** For `ℒ` ample,
`E ⊗ ℒ^{⊗ n}` is generated by global sections for `n ≫ 0` (Serre's theorem A), so some global
section `s : 𝒪_X ⟶ E ⊗ ℒ^{⊗ n}` is nonzero, and `s ⊗ ℒ^{⊗ -n}` is a nonzero morphism
`ℒ^{⊗ -n} ⟶ E`. -/
lemma exists_hom_ne_zero (E : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) E]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) E] (hE : ¬ IsZero E) :
    ∃ (ℳ : X.Modules) (_ : ℳ.IsInvertible) (φ : ℳ ⟶ E), φ ≠ 0 := by
  obtain ⟨ℒ, hℒ⟩ := exists_isAmple k X
  have := hℒ.isInvertible
  obtain ⟨n₀, hn₀⟩ := exists_generatingSections_tensorObj_tensorPow (X ↘ Spec (.of k)) hℒ E
  obtain ⟨G⟩ := hn₀ n₀ le_rfl
  set P := ℒ.tensorPow n₀
  obtain ⟨e⟩ := nonempty_tensorObj_dual_iso_unit P
  let eE : E ≅ (E ⊗ P) ⊗ Pᵛ := (ρ_ E).symm ≪≫ whiskerLeftIso E e.symm ≪≫ (α_ E P Pᵛ).symm
  have := isEquivalence_tensorRight Pᵛ
  have hne : ¬ IsZero (E ⊗ P) := fun h ↦ hE (((tensorRight Pᵛ).map_isZero h).of_iso eE)
  set ψ := (E ⊗ P).freeHomEquiv.symm G.s
  have hψ : ψ ≠ 0 := by
    intro h
    have : Epi ψ := G.epi
    rw [h] at this
    exact hne (@IsZero.of_epi_zero _ _ _ _ _ this)
  obtain ⟨i, hi⟩ : ∃ i, SheafOfModules.ιFree i ≫ ψ ≠ 0 := by
    by_contra! h
    exact hψ (Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan _) _ _
      fun i ↦ (h i).trans comp_zero.symm)
  let s : 𝟙_ X.Modules ⟶ E ⊗ P := SheafOfModules.ιFree i ≫ ψ
  have hs : s ≠ 0 := hi
  refine ⟨Pᵛ, inferInstance, (λ_ Pᵛ).inv ≫ (s ▷ Pᵛ) ≫ eE.inv, ?_⟩
  intro h
  apply hs
  have h' : s ▷ Pᵛ = 0 := by
    have := congrArg (fun f ↦ (λ_ Pᵛ).hom ≫ f ≫ eE.hom) h
    simpa using this
  apply (tensorRight Pᵛ).map_injective
  rw [Functor.map_zero]
  exact h'

variable (k) in
/-- **Riemann–Roch for finite locally free modules.** On a smooth proper curve `X` over `k` with
`H⁰(X, 𝒪_X) = k`, of genus `g`, a finite locally free module `E` of rank `r` satisfies
`χ(E) = deg (⋀ʳ E) + r (1 - g)`.

By induction on `r`. For `r = 0`, `E = 0` and `⋀⁰ E = 𝒪_X`. Otherwise
`AlgebraicGeometry.Scheme.Modules.exists_hom_ne_zero` and
`AlgebraicGeometry.Scheme.Modules.exists_shortExact_of_stalkLinearMap_ne_zero` give a short exact
sequence `0 ⟶ L ⟶ E ⟶ Q ⟶ 0` with `L` invertible and `Q` locally free of rank `r - 1`; then
`⋀ʳ E ≅ L ⊗ ⋀^{r-1} Q`, and `χ` and the degree are additive.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`,
`theorem-riemann-roch-coherent-serre-duality`) -/
theorem eulerChar_eq_degree_exteriorPower_add (r : ℕ) (E : X.Modules)
    [E.IsFiniteLocallyFreeOfRank r] :
    E.eulerChar k = (E.exteriorPower r).degree k + r * (1 - (arithmeticGenus k X : ℤ)) := by
  have := isIntegral_of_globalSectionsBijective k X
  induction r generalizing E with
  | zero =>
    obtain ⟨e⟩ := nonempty_exteriorPower_zero_iso E
    rw [eulerChar_eq_zero_of_isZero k (isZero_of_isFiniteLocallyFreeOfRank_zero E),
      degree_congr k e]
    have : degree k (𝟙_ X.Modules) = 0 := degree_unit k
    simp [this]
  | succ r ih =>
    have : E.IsFiniteLocallyFree :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    have hE0 : ¬ IsZero E := by
      intro h
      have h1 : E.rank = r + 1 := rank_eq_of_isFiniteLocallyFreeOfRank E
      have hs := (isZero_iff_forall_subsingleton E).1 h
      have : Subsingleton (E.presheaf.stalk (genericPoint X)) := ⟨fun a b ↦ by
        obtain ⟨U, hU, s, rfl⟩ := E.presheaf.exists_germ_eq a
        obtain ⟨V, hV, t, rfl⟩ := E.presheaf.exists_germ_eq b
        rw [Subsingleton.elim s 0, Subsingleton.elim t 0, map_zero, map_zero]⟩
      rw [rank, Module.finrank_zero_of_subsingleton] at h1
      omega
    obtain ⟨ℳ, _, φ, hφ⟩ := exists_hom_ne_zero k E hE0
    have hφη : φ.stalkLinearMap (genericPoint X) ≠ 0 := fun h ↦
      hφ (eq_zero_of_stalkLinearMap_genericPoint_eq_zero
        (fun _ _ hs ↦ eq_zero_of_isTorsionSection hs) φ h)
    obtain ⟨L, Q, f, g, w, hS, hL, hQ⟩ :=
      exists_shortExact_of_stalkLinearMap_ne_zero k (r := r) E ℳ φ hφη
    obtain ⟨e⟩ := nonempty_exteriorPower_iso_tensorObj hS (r := r)
    have : SheafOfModules.IsInvertible.{u, u, u} L :=
      (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one L).2 hL
    have : L.IsInvertible := IsInvertible.of_sheafOfModules L
    have hdeg : (E.exteriorPower (r + 1)).degree k =
        L.degree k + (Q.exteriorPower r).degree k :=
      (degree_congr k e).trans (degree_tensorObj L (Q.exteriorPower r))
    have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
    have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q r
    have hχ := eulerChar_eq_add_of_shortExact_of_isCoherent k hS
    rw [hχ, eulerChar_eq_degree_add (k := k) L, ih Q, hdeg]
    push_cast
    ring

end LocallyFree

section Coherent

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable (k) in
/-- **The degree of a coherent module on a curve**: `deg ℱ = dim_k H⁰(X, 𝒯) + deg (det ℰ)`,
where `𝒯 = ℱ_tors` is the torsion subsheaf, `ℰ = ℱ / 𝒯` the torsion-free quotient, which on a
smooth curve is finite locally free of rank `rk ℱ`
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_torsionQuotient`),
`det ℰ = ⋀^{rk ℱ} ℰ` and the degree of a line bundle is
`AlgebraicGeometry.Scheme.Modules.degree`. For a line bundle this is its degree
(`AlgebraicGeometry.Scheme.Modules.coherentDegree_eq_degree`).

The value is meaningful for coherent modules on smooth proper curves.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`,
`theorem-riemann-roch-coherent-serre-duality`) -/
noncomputable def coherentDegree [IrreducibleSpace X] (ℱ : X.Modules) : ℤ :=
  (torsion ℱ).finrankH k 0 + ((torsionQuotient ℱ).exteriorPower ℱ.rank).degree k

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GlobalSectionsBijective k X] [IsIntegral X]

variable (k) in
/-- **Riemann–Roch for coherent modules on a curve.** Let `X` be a smooth proper curve over `k`
with `H⁰(X, 𝒪_X) = k`, of genus `g`. For every coherent `𝒪_X`-module `ℱ`,
`χ(ℱ) = deg ℱ + rk ℱ (1 - g)`.

By additivity of `χ` on `0 ⟶ 𝒯 ⟶ ℱ ⟶ ℰ ⟶ 0`, with `χ(𝒯) = h⁰(𝒯)`
(`AlgebraicGeometry.Scheme.Modules.eulerChar_torsion`) and Riemann–Roch for the locally free
`ℰ` of rank `rk ℱ`
(`AlgebraicGeometry.Scheme.Modules.eulerChar_eq_degree_exteriorPower_add`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`, part (2),
`theorem-riemann-roch-coherent-serre-duality`) -/
theorem eulerChar_eq_coherentDegree_add (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] :
    ℱ.eulerChar k = ℱ.coherentDegree k + ℱ.rank * (1 - (arithmeticGenus k X : ℤ)) := by
  have := isLocallyNoetherian_of_smoothOfRelativeDimension_one k (X := X)
  have := isFinitePresentation_torsion k ℱ
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (torsionQuotient ℱ) :=
    isQuasicoherent_cokernel _
  have : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (torsionQuotient ℱ) :=
    isFinitePresentation_cokernel _
  have := isFiniteLocallyFreeOfRank_torsionQuotient k ℱ
  have hS : (ShortComplex.mk (torsionι ℱ) (torsionπ ℱ) (cokernel.condition _)).ShortExact :=
    shortExact_torsionShortComplex ℱ
  have hχ := eulerChar_eq_add_of_shortExact_of_isCoherent k hS
  rw [hχ, eulerChar_torsion k ℱ,
    eulerChar_eq_degree_exteriorPower_add k ℱ.rank (torsionQuotient ℱ), coherentDegree]
  ring

variable (k) in
/-- **The degree of a coherent module extends the degree of line bundles**: for an invertible
`ℒ`, `deg ℒ` in the sense of `AlgebraicGeometry.Scheme.Modules.coherentDegree` is
`AlgebraicGeometry.Scheme.Modules.degree`, as both satisfy Riemann–Roch with `rk ℒ = 1`. -/
theorem coherentDegree_eq_degree (ℒ : X.Modules) [ℒ.IsInvertible] :
    ℒ.coherentDegree k = ℒ.degree k := by
  have := IsInvertible.isQuasicoherent ℒ
  have : SheafOfModules.IsInvertible.{u, u, u} ℒ := IsInvertible.sheafOfModules_isInvertible ℒ
  have hℒ1 : ℒ.IsFiniteLocallyFreeOfRank 1 :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one ℒ).1 inferInstance
  have h := eulerChar_eq_coherentDegree_add k ℒ
  rw [rank_eq_of_isFiniteLocallyFreeOfRank (r := 1) ℒ, eulerChar_eq_degree_add (k := k) ℒ] at h
  push_cast at h
  linarith

end Coherent

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexSplit
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Relative effective Cartier divisors

Let `π : X ⟶ S` be a morphism of schemes. A closed subscheme `D ⊆ X`, given by a quasi-coherent
ideal `J`, is a *relative effective Cartier divisor on `X/S`* if `J` is invertible (`D` is an
effective Cartier divisor on `X`) and `D ⟶ S` is flat:
`AlgebraicGeometry.Scheme.IdealSheafData.IsRelativeEffectiveCartier`.

We state the criteria that the Picard framework needs:

* a locally principal closed subscheme of a flat, locally finitely presented `X/S` whose fibres
  are effective Cartier divisors is a relative effective Cartier divisor;
* on a smooth `X/S` of relative dimension `1` (the Cartier criterion), a closed subscheme which
  is finite locally free over `S` is a relative effective Cartier divisor, a relative effective
  Cartier divisor is the same as a closed subscheme which is locally quasi-finite, flat and
  locally of finite presentation over `S`, and if moreover `X/S` is proper, a relative effective
  Cartier divisor is finite locally free over `S`;
* relative effective Cartier divisors are stable under base change, and so is their line bundle.

## Main definitions

- `AlgebraicGeometry.Scheme.IdealSheafData.IsRelativeEffectiveCartier`
  (blueprint `def-pc-relative-effective-cartier`).

## Main statements

- `AlgebraicGeometry.Scheme.IdealSheafData.IsLocallyPrincipal.isInvertible_and_flat`
  (blueprint `proposition-divisors-degree-g-open-chart--1`).
- `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isFinite_and_locallyOfFinitePresentation`
  (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`, `(2) ⇒ (1)` for proper `X/S`).
- `AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat`
  (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`, `(1) ⇒ (2)`).
- `AlgebraicGeometry.Scheme.IdealSheafData.isRelativeEffectiveCartier_of_isFinite`,
  `AlgebraicGeometry.Scheme.IdealSheafData.isRelativeEffectiveCartier_iff_locallyQuasiFinite`,
  `AlgebraicGeometry.Scheme.IdealSheafData.locallyOfFinitePresentation_of_locallyQuasiFinite`
  (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`, the remaining implications).
- `AlgebraicGeometry.Scheme.IdealSheafData.IsRelativeEffectiveCartier.comap_of_isPullback`
  (blueprint `lem-pc-recd-pullback`).

## Implementation notes

The scheme-level statements are reduced, on affine charts `Spec (B ⊗[A] κ)` of the fibres, to
two purely algebraic forms of the local flatness criterion,
`Algebra.exists_notMem_isRegularPrincipal_and_flat_of_fiber` (Stacks, Tags 00MF, 046Z) and
`Algebra.exists_notMem_isRegularPrincipal_of_flat_of_fiber` (Stacks, Tag 062Y as used in 0B9D),
both in `WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

open scoped AlgebraicGeometry.Scheme.Modules

open Limits TensorProduct

/-- A closed subscheme `D ⊆ X`, with quasi-coherent ideal `J`, is a **relative effective Cartier
divisor on `X/S`** for a morphism `π : X ⟶ S` if it is an effective Cartier divisor on `X`, i.e.
`J` is invertible, and `D ⟶ S` is flat.

(Stacks, Tag 062T; blueprint: `def-pc-relative-effective-cartier`) -/
def IsRelativeEffectiveCartier (J : X.IdealSheafData) (π : X ⟶ S) : Prop :=
  J.IsInvertible ∧ Flat (J.subschemeι ≫ π)

/-- **Affine charts of a fibre product.** Given a pullback square `X' = X ×[S] T` and affine
opens `W ⊆ S`, `U ⊆ X` over `W` and `V ⊆ T` over `W`, the open subscheme of `X'` lying over `U`
and `V` is `Spec (Γ(X, U) ⊗[Γ(S, W)] Γ(T, V))`: there is an open immersion
`ι : Spec (Γ(X, U) ⊗[Γ(S, W)] Γ(T, V)) ⟶ X'` whose composites with the projections are induced
by the two inclusions into the tensor product, and whose range contains every point of `X'`
lying over `U` and `V`. -/
lemma _root_.CategoryTheory.IsPullback.exists_isOpenImmersion_spec_tensorProduct
    {X' T : Scheme.{u}} {g' : X' ⟶ X} {π' : X' ⟶ T} {π : X ⟶ S} {g : T ⟶ S}
    (h : IsPullback g' π' π g) {W : S.Opens} (hW : IsAffineOpen W) {U : X.Opens}
    (hU : IsAffineOpen U) (hUW : U ≤ π ⁻¹ᵁ W) {V : T.Opens} (hV : IsAffineOpen V)
    (hVW : V ≤ g ⁻¹ᵁ W) :
    letI := (π.appLE W U hUW).hom.toAlgebra
    letI := (g.appLE W V hVW).hom.toAlgebra
    ∃ ι : Spec (.of (Γ(X, U) ⊗[Γ(S, W)] Γ(T, V))) ⟶ X', IsOpenImmersion ι ∧
      ι ≫ g' = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        hU.fromSpec ∧
      ι ≫ π' = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
        hV.fromSpec ∧
      ∀ x' : X', g' x' ∈ U → π' x' ∈ V → x' ∈ Set.range ι := by
  let := (π.appLE W U hUW).hom.toAlgebra
  let := (g.appLE W V hVW).hom.toAlgebra
  have e₁ : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, W) Γ(X, U))) ≫ hW.fromSpec =
      hU.fromSpec ≫ π := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
    exact IsAffineOpen.SpecMap_appLE_fromSpec π hW hU hUW
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, W) Γ(T, V))) ≫ hW.fromSpec =
      hV.fromSpec ≫ g := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
    exact IsAffineOpen.SpecMap_appLE_fromSpec g hW hV hVW
  have : IsOpenImmersion (pullback.map _ _ π g hU.fromSpec hV.fromSpec hW.fromSpec e₁ e₂) :=
    Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ e₁ e₂
  refine ⟨(pullbackSpecIso Γ(S, W) Γ(X, U) Γ(T, V)).inv ≫
    pullback.map _ _ π g hU.fromSpec hV.fromSpec hW.fromSpec e₁ e₂ ≫ h.isoPullback.inv,
    inferInstance, ?_, ?_, fun x' hxU hxV ↦ ?_⟩
  · rw [Category.assoc, Category.assoc, h.isoPullback_inv_fst, pullback.lift_fst,
      ← Category.assoc, pullbackSpecIso_inv_fst]
  · rw [Category.assoc, Category.assoc, h.isoPullback_inv_snd, pullback.lift_snd,
      ← Category.assoc, pullbackSpecIso_inv_snd]
    rfl
  · obtain ⟨y, hy⟩ : h.isoPullback.hom x' ∈
        Set.range (pullback.map _ _ π g hU.fromSpec hV.fromSpec hW.fromSpec e₁ e₂) := by
      rw [Scheme.Pullback.range_map, IsAffineOpen.range_fromSpec, IsAffineOpen.range_fromSpec]
      refine ⟨?_, ?_⟩
      · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
        exact hxU
      · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h.isoPullback_hom_snd]
        exact hxV
    refine ⟨(pullbackSpecIso _ _ _).hom y, ?_⟩
    simp [← Scheme.Hom.comp_apply, hy]

/-- An invertible ideal is generated by a non-zerodivisor on arbitrarily small affine open
neighbourhoods of any point. -/
lemma IsInvertible.exists_isRegularPrincipal_le {J : X.IdealSheafData} (hJ : J.IsInvertible)
    {x : X} {O : X.Opens} (hx : x ∈ O) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ O ∧ (J.ideal U).IsRegularPrincipal := by
  obtain ⟨U₀, hxU₀, hU₀⟩ := hJ x
  obtain ⟨V, hVaff, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U₀.1 ⊓ O) (x := x) ⟨hxU₀, hx⟩
  refine ⟨⟨V, hVaff⟩, hxV, hVU.trans inf_le_right, ?_⟩
  rw [← J.map_ideal (U := ⟨V, hVaff⟩) (V := U₀) (hVU.trans inf_le_left)]
  exact hU₀.map_of_flat (Scheme.Hom.flat_appLE (𝟙 X) U₀.2 hVaff (hVU.trans inf_le_left))

/-- If the closed subscheme `D = V(J)` is flat over `S`, then for affine opens `W ⊆ S` and
`U ⊆ X` over `W`, the ring `Γ(D, D ∩ U) = Γ(X, U) ⧸ J(U)` is flat over `Γ(S, W)`. -/
lemma flat_app_subschemeι_comp_appLE {π : X ⟶ S} {J : X.IdealSheafData}
    (hflat : Flat (J.subschemeι ≫ π)) (W : S.affineOpens) (U : X.affineOpens)
    (hUW : U.1 ≤ π ⁻¹ᵁ W.1) :
    ((J.subschemeι.app U.1).hom.comp (π.appLE W U hUW).hom).Flat := by
  have := (J.subschemeι ≫ π).flat_appLE W.2 (U.2.preimage J.subschemeι)
    (J.subschemeι.preimage_mono hUW)
  rwa [← Scheme.Hom.appLE_comp_appLE _ _ _ U.1 _ hUW le_rfl, CommRingCat.hom_comp,
    ← Scheme.Hom.app_eq_appLE] at this

/-- **Base change of a flat closed subscheme.** In a pullback square `X' = X ×[S] T`, the closed
subscheme `V(J.comap g') ⊆ X'` is the base change of `V(J) ⟶ S` along `T ⟶ S`; in particular it
is flat over `T` if `V(J)` is flat over `S`. -/
theorem flat_comap_subschemeι_comp_of_isPullback {π : X ⟶ S} {J : X.IdealSheafData}
    (hflat : Flat (J.subschemeι ≫ π)) {X' T : Scheme.{u}} {g' : X' ⟶ X} {π' : X' ⟶ T}
    {g : T ⟶ S} (h : IsPullback g' π' π g) : Flat ((J.comap g').subschemeι ≫ π') := by
  have sq : IsPullback (pullback.snd g' J.subschemeι) (pullback.fst g' J.subschemeι ≫ π')
      (J.subschemeι ≫ π) g := (IsPullback.of_hasPullback g' J.subschemeι).flip.paste_vert h
  have := MorphismProperty.of_isPullback (P := @Flat) sq hflat
  rw [← comapIso_hom_fst, Category.assoc]
  infer_instance

/-- **Base change of an effective Cartier divisor which is flat over the base.** In a pullback
square `X' = X ×[S] T`, if `J` is invertible and `V(J)` is flat over `S`, then `J.comap g'` is
invertible. Locally `J = (f)` on `Spec B ⊆ X` over `Spec A ⊆ S`, with `f` a non-zerodivisor and
`B ⧸ (f)` flat over `A`; on the chart `Spec (B ⊗[A] A')` of `X'` the pulled back ideal is
generated by `f ⊗ 1`, a non-zerodivisor by
`Algebra.TensorProduct.includeLeftRingHom_mem_nonZeroDivisors_of_flat`. -/
theorem IsInvertible.comap_of_isPullback {π : X ⟶ S} {J : X.IdealSheafData}
    (hJ : J.IsInvertible) (hflat : Flat (J.subschemeι ≫ π)) {X' T : Scheme.{u}} {g' : X' ⟶ X}
    {π' : X' ⟶ T} {g : T ⟶ S} (h : IsPullback g' π' π g) : (J.comap g').IsInvertible := by
  have key (x' : X') : ∃ (R : CommRingCat.{u}) (ι : Spec R ⟶ X'), IsOpenImmersion ι ∧
      x' ∈ Set.range ι ∧ (J.comap (ι ≫ g')).IsInvertible := by
    obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (x := π (g' x')) (U := ⊤) trivial
    obtain ⟨U, hxU, hUW, f, hf, hJU⟩ := hJ.exists_isRegularPrincipal_le (O := π ⁻¹ᵁ W) hsW
    have htW : π' x' ∈ g ⁻¹ᵁ W := by
      rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]
      exact hsW
    obtain ⟨V, hV, htV, hVW⟩ := exists_isAffineOpen_mem_and_subset htW
    obtain ⟨ι, hι, hιg, -, hrange⟩ :=
      h.exists_isOpenImmersion_spec_tensorProduct hW U.2 hUW hV hVW
    let := (π.appLE W U hUW).hom.toAlgebra
    let := (g.appLE W V hVW).hom.toAlgebra
    refine ⟨_, ι, hι, hrange x' hxU htV, ?_⟩
    rw [hιg]
    refine IsInvertible.of_specMap_ofHom_fromSpec U _ ?_
    rw [hJU, Ideal.map_span, Set.image_singleton]
    refine Ideal.isRegularPrincipal_span_singleton
      (Algebra.TensorProduct.includeLeftRingHom_mem_nonZeroDivisors_of_flat
        (J.subschemeι.app U.1).hom (J.subschemeι_app_surjective U) ?_ ?_ hf)
    · rw [ker_subschemeι_app, hJU]
    · rw [RingHom.algebraMap_toAlgebra]
      exact flat_app_subschemeι_comp_appLE hflat ⟨W, hW⟩ U hUW
  choose R ι hι hx' hinv using key
  have : ∀ x', IsOpenImmersion (ι x') := hι
  refine IsInvertible.of_iSup_opensRange_eq_top ι ?_ fun x' ↦ ?_
  · exact eq_top_iff.mpr fun x' _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x', hx' x'⟩
  · rw [← comap_comp]
    exact hinv x'

/-- On `Spec R`, if an invertible ideal sheaf has global sections given by an ideal `I` of `R`,
then `I` is locally generated by a non-zerodivisor: around every prime `P` there is `g ∉ P` such
that `I R_g` is generated by a non-zerodivisor. -/
lemma IsInvertible.exists_isRegularPrincipal_map_localizationAway {R : Type u} [CommRing R]
    {J : (Spec (.of R)).IdealSheafData} (hJ : J.IsInvertible) {I : Ideal R}
    (hI : J.ideal ⟨⊤, isAffineOpen_top _⟩ = I.map (Scheme.ΓSpecIso (.of R)).inv.hom)
    (P : Ideal R) [P.IsPrime] :
    ∃ g ∉ P, (I.map (algebraMap R (Localization.Away g))).IsRegularPrincipal := by
  let P' : Spec (.of R) := ⟨P, inferInstance⟩
  obtain ⟨V, hPV, hV⟩ := hJ P'
  obtain ⟨_, ⟨g, rfl⟩, hPg, hgV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hPV V.1.isOpen
  let g₀ := (Scheme.ΓSpecIso (.of R)).inv g
  let D := (Spec (.of R)).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) g₀
  have hD : (D : (Spec (.of R)).Opens) = PrimeSpectrum.basicOpen g :=
    basicOpen_eq_of_affine g
  have hDV : D ≤ V := by
    intro x hx
    rw [hD] at hx
    exact hgV hx
  have hJD : (J.ideal D).IsRegularPrincipal := by
    rw [← J.map_ideal hDV]
    exact hV.map_of_flat (Scheme.Hom.flat_appLE (𝟙 _) V.2 D.2 hDV)
  refine ⟨g, hPg, ?_⟩
  have hDtop : D.1 ≤ (⟨⊤, isAffineOpen_top _⟩ : (Spec (.of R)).affineOpens).1 := le_top
  let ρ := ((Spec (.of R)).presheaf.map (homOfLE hDtop).op).hom
  let φ := ρ.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := φ.toAlgebra
  have : IsLocalization.Away g Γ(Spec (.of R), D) := by
    let := ρ.toAlgebra
    have := (isAffineOpen_top (Spec (.of R))).isLocalization_of_eq_basicOpen g₀
      (homOfLE hDtop) rfl
    have := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers g₀)
      Γ(Spec (.of R), D) (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
    have hg : (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv g₀ = g :=
      Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of R)) g
    rw [Submonoid.map_powers, hg] at this
    exact this
  have hφ : I.map φ = J.ideal D := by
    rw [← J.map_ideal hDtop, hI, Ideal.map_map]
    rfl
  let e := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(Spec (.of R), D)
  have he : e.symm.toRingEquiv.toRingHom.comp φ = algebraMap R (Localization.Away g) :=
    e.symm.toAlgHom.comp_algebraMap
  rw [← hφ] at hJD
  have := hJD.map_of_bijective (f := e.symm.toRingEquiv.toRingHom) e.symm.toRingEquiv.bijective
  rwa [Ideal.map_map, he] at this

/-- **The fibre of a closed subscheme on an affine chart.** Let `W ⊆ S` be an affine open
over which `Spec κ(s)` lies and `U ⊆ X` an affine open over `W`; write `A = Γ(S, W)`,
`B = Γ(X, U)` and `K = Γ(Spec κ(s), ⊤)`. If the restriction of `J` to the fibre `X_s` is
invertible, then the extension of `J(U)` to the chart `B ⊗[A] K` of `X_s` is locally generated
by a non-zerodivisor. -/
lemma exists_isRegularPrincipal_map_tensorProduct_of_isInvertible_comap_fiberι (π : X ⟶ S)
    {J : X.IdealSheafData} (s : S) (hJs : (J.comap (π.fiberι s)).IsInvertible) {W : S.Opens}
    (hW : IsAffineOpen W) (hsW : ⊤ ≤ S.fromSpecResidueField s ⁻¹ᵁ W) (U : X.affineOpens)
    (hUW : U.1 ≤ π ⁻¹ᵁ W) :
    letI := (π.appLE W U hUW).hom.toAlgebra
    letI := ((S.fromSpecResidueField s).appLE W ⊤ hsW).hom.toAlgebra
    ∀ P : Ideal (Γ(X, U) ⊗[Γ(S, W)] Γ(Spec (S.residueField s), ⊤)), P.IsPrime →
      ∃ g ∉ P, (((J.ideal U).map Algebra.TensorProduct.includeLeftRingHom).map
        (algebraMap (Γ(X, U) ⊗[Γ(S, W)] Γ(Spec (S.residueField s), ⊤))
          (Localization.Away g))).IsRegularPrincipal := by
  intro P _
  obtain ⟨ι, hι, hιg, -, -⟩ := IsPullback.exists_isOpenImmersion_spec_tensorProduct
    (IsPullback.of_hasPullback π (S.fromSpecResidueField s)) hW U.2 hUW (isAffineOpen_top _) hsW
  have : (J.comap (ι ≫ pullback.fst π (S.fromSpecResidueField s))).IsInvertible := by
    rw [comap_comp]
    exact @IsInvertible.comap_of_isOpenImmersion _ _ _ hJs ι hι
  rw [hιg] at this
  exact this.exists_isRegularPrincipal_map_localizationAway
    (ideal_top_comap_specMap_ofHom_fromSpec J U _) P

/-- In the situation of `exists_isRegularPrincipal_map_tensorProduct_of_isInvertible_comap_fiberι`,
the kernel of `Γ(S, W) → Γ(Spec κ(s), ⊤)` is the prime of `s`, i.e. the contraction of the
prime of any point of `U` over `s`. -/
lemma ker_appLE_fromSpecResidueField (π : X ⟶ S) (s : S) {W : S.Opens} (hW : IsAffineOpen W)
    (hsW : ⊤ ≤ S.fromSpecResidueField s ⁻¹ᵁ W) {U : X.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ π ⁻¹ᵁ W) (q : Spec Γ(X, U)) (hq : π (hU.fromSpec q) = s) :
    RingHom.ker ((S.fromSpecResidueField s).appLE W ⊤ hsW).hom =
      q.asIdeal.comap (π.appLE W U hUW).hom := by
  let := (Modules.isField_Γ_Spec_residueField s).toField
  let pt : Spec Γ(Spec (S.residueField s), ⊤) := ⟨⊥, Ideal.isPrime_bot⟩
  have e₁ : hW.fromSpec (Spec.map ((S.fromSpecResidueField s).appLE W ⊤ hsW) pt) = s := by
    rw [← Scheme.Hom.comp_apply, IsAffineOpen.SpecMap_appLE_fromSpec _ hW (isAffineOpen_top _),
      Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have e₂ : hW.fromSpec (Spec.map (π.appLE W U hUW) q) = s := by
    rw [← Scheme.Hom.comp_apply, IsAffineOpen.SpecMap_appLE_fromSpec _ hW hU, Scheme.Hom.comp_apply,
      hq]
  have := congrArg PrimeSpectrum.asIdeal (hW.fromSpec.isOpenEmbedding.injective (e₁.trans e₂.symm))
  rw [RingHom.ker_eq_comap_bot]
  exact this

/-- **Locally principal closed subschemes are of finite presentation.** If `J` is locally
principal and `π` is locally of finite presentation, then so is `V(J) ⟶ S`: locally
`V(J) = Spec (B ⧸ (f))` with `(f)` finitely generated. -/
theorem IsLocallyPrincipal.locallyOfFinitePresentation_subschemeι_comp (π : X ⟶ S)
    [LocallyOfFinitePresentation π] {J : X.IdealSheafData} (hJ : J.IsLocallyPrincipal) :
    LocallyOfFinitePresentation (J.subschemeι ≫ π) := by
  have : LocallyOfFinitePresentation J.subschemeι := by
    rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
      (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.finitePresentation_holdsForLocalizationAway).left]
    intro d
    obtain ⟨U, hU, a, ha⟩ := hJ (J.subschemeι d)
    refine ⟨U, ⟨_, U.2.preimage J.subschemeι⟩, hU, le_rfl, ?_⟩
    rw [← Scheme.Hom.app_eq_appLE]
    refine RingHom.FinitePresentation.of_surjective _ (J.subschemeι_app_surjective U) ?_
    rw [ker_subschemeι_app, ha]
    exact ⟨{a}, by simp⟩
  infer_instance

/-- **An effective Cartier divisor on a smooth curve over a field is quasi-finite.** Locally the
divisor is `Spec (B ⧸ (f))` with `f` a non-zerodivisor of the finitely generated `K`-algebra `B`
of dimension at most one, so `B ⧸ (f)` has dimension zero. -/
theorem IsInvertible.locallyQuasiFinite_subschemeι_comp_of_field {K : Type u} [Field K]
    {F : Scheme.{u}} (p : F ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
    {J : F.IdealSheafData} (hJ : J.IsInvertible) : LocallyQuasiFinite (J.subschemeι ≫ p) := by
  have := SmoothOfRelativeDimension.smooth 1 p
  have hdim := topologicalKrullDim_le_of_smoothOfRelativeDimension p 1
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyQuasiFinite)
    (RingHom.QuasiFinite.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.QuasiFinite.holdsForLocalizationAway).left]
  intro d
  obtain ⟨U, hU, f, hf, hJU⟩ := hJ (J.subschemeι d)
  refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨_, U.2.preimage J.subschemeι⟩, hU, le_top, ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ U.1 _ le_top le_rfl, CommRingCat.hom_comp,
    ← Scheme.Hom.app_eq_appLE]
  refine RingHom.QuasiFinite.comp_of_ringKrullDim_le_one ?_ _ ?_ ?_ _
    (J.subschemeι_app_surjective U) hf ?_
  · exact MulEquiv.isField (Field.toIsField K)
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  · exact HasRingHomProperty.appLE (P := @LocallyOfFiniteType) p inferInstance
      ⟨⊤, isAffineOpen_top _⟩ U le_top
  · rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      U.2.isoSpec.hom.homeomorph.isHomeomorph).symm.le.trans
        ((topologicalKrullDim_subspace_le F U).trans (by exact_mod_cast hdim))
  · rw [← RingHom.mem_ker, ker_subschemeι_app, hJU]
    exact Ideal.subset_span rfl

/-- **A relative effective Cartier divisor on a smooth relative curve is locally
quasi-finite.** Its fibre over `s : S` is the effective Cartier divisor
`J.comap (π.fiberι s)` of the smooth curve `π.fiber s` over `κ(s)`
(`IsInvertible.comap_of_isPullback`), which is quasi-finite over `κ(s)`. -/
theorem IsInvertible.locallyQuasiFinite_subschemeι_comp (π : X ⟶ S)
    [SmoothOfRelativeDimension 1 π] {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (hflat : Flat (J.subschemeι ≫ π)) : LocallyQuasiFinite (J.subschemeι ≫ π) := by
  refine LocallyQuasiFinite.of_fiberToSpecResidueField _ fun s ↦ ?_
  have h := IsPullback.of_hasPullback π (S.fromSpecResidueField s)
  have sq : IsPullback (pullback.snd (pullback.fst π (S.fromSpecResidueField s)) J.subschemeι)
      (pullback.fst (pullback.fst π (S.fromSpecResidueField s)) J.subschemeι ≫
        pullback.snd π (S.fromSpecResidueField s))
      (J.subschemeι ≫ π) (S.fromSpecResidueField s) :=
    (IsPullback.of_hasPullback _ J.subschemeι).flip.paste_vert h
  have := (hJ.comap_of_isPullback hflat h).locallyQuasiFinite_subschemeι_comp_of_field
    (K := S.residueField s) (pullback.snd π (S.fromSpecResidueField s))
  have H : LocallyQuasiFinite (pullback.fst (pullback.fst π (S.fromSpecResidueField s))
      J.subschemeι ≫ pullback.snd π (S.fromSpecResidueField s)) := by
    rw [← comapIso_inv_subschemeι, Category.assoc]
    infer_instance
  rw [Scheme.Hom.fiberToSpecResidueField, ← sq.isoPullback_inv_snd]
  have : IsOpenImmersion sq.isoPullback.inv := inferInstance
  have H' : LocallyQuasiFinite sq.isoPullback.inv := inferInstance
  exact MorphismProperty.comp_mem @LocallyQuasiFinite _ _ H' H

/-- A locally principal ideal is principal on arbitrarily small affine open neighbourhoods of
any point. -/
lemma IsLocallyPrincipal.exists_isPrincipal_le {J : X.IdealSheafData}
    (hJ : J.IsLocallyPrincipal) {x : X} {O : X.Opens} (hx : x ∈ O) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ O ∧ (J.ideal U).IsPrincipal := by
  obtain ⟨U₀, hxU₀, a, ha⟩ := hJ x
  obtain ⟨V, hVaff, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U₀.1 ⊓ O) (x := x) ⟨hxU₀, hx⟩
  refine ⟨⟨V, hVaff⟩, hxV, hVU.trans inf_le_right,
    ⟨(X.presheaf.map (homOfLE (hVU.trans inf_le_left)).op).hom a, ?_⟩⟩
  rw [← J.map_ideal (U := ⟨V, hVaff⟩) (V := U₀) (hVU.trans inf_le_left), ha,
    Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]
  rfl

/-- **On a smooth curve over a field, a quasi-finite closed subscheme is a divisor.** Let
`p : F ⟶ Spec K` be smooth of relative dimension `1` and let `V(J) ⊆ F` be locally quasi-finite
over `K`, i.e. discrete. At a point `x ∈ V(J)` the local ring `𝒪_{F,x}` is regular of dimension
at most one, hence a principal ideal domain, and the stalk of `J` at `x` is nonzero: otherwise
`V(J)` would contain an open neighbourhood of `x`, which would be a discrete nonempty open
subscheme of `F`, contradicting that `F` has dimension one everywhere. So `J_x` is generated by
a nonzero element, and this spreads out to a neighbourhood of `x`
(`Ideal.exists_notMem_isRegularPrincipal_map_away`).

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, the fibrewise step of `(1) ⇒ (2)`) -/
theorem isInvertible_of_locallyQuasiFinite_of_field {K : Type u} [Field K] {F : Scheme.{u}}
    (p : F ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p] {J : F.IdealSheafData}
    [LocallyQuasiFinite (J.subschemeι ≫ p)] : J.IsInvertible := by
  have := SmoothOfRelativeDimension.smooth 1 p
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsRegular F := IsRegular.of_smooth p
  have hdim := topologicalKrullDim_le_of_smoothOfRelativeDimension p 1
  have hdisc : DiscreteTopology J.subscheme := by
    rw [← isDiscrete_univ_iff]
    rcases isEmpty_or_nonempty J.subscheme with h | ⟨⟨d⟩⟩
    · rw [Set.univ_eq_empty_iff.mpr h]
      exact ⟨inferInstance⟩
    · convert (J.subschemeι ≫ p).isDiscrete_preimage_singleton ((J.subschemeι ≫ p) d)
      ext e
      simp only [Set.mem_univ, Set.mem_preimage, Set.mem_singleton_iff, true_iff]
      exact Subsingleton.elim _ _
  intro x
  by_cases hx : x ∈ J.support
  swap
  · obtain ⟨U, hU, hxU, hUs⟩ := exists_isAffineOpen_mem_and_subset
      (U := ⟨(J.support : Set F)ᶜ, J.support.isClosed.isOpen_compl⟩) hx
    refine ⟨⟨U, hU⟩, hxU, 1, one_mem _, ?_⟩
    rw [Ideal.span_singleton_one]
    exact J.ideal_eq_top_of_disjoint_support (Set.subset_compl_iff_disjoint_right.mp hUs)
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  let xU : U := ⟨x, hxU⟩
  set q := hU.primeIdealOf xU with hq
  let := TopCat.Presheaf.algebra_section_stalk F.presheaf xU
  have := hU.isLocalization_stalk xU
  have : IsNoetherianRing Γ(F, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨I, hIdef⟩ : ∃ I, I = J.ideal ⟨U, hU⟩ := ⟨_, rfl⟩
  have hmem (f : Γ(F, U)) : x ∈ F.basicOpen f ↔ f ∉ q.asIdeal := by
    have e : hU.fromSpec q = x := hU.fromSpec_primeIdealOf xU
    have h : q ∈ hU.fromSpec ⁻¹ᵁ F.basicOpen f ↔ q ∈ PrimeSpectrum.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]
    rw [← e]
    exact h
  -- the stalk of `J` at `x` is nonzero, as `V(J)` is discrete while `X` has no isolated points
  have hI0 : I.map (algebraMap Γ(F, U) (F.presheaf.stalk x)) ≠ ⊥ := by
    intro h0
    have hk (a : Γ(F, U)) (ha : a ∈ I) : ∃ u ∉ q.asIdeal, u * a = 0 := by
      have : algebraMap _ (F.presheaf.stalk x) a = 0 := by
        rw [← Ideal.mem_bot, ← h0]
        exact Ideal.mem_map_of_mem _ ha
      obtain ⟨⟨u, hu⟩, h⟩ := (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl _ a).1 this
      exact ⟨u, hu, h⟩
    obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
    have hk' (a : Γ(F, U)) (ha : a ∈ S) : ∃ u ∉ q.asIdeal, u * a = 0 := by
      refine hk a ?_
      rw [← hS]
      exact Ideal.subset_span ha
    choose! u hu hu' using hk'
    have hg : ∏ a ∈ S, u a ∉ q.asIdeal := q.asIdeal.primeCompl.prod_mem fun a ha ↦ hu a ha
    have hgI (a : Γ(F, U)) (ha : a ∈ I) : (∏ a ∈ S, u a) * a = 0 := by
      rw [← hS] at ha
      refine Ideal.mem_bot.1 (Ideal.mul_mem_of_mem_span_of_forall _ ⊥ _ (fun b hb ↦ ?_) ha)
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem u hb
      rw [Ideal.mem_bot, hc, mul_comm (u b) c, mul_assoc, hu' b hb, mul_zero]
    let Z := F.basicOpen (∏ a ∈ S, u a)
    have hZ (y : F) (hy : y ∈ Z) : y ∈ Set.range J.subschemeι := by
      rw [range_subschemeι, SetLike.mem_coe,
        mem_support_iff_of_mem (U := ⟨U, hU⟩) (F.basicOpen_le _ hy), Scheme.mem_zeroLocus_iff,
        ← hIdef]
      intro a ha hya
      have : y ∈ F.basicOpen ((∏ a ∈ S, u a) * a) := by
        rw [Scheme.basicOpen_mul]
        exact ⟨hy, hya⟩
      rw [hgI a ha, Scheme.basicOpen_zero] at this
      exact this
    have : DiscreteTopology Z := by
      refine discreteTopology_iff_isOpen_singleton.mpr fun z ↦ ?_
      obtain ⟨d, hd⟩ := hZ z.1 z.2
      obtain ⟨t, ht, htd⟩ := J.subschemeι.isEmbedding.isOpen_iff.mp (isOpen_discrete {d})
      refine isOpen_induced_iff.mpr ⟨t, ht, Set.ext fun w ↦ ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩⟩
      · obtain ⟨d', hd'⟩ := hZ w.1 w.2
        have : d' ∈ J.subschemeι ⁻¹' t := by
          rw [Set.mem_preimage, hd']
          exact hw
        rw [htd, Set.mem_singleton_iff] at this
        rw [Set.mem_singleton_iff]
        exact Subtype.ext (hd'.symm.trans (this ▸ hd))
      · rw [Set.mem_singleton_iff] at hw
        have : d ∈ J.subschemeι ⁻¹' t := htd ▸ Set.mem_singleton d
        rw [Set.mem_preimage, hd] at this
        rw [hw]
        exact this
    have : Nonempty Z := ⟨⟨x, (hmem _).mpr hg⟩⟩
    have : SmoothOfRelativeDimension 1 (Z.ι ≫ p) :=
      (zero_add 1) ▸ (inferInstance : SmoothOfRelativeDimension (0 + 1) (Z.ι ≫ p))
    have h1 := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Z.ι ≫ p) 1
    have h0 := topologicalKrullDim_zero_of_discreteTopology Z
    rw [h1] at h0
    exact absurd h0 (by norm_num)
  -- the local ring at `x` is a discrete valuation ring
  have : IsPrincipalIdealRing (F.presheaf.stalk x) := by
    refine ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain _).out 6 1).mp ?_
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (F.presheaf.stalk x)).mp
      inferInstance
    have h' := (ringKrullDim_stalk_le_topologicalKrullDim x).trans hdim
    rw [← h] at h'
    exact_mod_cast h'
  obtain ⟨t, ht⟩ := (IsPrincipalIdealRing.principal
    (I.map (algebraMap Γ(F, U) (F.presheaf.stalk x)))).principal
  obtain ⟨g, hgq, hg⟩ := Ideal.exists_notMem_isRegularPrincipal_map_away q.asIdeal
    (F.presheaf.stalk x) I (t := t) (by rw [ht, Ideal.submodule_span_eq])
    fun ht0 ↦ hI0 (by rw [ht, Ideal.submodule_span_eq, ht0, Ideal.span_singleton_eq_bot])
  let D := F.affineBasicOpen (U := ⟨U, hU⟩) g
  have hDU : D.1 ≤ U := F.basicOpen_le g
  let := (F.presheaf.map (homOfLE hDU).op).hom.toAlgebra
  have : IsLocalization.Away g Γ(F, D) := hU.isLocalization_of_eq_basicOpen g (homOfLE hDU) rfl
  refine ⟨D, (hmem g).mpr hgq, ?_⟩
  rw [← J.map_ideal (V := ⟨U, hU⟩) hDU, ← hIdef]
  exact hg Γ(F, D)

/-- If `V(J)` is locally of finite presentation over `S`, then for affine opens `W ⊆ S` and
`U ⊆ X` over `W`, the ring `Γ(X, U) ⧸ J(U)` is of finite presentation over `Γ(S, W)`. -/
lemma finitePresentation_app_subschemeι_comp_appLE {π : X ⟶ S} {J : X.IdealSheafData}
    (hlfp : LocallyOfFinitePresentation (J.subschemeι ≫ π)) (W : S.affineOpens)
    (U : X.affineOpens) (hUW : U.1 ≤ π ⁻¹ᵁ W.1) :
    ((J.subschemeι.app U.1).hom.comp (π.appLE W U hUW).hom).FinitePresentation := by
  have := HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) _ hlfp W
    ⟨_, U.2.preimage J.subschemeι⟩ (J.subschemeι.preimage_mono hUW)
  rwa [← Scheme.Hom.appLE_comp_appLE _ _ _ U.1 _ hUW le_rfl, CommRingCat.hom_comp,
    ← Scheme.Hom.app_eq_appLE] at this

/-- **Base change of a locally quasi-finite closed subscheme.** In a pullback square
`X' = X ×[S] T`, if `V(J)` is locally quasi-finite over `S`, then `V(J.comap g')` is locally
quasi-finite over `T`. -/
theorem locallyQuasiFinite_comap_subschemeι_comp_of_isPullback {π : X ⟶ S}
    {J : X.IdealSheafData} (hqf : LocallyQuasiFinite (J.subschemeι ≫ π)) {X' T : Scheme.{u}}
    {g' : X' ⟶ X} {π' : X' ⟶ T} {g : T ⟶ S} (h : IsPullback g' π' π g) :
    LocallyQuasiFinite ((J.comap g').subschemeι ≫ π') := by
  have sq : IsPullback (pullback.snd g' J.subschemeι) (pullback.fst g' J.subschemeι ≫ π')
      (J.subschemeι ≫ π) g := (IsPullback.of_hasPullback g' J.subschemeι).flip.paste_vert h
  have H := MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) sq hqf
  have H' : LocallyQuasiFinite (J.comapIso g').hom := inferInstance
  rw [← comapIso_hom_fst, Category.assoc]
  exact MorphismProperty.comp_mem @LocallyQuasiFinite _ _ H' H

/-- **Closed subschemes of a smooth relative curve which are quasi-finite, flat and of finite
presentation over the base are divisors.** On an affine chart `Spec B ⊆ X` over
`Spec A ⊆ S`, the ideal `I = J(U)` has `B ⧸ I` flat and of finite presentation over `A`, and its
fibre over each point `s` is an effective Cartier divisor on the smooth curve `X_s`
(`isInvertible_of_locallyQuasiFinite_of_field`), so `I` is locally generated by a
non-zerodivisor by `Algebra.exists_notMem_isRegularPrincipal_of_flat_of_fiber`.

(Stacks, Tag 0B9D; blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, `(3) ⇒ (2)`) -/
theorem isInvertible_of_locallyQuasiFinite_of_flat (π : X ⟶ S) [SmoothOfRelativeDimension 1 π]
    {J : X.IdealSheafData} (hqf : LocallyQuasiFinite (J.subschemeι ≫ π))
    (hflat : Flat (J.subschemeι ≫ π)) (hlfp : LocallyOfFinitePresentation (J.subschemeι ≫ π)) :
    J.IsInvertible := by
  have := SmoothOfRelativeDimension.smooth 1 π
  intro x
  obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (x := π x) (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset (U := π ⁻¹ᵁ W) (x := x) hsW
  obtain ⟨q, hq⟩ : x ∈ Set.range hU.fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    exact hxU
  have hsW' : ⊤ ≤ S.fromSpecResidueField (π x) ⁻¹ᵁ W := fun y _ ↦ by
    rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
    exact hsW
  have hfib : (J.comap (π.fiberι (π x))).IsInvertible := by
    have := locallyQuasiFinite_comap_subschemeι_comp_of_isPullback hqf
      (IsPullback.of_hasPullback π (S.fromSpecResidueField (π x)))
    exact @isInvertible_of_locallyQuasiFinite_of_field (S.residueField (π x)) _ _
      (pullback.snd π (S.fromSpecResidueField (π x))) _
      (J.comap (pullback.fst π (S.fromSpecResidueField (π x)))) this
  let := (π.appLE W U hUW).hom.toAlgebra
  let := ((S.fromSpecResidueField (π x)).appLE W ⊤ hsW').hom.toAlgebra
  have : Module.Flat Γ(S, W) Γ(X, U) := π.flat_appLE hW hU hUW
  have : Algebra.FinitePresentation Γ(S, W) Γ(X, U) :=
    HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) π inferInstance ⟨W, hW⟩
      ⟨U, hU⟩ hUW
  have := q.isPrime
  obtain ⟨g, hgq, hg⟩ := Algebra.exists_notMem_isRegularPrincipal_of_flat_of_fiber
    (Modules.isField_Γ_Spec_residueField _) (J.subschemeι.app U).hom
    (J.subschemeι_app_surjective ⟨U, hU⟩)
    (flat_app_subschemeι_comp_appLE hflat ⟨W, hW⟩ ⟨U, hU⟩ hUW)
    (finitePresentation_app_subschemeι_comp_appLE hlfp ⟨W, hW⟩ ⟨U, hU⟩ hUW) q.asIdeal
    (ker_appLE_fromSpecResidueField π _ hW hsW' hU hUW q (by rw [hq]))
    (by
      rw [ker_subschemeι_app J ⟨U, hU⟩]
      exact exists_isRegularPrincipal_map_tensorProduct_of_isInvertible_comap_fiberι π _ hfib
        hW hsW' ⟨U, hU⟩ hUW)
  let D := X.affineBasicOpen (U := ⟨U, hU⟩) g
  have hDU : D.1 ≤ U := X.basicOpen_le g
  let := (X.presheaf.map (homOfLE hDU).op).hom.toAlgebra
  have : IsLocalization.Away g Γ(X, D) := hU.isLocalization_of_eq_basicOpen g (homOfLE hDU) rfl
  refine ⟨D, ?_, ?_⟩
  · have : q ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hgq
    rw [← hq]
    exact this
  · rw [← J.map_ideal (V := ⟨U, hU⟩) hDU, ← ker_subschemeι_app J ⟨U, hU⟩]
    exact hg Γ(X, D)

/-- **Effective Cartier divisors from local equations.** Let `π : X ⟶ S` be flat and locally of
finite presentation and let `D ⊆ X` be a locally principal closed subscheme, with ideal `J`. If
every fibre `D_s ⊆ X_s` is an effective Cartier divisor, then `D` is a relative effective
Cartier divisor on `X/S`: `J` is invertible and `D ⟶ S` is flat.

(Stacks, Tag 062Y; blueprint: `proposition-divisors-degree-g-open-chart--1`) -/
theorem IsLocallyPrincipal.isInvertible_and_flat (π : X ⟶ S) [Flat π]
    [LocallyOfFinitePresentation π] {J : X.IdealSheafData} (hJ : J.IsLocallyPrincipal)
    (hfib : ∀ s : S, (J.comap (π.fiberι s)).IsInvertible) :
    J.IsInvertible ∧ Flat (J.subschemeι ≫ π) := by
  have key (x : X) : ∃ (W : S.affineOpens) (V : X.affineOpens) (hVW : V.1 ≤ π ⁻¹ᵁ W.1),
      x ∈ V.1 ∧ (J.ideal V).IsRegularPrincipal ∧
        ((J.subschemeι.app V.1).hom.comp (π.appLE W V hVW).hom).Flat := by
    obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (x := π x) (U := ⊤) trivial
    obtain ⟨U, hxU, hUW, hJU⟩ := hJ.exists_isPrincipal_le (O := π ⁻¹ᵁ W) hsW
    have hU : IsAffineOpen U.1 := U.2
    obtain ⟨q, hq⟩ : x ∈ Set.range hU.fromSpec := by
      rw [IsAffineOpen.range_fromSpec]
      exact hxU
    have hsW' : ⊤ ≤ S.fromSpecResidueField (π x) ⁻¹ᵁ W := fun y _ ↦ by
      rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
      exact hsW
    let := (π.appLE W U hUW).hom.toAlgebra
    let := ((S.fromSpecResidueField (π x)).appLE W ⊤ hsW').hom.toAlgebra
    have : Module.Flat Γ(S, W) Γ(X, U) := π.flat_appLE hW U.2 hUW
    have : Algebra.FinitePresentation Γ(S, W) Γ(X, U) :=
      HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) π inferInstance ⟨W, hW⟩ U hUW
    have := q.isPrime
    obtain ⟨g, hgq, hg⟩ := Algebra.exists_notMem_isRegularPrincipal_and_flat_of_fiber
      (Modules.isField_Γ_Spec_residueField _) (J.ideal U) hJU q.asIdeal
      (ker_appLE_fromSpecResidueField π _ hW hsW' hU hUW q (by rw [hq]))
      (exists_isRegularPrincipal_map_tensorProduct_of_isInvertible_comap_fiberι π _ (hfib _)
        hW hsW' U hUW)
    let D := X.affineBasicOpen (U := U) g
    have hDU : D.1 ≤ U.1 := X.basicOpen_le g
    let := (X.presheaf.map (homOfLE hDU).op).hom.toAlgebra
    have : IsLocalization.Away g Γ(X, D) := hU.isLocalization_of_eq_basicOpen g (homOfLE hDU) rfl
    obtain ⟨h₁, h₂⟩ := hg Γ(X, D) Γ(J.subscheme, J.subschemeι ⁻¹ᵁ D) (J.subschemeι.app D).hom
      (J.subschemeι_app_surjective D) (by
        rw [ker_subschemeι_app, ← J.map_ideal hDU]
        rfl)
    refine ⟨⟨W, hW⟩, D, hDU.trans hUW, ?_, ?_, ?_⟩
    · have : q ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
        rw [hU.fromSpec_preimage_basicOpen]
        exact hgq
      rw [← hq]
      exact this
    · rw [← J.map_ideal hDU]
      exact h₁
    · rw [← Scheme.Hom.appLE_map π hUW (homOfLE hDU).op]
      exact h₂
  refine ⟨fun x ↦ ?_, ?_⟩
  · obtain ⟨W, V, hVW, hxV, hV, -⟩ := key x
    exact ⟨V, hxV, hV⟩
  · rw [HasRingHomProperty.iff_exists_appLE (P := @Flat)
      (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.Flat.holdsForLocalizationAway).left]
    intro d
    obtain ⟨W, V, hVW, hxV, -, hflat⟩ := key (J.subschemeι d)
    refine ⟨W, ⟨_, V.2.preimage J.subschemeι⟩, hxV, J.subschemeι.preimage_mono hVW, ?_⟩
    rwa [← Scheme.Hom.appLE_comp_appLE _ _ _ V.1 _ hVW le_rfl, CommRingCat.hom_comp,
      ← Scheme.Hom.app_eq_appLE]

/-- **The Cartier criterion on proper smooth curves.** Let `π : X ⟶ S` be proper and smooth of
relative dimension `1`, and let `D ⊆ X` be a relative effective Cartier divisor, i.e. its ideal
`J` is invertible and `D ⟶ S` is flat. Then `D ⟶ S` is finite locally free: finite, (flat) and
locally of finite presentation.

(Stacks, Tag 0B9D; blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, the implication
`(2) ⇒ (1)` for proper `X/S`) -/
theorem IsInvertible.isFinite_and_locallyOfFinitePresentation (π : X ⟶ S)
    [IsProper π] [SmoothOfRelativeDimension 1 π] {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (hflat : Flat (J.subschemeι ≫ π)) :
    IsFinite (J.subschemeι ≫ π) ∧ LocallyOfFinitePresentation (J.subschemeι ≫ π) := by
  have := SmoothOfRelativeDimension.smooth 1 π
  have := hJ.locallyQuasiFinite_subschemeι_comp π hflat
  exact ⟨.of_isProper_of_locallyQuasiFinite _,
    hJ.isLocallyPrincipal.locallyOfFinitePresentation_subschemeι_comp π⟩

/-- **Finite locally free closed subschemes of a smooth curve are divisors.** Let `π : X ⟶ S`
be smooth of relative dimension `1`, and let `D ⊆ X` be a closed subscheme, with ideal `J`,
which is finite locally free over `S`: `D ⟶ S` is finite, flat and locally of finite
presentation. Then `J` is invertible, so `D` is a relative effective Cartier divisor on `X/S`.

(Stacks, Tag 0B9D; blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, the implication
`(1) ⇒ (2)`) -/
theorem isInvertible_of_isFinite_of_flat (π : X ⟶ S) [SmoothOfRelativeDimension 1 π]
    {J : X.IdealSheafData} (hfin : IsFinite (J.subschemeι ≫ π)) (hflat : Flat (J.subschemeι ≫ π))
    (hlfp : LocallyOfFinitePresentation (J.subschemeι ≫ π)) : J.IsInvertible :=
  isInvertible_of_locallyQuasiFinite_of_flat π inferInstance hflat hlfp

/-- **The Cartier criterion, `(1) ⇒ (2)`, for relative divisors.** Let `π : X ⟶ S` be smooth of
relative dimension `1` and let `D ⊆ X` be a closed subscheme, with ideal `J`, which is finite
locally free over `S`. Then `D` is a relative effective Cartier divisor on `X/S`: `J` is
invertible by `isInvertible_of_isFinite_of_flat`, and `D ⟶ S` is flat by hypothesis.

(Stacks, Tag 0B9D; blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, the implication
`(1) ⇒ (2)`) -/
theorem isRelativeEffectiveCartier_of_isFinite (π : X ⟶ S) [SmoothOfRelativeDimension 1 π]
    {J : X.IdealSheafData} [IsFinite (J.subschemeι ≫ π)] [Flat (J.subschemeι ≫ π)]
    [LocallyOfFinitePresentation (J.subschemeι ≫ π)] :
    J.IsRelativeEffectiveCartier π :=
  ⟨isInvertible_of_isFinite_of_flat π inferInstance inferInstance inferInstance, inferInstance⟩

/-- **The Cartier criterion, `(2) ⇔ (3)`.** Let `π : X ⟶ S` be smooth of relative dimension `1`
and let `D ⊆ X` be a closed subscheme, with ideal `J`. Then `D` is a relative effective Cartier
divisor on `X/S` if and only if `D ⟶ S` is locally quasi-finite, flat and locally of finite
presentation.

(Stacks, Tag 0B9D; blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, the equivalence
`(2) ⇔ (3)`) -/
theorem isRelativeEffectiveCartier_iff_locallyQuasiFinite (π : X ⟶ S)
    [SmoothOfRelativeDimension 1 π] {J : X.IdealSheafData} :
    J.IsRelativeEffectiveCartier π ↔ LocallyQuasiFinite (J.subschemeι ≫ π) ∧
      Flat (J.subschemeι ≫ π) ∧ LocallyOfFinitePresentation (J.subschemeι ≫ π) := by
  have := SmoothOfRelativeDimension.smooth 1 π
  refine ⟨fun h ↦ ⟨h.1.locallyQuasiFinite_subschemeι_comp π h.2, h.2,
    h.1.isLocallyPrincipal.locallyOfFinitePresentation_subschemeι_comp π⟩,
    fun ⟨hqf, hflat, hlfp⟩ ↦ ⟨isInvertible_of_locallyQuasiFinite_of_flat π hqf hflat hlfp, hflat⟩⟩

/-- **The Cartier criterion, `(4) ⇒ (3)` over a locally noetherian base.** Let `S` be locally
noetherian, let `π : X ⟶ S` be smooth of relative dimension `1`, and let `D ⊆ X` be a closed
subscheme, with ideal `J`, such that `D ⟶ S` is locally quasi-finite and flat. Then `D ⟶ S` is
locally quasi-finite, flat and locally of finite presentation, so `D` is a relative effective
Cartier divisor by `isRelativeEffectiveCartier_iff_locallyQuasiFinite`.

`D ⟶ S` is a closed immersion followed by a smooth morphism, hence locally of finite type, and
a morphism locally of finite type into a locally noetherian scheme is locally of finite
presentation.

(Stacks, Tag 0B9D; blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, the implication
`(4) ⇒ (3)` for locally noetherian `S`) -/
theorem locallyOfFinitePresentation_of_locallyQuasiFinite [IsLocallyNoetherian S]
    (π : X ⟶ S) [SmoothOfRelativeDimension 1 π] {J : X.IdealSheafData}
    (hqf : LocallyQuasiFinite (J.subschemeι ≫ π)) (hflat : Flat (J.subschemeι ≫ π)) :
    LocallyQuasiFinite (J.subschemeι ≫ π) ∧ Flat (J.subschemeι ≫ π) ∧
      LocallyOfFinitePresentation (J.subschemeι ≫ π) :=
  have := SmoothOfRelativeDimension.smooth 1 π
  ⟨hqf, hflat, inferInstance⟩

/-- **Pullback of relative effective Cartier divisors.** Let `π : X ⟶ S` be flat and locally of
finite presentation, let `D ⊆ X` be a relative effective Cartier divisor on `X/S` with ideal
`J`, and let

```
  X' ──── g' ───▶ X
  │               │
  π'              π
  ▼               ▼
  T ───── g ────▶ S
```

be a pullback square. Then the base change `D_T = D ×[S] T ⊆ X'`, with ideal `J.comap g'`, is a
relative effective Cartier divisor on `X'/T`, and its line bundle is the pullback of that of
`D`: `𝒪_{X'}(D_T) ≅ g'^* 𝒪_X(D)`.

(Stacks, Tag 056Q; blueprint: `lem-pc-recd-pullback`) -/
theorem IsRelativeEffectiveCartier.isRelativeEffectiveCartier_comap_of_isPullback {π : X ⟶ S}
    [Flat π] [LocallyOfFinitePresentation π] {J : X.IdealSheafData}
    (hJ : J.IsRelativeEffectiveCartier π) {X' T : Scheme.{u}} {g' : X' ⟶ X} {π' : X' ⟶ T}
    {g : T ⟶ S} (h : IsPullback g' π' π g) : (J.comap g').IsRelativeEffectiveCartier π' :=
  ⟨hJ.1.comap_of_isPullback hJ.2 h, flat_comap_subschemeι_comp_of_isPullback hJ.2 h⟩

/-- **Pullback of relative effective Cartier divisors, with the line bundle.** In the situation
of `IsRelativeEffectiveCartier.isRelativeEffectiveCartier_comap_of_isPullback`, the base change
`D_T` is a relative effective Cartier divisor on `X'/T` and `𝒪_{X'}(D_T) ≅ g'^* 𝒪_X(D)`.

(Stacks, Tag 056Q; blueprint: `lem-pc-recd-pullback`) -/
theorem IsRelativeEffectiveCartier.comap_of_isPullback {π : X ⟶ S} [Flat π]
    [LocallyOfFinitePresentation π] {J : X.IdealSheafData} (hJ : J.IsRelativeEffectiveCartier π)
    {X' T : Scheme.{u}} {g' : X' ⟶ X} {π' : X' ⟶ T} {g : T ⟶ S} (h : IsPullback g' π' π g) :
    (J.comap g').IsRelativeEffectiveCartier π' ∧
      Nonempty ((J.comap g').toModulesᵛ ≅ (Modules.pullback g').obj J.toModulesᵛ) := by
  have h' := hJ.isRelativeEffectiveCartier_comap_of_isPullback h
  exact ⟨h', (hJ.1.nonempty_pullback_dual_toModules_iso g' h'.1).map Iso.symm⟩

end AlgebraicGeometry.Scheme.IdealSheafData

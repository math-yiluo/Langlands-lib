/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineOpenAlgebra
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.LocalIso
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.Mathlib.Topology.Sets.Opens

/-!
# Four facts about étale morphisms

## Lifting along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes and `p : W ⟶ Z` an étale morphism. Then `W` is,
in a neighbourhood of any of its points, the base change along `i` of a scheme étale over `X`.

This is the geometric counterpart of the ring theoretic statement that a standard étale algebra
over a quotient `R ⧸ I` is the base change of a standard étale algebra over `R`
(`Algebra.IsStandardEtale.exists_algEquiv_quotient_tensor`): everything is local on `X` and on
`W`, so the lift is produced inside a single affine chart and no gluing is involved.

## Local structure

An étale morphism `q : W ⟶ Spec B` is, around every point of `W`, dominated by `Spec` of a
standard étale `B`-algebra (`AlgebraicGeometry.Etale.exists_standardEtalePair`).

## Étale covers of a normal scheme with separably closed function field

Let `S` be an integral normal scheme whose function field is separably closed, and let
`p : V ⟶ S` be separated and étale. Then `V` is a disjoint union of open subschemes of `S`. This
is rendered as: there is an index type `ι` and a family of opens `U : ι → V.Opens` which are
pairwise disjoint, cover `V`, and are such that each composite `(U i).ι ≫ p` is an open
immersion. Normality of `S` is not a notion available in Mathlib at the level of schemes, so it
is taken as the explicit hypothesis that every stalk of `S` is integrally closed; together with
`[IsIntegral S]` this says exactly that `S` is an integral normal scheme.

## Connected components of fibres along an étale base change

Let `f : X ⟶ S` be locally of finite type and `r : Z ⟶ S` étale. For `z : Z`, the projection
from the fibre of `X ×_S Z` over `z` to the fibre of `X` over `r z` is open and closed, so it maps
connected components onto connected components.

## Étale schemes over reduced schemes

A scheme étale over a reduced scheme is reduced, by the corresponding statement
`Algebra.Etale.isReduced` for rings.

## Main results

- `AlgebraicGeometry.Etale.exists_isPullback_of_isClosedImmersion`: for every point `w` of `W`
  there is an open neighbourhood `W₀` of `w` in `W` and an étale morphism `q : V ⟶ X` such that
  `W₀` is the fibre product `V ×[X] Z`, compatibly with `p`.
- `AlgebraicGeometry.Etale.exists_pullback_hom_of_isClosedImmersion`: the pointed form. Given a
  morphism `s : Spec Ω ⟶ W` with `Ω` a field — in the application a geometric point of `W` — there
  is an étale `q : V ⟶ X` and a morphism `V ×[X] Z ⟶ W` over `Z` through which `s` factors.
- `AlgebraicGeometry.Etale.exists_standardEtalePair`: an étale morphism to `Spec B` is locally
  dominated by `Spec` of a standard étale `B`-algebra.
- `AlgebraicGeometry.Etale.exists_opens_isOpenImmersion_of_isSepClosed_functionField`: a
  separated étale scheme over an integral normal base with separably closed function field is a
  disjoint union of opens of the base.
- `AlgebraicGeometry.Etale.exists_finite_opens_isOpenImmersion_of_isSepClosed_functionField`: the
  same statement with finitely many pieces when the source is quasi-compact.
- `AlgebraicGeometry.connectedComponentIn_subset_image_pullback_fst`: the first projection maps
  a connected component of a fibre of `X ×_S Z ⟶ Z` onto a connected component of a fibre of `X`.
- `AlgebraicGeometry.isReduced_of_etale`: a scheme étale over a reduced scheme is reduced.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Topology

namespace AlgebraicGeometry

/-- Blueprint `lemma-openclosed-etale-lifts-locally`: **Étale morphisms lift locally along a
closed immersion.** If `i : Z ⟶ X` is a closed
immersion and `p : W ⟶ Z` is étale, then every point `w` of `W` has an open neighbourhood `W₀`
which is the base change along `i` of a scheme `V` étale over `X`, in a way compatible with `p`:
the square
```
W₀ ------- a -------> V
|                     |
W₀.ι ≫ p              q
↓                     ↓
Z ------- i --------> X
```
is cartesian. -/
theorem Etale.exists_isPullback_of_isClosedImmersion {X Z W : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (p : W ⟶ Z) [Etale p] (w : W) :
    ∃ W₀ : W.Opens, w ∈ W₀ ∧ ∃ (V : Scheme.{u}) (q : V ⟶ X) (_ : Etale q)
      (a : W₀.toScheme ⟶ V), IsPullback a (W₀.ι ≫ p) q i := by
  -- an affine chart `U` of `X` around the image of `w`
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := i.base (p.base w)) (U := ⊤) trivial
  -- an affine chart `W'` of `W` around `w`, mapping into the preimage of `U`
  obtain ⟨W', hW', hwW', hW'le⟩ :=
    exists_isAffineOpen_mem_and_subset (X := W) (x := w) (U := p ⁻¹ᵁ (i ⁻¹ᵁ U)) hxU
  replace hW'le : W' ≤ p ⁻¹ᵁ (i ⁻¹ᵁ U) := hW'le
  -- the closed immersion `i ⁻¹ᵁ U ⟶ U ≅ Spec Γ(X, U)` presents `i ⁻¹ᵁ U` as `Spec (Γ(X, U) ⧸ I)`
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := (i ∣_ U) ≫ hU.isoSpec.hom)).mp
    inferInstance
  -- the restriction of `p` to the two charts, read as a homomorphism `Γ(X, U) ⧸ I ⟶ Γ(W, W')`
  let ψ : CommRingCat.of (↥Γ(X, U) ⧸ I) ⟶ Γ(W, W') :=
    Spec.preimage (hW'.isoSpec.inv ≫ p.resLE (i ⁻¹ᵁ U) W' hW'le ≫ e.hom)
  have hψ : Spec.map ψ = hW'.isoSpec.inv ≫ p.resLE (i ⁻¹ᵁ U) W' hW'le ≫ e.hom :=
    Spec.map_preimage _
  have hψet : Etale (Spec.map ψ) := by
    rw [hψ]
    infer_instance
  let _ : Algebra (↥Γ(X, U) ⧸ I) ↥Γ(W, W') := ψ.hom.toAlgebra
  have : Algebra.Etale (↥Γ(X, U) ⧸ I) ↥Γ(W, W') := HasRingHomProperty.Spec_iff.mp hψet
  -- shrink `W'` to a basic open on which `Γ(W, -)` is standard étale over `Γ(X, U) ⧸ I`, and
  -- lift that standard étale algebra to `Γ(X, U)`
  obtain ⟨a, ha, hst⟩ := Algebra.IsEtaleAt.exists_isStandardEtale
    (R := ↥Γ(X, U) ⧸ I) (hW'.primeIdealOf ⟨w, hwW'⟩).asIdeal
  obtain ⟨T, _, _, hT, ⟨E⟩⟩ := Algebra.IsStandardEtale.exists_algEquiv_quotient_tensor
    (R := ↥Γ(X, U)) (Localization.Away a) I
  have hw₀ : w ∈ W.basicOpen a := by
    have : hW'.primeIdealOf ⟨w, hwW'⟩ ∈ hW'.fromSpec ⁻¹ᵁ W.basicOpen a := by
      rwa [hW'.fromSpec_preimage_basicOpen a]
    rwa [Scheme.Hom.mem_preimage, hW'.fromSpec_primeIdealOf ⟨w, hwW'⟩] at this
  have hloc : IsLocalization.Away a ↥Γ(W, W.basicOpen a) := hW'.isLocalization_basicOpen a
  -- `Γ(W, W.basicOpen a)` is the base change of `T` along `Γ(X, U) ⟶ Γ(X, U) ⧸ I`
  let ε : ((↥Γ(X, U) ⧸ I) ⊗[↥Γ(X, U)] T) ≃+* ↥Γ(W, W.basicOpen a) :=
    E.toRingEquiv.trans
      (IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a)
        ↥Γ(W, W.basicOpen a)).toRingEquiv
  have hε : ∀ x : ↥Γ(X, U) ⧸ I, ε (algebraMap _ _ x) =
      (W.presheaf.map (homOfLE (W.basicOpen_le a)).op).hom (ψ.hom x) := by
    intro x
    change (IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a)
        ↥Γ(W, W.basicOpen a)) (E (algebraMap _ _ x)) = _
    rw [E.commutes, IsScalarTower.algebraMap_apply (↥Γ(X, U) ⧸ I) ↥Γ(W, W') (Localization.Away a),
      AlgEquiv.commutes]
    rfl
  have hpo : IsPushout (CommRingCat.ofHom (algebraMap ↥Γ(X, U) (↥Γ(X, U) ⧸ I)))
      (CommRingCat.ofHom (algebraMap ↥Γ(X, U) T))
      (ψ ≫ W.presheaf.map (homOfLE (W.basicOpen_le a)).op)
      (CommRingCat.ofHom
        (ε.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ↥Γ(X, U))
          (A := ↥Γ(X, U) ⧸ I) (B := T)).toRingHom)) := by
    refine (CommRingCat.isPushout_tensorProduct ↥Γ(X, U) (↥Γ(X, U) ⧸ I) T).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ε.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext x
      simpa using hε x
    · ext x
      simp
  have hW₀ : IsAffineOpen (W.basicOpen a) := hW'.basicOpen a
  have hle : W.basicOpen a ≤ p ⁻¹ᵁ (i ⁻¹ᵁ U) := (W.basicOpen_le a).trans hW'le
  -- passing to `Spec` turns the restriction `Γ(W, W') ⟶ Γ(W, W.basicOpen a)` into the inclusion
  have h1 : Spec.map (W.presheaf.map (homOfLE (W.basicOpen_le a)).op) ≫ hW'.isoSpec.inv
      = hW₀.isoSpec.inv ≫ W.homOfLE (W.basicOpen_le a) := by
    rw [← cancel_epi hW₀.isoSpec.hom, ← Category.assoc, IsAffineOpen.isoSpec_hom,
      Scheme.Opens.toSpecΓ_SpecMap_presheaf_map]
    simp
  -- hence the left hand vertical map of the affine square is the restriction of `p`
  have hkey : Spec.map (ψ ≫ W.presheaf.map (homOfLE (W.basicOpen_le a)).op)
      = hW₀.isoSpec.inv ≫ p.resLE (i ⁻¹ᵁ U) (W.basicOpen a) hle ≫ e.hom := by
    have h2 : W.homOfLE (W.basicOpen_le a) ≫ p.resLE (i ⁻¹ᵁ U) W' hW'le
        = p.resLE (i ⁻¹ᵁ U) (W.basicOpen a) hle := Scheme.Hom.map_resLE _ _ _
    rw [Spec.map_comp, hψ, ← Category.assoc, h1, Category.assoc, ← Category.assoc _ _ e.hom, h2]
  have hqet : Etale (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(X, U) T))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  -- the affine square, transported along the charts
  have hsq : IsPullback
      (hW₀.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (ε.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ↥Γ(X, U))
          (A := ↥Γ(X, U) ⧸ I) (B := T)).toRingHom)))
      (p.resLE (i ⁻¹ᵁ U) (W.basicOpen a) hle)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(X, U) T)) ≫ hU.isoSpec.inv)
      (i ∣_ U) := by
    refine ((isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip).of_iso
      hW₀.isoSpec.symm (Iso.refl _) e.symm hU.isoSpec.symm ?_ ?_ ?_ ?_
    · simp
    · rw [hkey]
      simp
    · simp
    · simp only [Iso.symm_hom, Ideal.Quotient.algebraMap_eq]
      rw [eq_comm, Iso.inv_comp_eq, ← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
  -- paste with the cartesian square expressing `i ⁻¹ᵁ U = Z ×[X] U`
  have hpaste := hsq.paste_vert (isPullback_morphismRestrict i U)
  rw [Scheme.Hom.resLE_comp_ι] at hpaste
  exact ⟨W.basicOpen a, hw₀, Spec (CommRingCat.of T), _, inferInstance, _, hpaste⟩

/-- Blueprint `lemma-openclosed-etale-lifts-locally`, pointed form.

The pointed form of `AlgebraicGeometry.Etale.exists_isPullback_of_isClosedImmersion`: if
`i : Z ⟶ X` is a closed immersion, `p : W ⟶ Z` is étale and `s : Spec Ω ⟶ W` is a point of `W`
with values in a field `Ω`, then there is an étale morphism `q : V ⟶ X` together with a morphism
`g : V ×[X] Z ⟶ W` over `Z` through which `s` factors. -/
theorem Etale.exists_pullback_hom_of_isClosedImmersion {X Z W : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (p : W ⟶ Z) [Etale p] {Ω : Type u} [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ W) :
    ∃ (V : Scheme.{u}) (q : V ⟶ X) (_ : Etale q) (g : pullback q i ⟶ W),
      g ≫ p = pullback.snd q i ∧
        ∃ t : Spec (CommRingCat.of Ω) ⟶ pullback q i, t ≫ g = s := by
  obtain ⟨W₀, hw₀, V, q, hq, α, hpb⟩ :=
    Etale.exists_isPullback_of_isClosedImmersion i p (s.base default)
  have hrange : Set.range s.base ⊆ Set.range W₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨x, rfl⟩
    rw [Subsingleton.elim x default]
    exact hw₀
  refine ⟨V, q, hq, hpb.isoPullback.inv ≫ W₀.ι, ?_,
    IsOpenImmersion.lift W₀.ι s hrange ≫ hpb.isoPullback.hom, ?_⟩
  · rw [Category.assoc, Iso.inv_comp_eq]
    exact hpb.isoPullback_hom_snd.symm
  · rw [Category.assoc, Iso.hom_inv_id_assoc, IsOpenImmersion.lift_fac]

/-- **Étale morphisms are locally standard étale.** For an étale morphism `q : W ⟶ Spec B` and a
point `w` of `W`, there is a standard étale `B`-algebra `P.Ring` and a morphism
`Spec P.Ring ⟶ W` over `Spec B` whose image contains `w`: the restriction of `q` to an affine
open `Spec C` around `w` is given by an étale `B`-algebra `C`, which is standard étale after
inverting an element not in the prime of `w` (`Algebra.IsEtaleAt.exists_isStandardEtale`).
The morphism `Spec P.Ring ⟶ W` is an open immersion onto a basic open of the affine open. -/
theorem Etale.exists_standardEtalePair_isOpenImmersion {B : CommRingCat.{u}} {W : Scheme.{u}}
    (q : W ⟶ Spec B) [Etale q] (w : W) :
    ∃ (P : StandardEtalePair B) (e : Spec (.of P.Ring) ⟶ W), IsOpenImmersion e ∧
      e ≫ q = Spec.map (CommRingCat.ofHom (algebraMap B P.Ring)) ∧ w ∈ Set.range e := by
  obtain ⟨W', hW', hwW', -⟩ := exists_isAffineOpen_mem_and_subset (X := W) (x := w) (U := ⊤) trivial
  let _ : Algebra B Γ(W, W') := (hW'.ringHomOfSpec q).toAlgebra
  have : Algebra.Etale B Γ(W, W') := RingHom.etale_algebraMap.mp (hW'.etale_ringHomOfSpec q)
  obtain ⟨a, ha, hst⟩ := Algebra.IsEtaleAt.exists_isStandardEtale
    (R := B) (hW'.primeIdealOf ⟨w, hwW'⟩).asIdeal
  let Pr := hst.nonempty_standardEtalePresentation.some
  let φ : Γ(W, W') →+* Pr.P.Ring :=
    Pr.equivRing.toRingEquiv.toRingHom.comp (algebraMap Γ(W, W') (Localization.Away a))
  refine ⟨Pr.P, Spec.map (CommRingCat.ofHom φ) ≫ hW'.fromSpec, ?_, ?_, ?_⟩
  · have : IsIso (Spec.map (CommRingCat.ofHom Pr.equivRing.toRingEquiv.toRingHom)) :=
      inferInstanceAs (IsIso (Spec.map Pr.equivRing.toRingEquiv.toCommRingCatIso.hom))
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
      simp only [φ, CommRingCat.ofHom_comp, Spec.map_comp]
      infer_instance
    infer_instance
  · rw [Category.assoc, ← hW'.SpecMap_ringHomOfSpec q, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext b
    change Pr.equivRing (algebraMap Γ(W, W') (Localization.Away a) (algebraMap B Γ(W, W') b)) = _
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  · obtain ⟨r, hr⟩ : hW'.primeIdealOf ⟨w, hwW'⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(W, W') (Localization.Away a))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
      exact ha
    refine ⟨PrimeSpectrum.comap Pr.equivRing.symm.toRingEquiv.toRingHom r, ?_⟩
    rw [Scheme.Hom.comp_apply, Spec.map_apply]
    refine (congrArg hW'.fromSpec ?_).trans (hW'.fromSpec_primeIdealOf ⟨w, hwW'⟩)
    rw [← hr]
    refine PrimeSpectrum.ext (Ideal.ext fun x ↦ ?_)
    simp [φ]

/-- **Étale morphisms are locally standard étale.** For an étale morphism `q : W ⟶ Spec B` and a
point `w` of `W`, there is a standard étale `B`-algebra `P.Ring` and a morphism
`Spec P.Ring ⟶ W` over `Spec B` whose image contains `w`
(`AlgebraicGeometry.Etale.exists_standardEtalePair_isOpenImmersion`). -/
theorem Etale.exists_standardEtalePair {B : CommRingCat.{u}} {W : Scheme.{u}} (q : W ⟶ Spec B)
    [Etale q] (w : W) :
    ∃ (P : StandardEtalePair B) (e : Spec (.of P.Ring) ⟶ W),
      e ≫ q = Spec.map (CommRingCat.ofHom (algebraMap B P.Ring)) ∧ w ∈ Set.range e := by
  obtain ⟨P, e, -, he, hw⟩ := Etale.exists_standardEtalePair_isOpenImmersion q w
  exact ⟨P, e, he, hw⟩

/-- An étale morphism `p : V ⟶ S` into an integral normal scheme `S` with separably closed
function field is a local isomorphism: every point of `V` has an open neighbourhood mapping
isomorphically onto an open of `S`. Normality of `S` is the hypothesis `hS` that every stalk of
`S` is integrally closed.

Over affine charts `Spec A ⊆ S` and `Spec B ⊆ V` this is
`Algebra.Etale.exists_algHom_localizationAway_comap_eq`: every point of `Spec B` lies on a
section of `Spec B → Spec A` over a basic open of `Spec A`, and a section of an étale morphism
over an open is an open immersion (`AlgebraicGeometry.FormallyUnramified.isOpenImmersion_of_comp`).
-/
theorem Etale.isLocalIso_of_isSepClosed_functionField {V S : Scheme.{u}} [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsSepClosed S.functionField] (p : V ⟶ S) [Etale p] : IsLocalIso p := by
  refine ⟨fun x ↦ ?_⟩
  -- affine charts `U ∋ p x` of `S` and `W ∋ x` of `V` with `W ⊆ p ⁻¹ U`
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := p.base x) (U := ⊤) trivial
  obtain ⟨W, hW, hxW, hWle⟩ :=
    exists_isAffineOpen_mem_and_subset (X := V) (x := x) (U := p ⁻¹ᵁ U) hxU
  replace hWle : W ≤ p ⁻¹ᵁ U := hWle
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : IsIntegrallyClosed Γ(S, U) :=
    Scheme.isIntegrallyClosed_of_isIntegrallyClosed_stalk hS U
  have : IsFractionRing Γ(S, U) S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S U hU
  let _ : Algebra Γ(S, U) Γ(V, W) := (p.appLE U W hWle).hom.toAlgebra
  have : Algebra.Etale Γ(S, U) Γ(V, W) :=
    RingHom.etale_algebraMap.mp (HasRingHomProperty.appLE @Etale p ‹_› ⟨U, hU⟩ ⟨W, hW⟩ hWle)
  -- the point `x` lies on a section `σ` of `p` over a basic open of `U`
  obtain ⟨a, ψ, P, hP, hPq⟩ := Algebra.Etale.exists_algHom_localizationAway_comap_eq
    (A := Γ(S, U)) S.functionField (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
  let j : Spec (.of (Localization.Away a)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) (Localization.Away a))) ≫ hU.fromSpec
  let σ : Spec (.of (Localization.Away a)) ⟶ V :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hW.fromSpec
  have hσ : σ ≫ p = j := by
    simp only [σ, j, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hU hW hWle,
      ← Spec.map_comp_assoc]
    congr 2
    ext y
    exact ψ.commutes y
  have : IsOpenImmersion (σ ≫ p) := by
    rw [hσ]
    infer_instance
  have : IsOpenImmersion σ := FormallyUnramified.isOpenImmersion_of_comp p σ
  refine ⟨σ.opensRange, ⟨⟨P, hP⟩, ?_⟩, ?_⟩
  · have h1 : (Spec.map (CommRingCat.ofHom ψ.toRingHom)).base ⟨P, hP⟩ =
        hW.primeIdealOf ⟨x, hxW⟩ := PrimeSpectrum.ext hPq
    simp only [σ, Scheme.Hom.comp_base, TopCat.comp_app, h1]
    exact hW.fromSpec_primeIdealOf ⟨x, hxW⟩
  · rw [← σ.isoOpensRange_inv_comp, Category.assoc, hσ]
    infer_instance

/-- **Étale covers of a normal scheme with separably closed function field**
(blueprint `proposition-base-change-larger-algebraically-closed`). Let `S` be an integral normal
scheme — normality being the hypothesis `hS` that every stalk of `S` is integrally closed — with
separably closed function field. Then

1. every separated étale morphism `p : V ⟶ S` is a disjoint union of open immersions: there are
  nonempty, pairwise disjoint opens `U i` covering `V` with every `(U i).ι ≫ p` an open
  immersion;
2. every local ring of `S` is strictly henselian: it is henselian with separably closed residue
  field. -/
@[stacks 09Z9]
theorem Etale.exists_opens_isOpenImmersion_and_henselianLocalRing_stalk {S : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsSepClosed S.functionField] :
    (∀ (V : Scheme.{u}) (p : V ⟶ S) [IsSeparated p] [Etale p],
      ∃ (ι : Type u) (U : ι → V.Opens), (∀ i, (U i : Set V).Nonempty) ∧
        (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧ (⨆ i, U i) = ⊤ ∧
        ∀ i, IsOpenImmersion ((U i).ι ≫ p)) ∧
      ∀ x : S, HenselianLocalRing (S.presheaf.stalk x) ∧ IsSepClosed (S.residueField x) := by
  refine ⟨fun V p _ _ ↦ ?_, fun x ↦ ⟨Scheme.henselianLocalRing_stalk_of_isSepClosed_functionField
    hS x, Scheme.isSepClosed_residueField_of_isSepClosed_functionField hS x⟩⟩
  have := Etale.isLocalIso_of_isSepClosed_functionField hS p
  exact IsLocalIso.exists_opens_isOpenImmersion p

/-- **Étale covers of a normal scheme with separably closed function field.** Let `S` be an
integral normal scheme — normality being spelled out as the hypothesis `hS` that every stalk of
`S` is integrally closed — whose function field `S.functionField` is separably closed, and let
`p : V ⟶ S` be separated and étale. Then `V` is the disjoint union of a family of opens `U i`
each of which maps isomorphically onto an open of `S` (blueprint
`proposition-base-change-larger-algebraically-closed`). -/
@[stacks 09Z9]
theorem Etale.exists_opens_isOpenImmersion_of_isSepClosed_functionField
    {V S : Scheme.{u}} [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsSepClosed S.functionField] (p : V ⟶ S) [IsSeparated p] [Etale p] :
    ∃ (ι : Type u) (U : ι → V.Opens), (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (⨆ i, U i) = ⊤ ∧ ∀ i, IsOpenImmersion ((U i).ι ≫ p) := by
  obtain ⟨ι, U, -, hU⟩ :=
    (Etale.exists_opens_isOpenImmersion_and_henselianLocalRing_stalk hS).1 V p
  exact ⟨ι, U, hU⟩

/-- The quasi-compact refinement of
`AlgebraicGeometry.Etale.exists_opens_isOpenImmersion_of_isSepClosed_functionField`: if `V` is
in addition quasi-compact, then finitely many opens suffice (blueprint
`proposition-base-change-larger-algebraically-closed`). -/
@[stacks 09Z9]
theorem Etale.exists_finite_opens_isOpenImmersion_of_isSepClosed_functionField
    {V S : Scheme.{u}} [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsSepClosed S.functionField] (p : V ⟶ S) [IsSeparated p] [Etale p] [CompactSpace V] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → V.Opens), (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (⨆ i, U i) = ⊤ ∧ ∀ i, IsOpenImmersion ((U i).ι ≫ p) := by
  obtain ⟨ι, U, hne, hdisj, hcov, hU⟩ :=
    (Etale.exists_opens_isOpenImmersion_and_henselianLocalRing_stalk hS).1 V p
  exact ⟨ι, TopologicalSpace.Opens.finite_of_compactSpace_of_pairwiseDisjoint U hne hdisj hcov,
    U, hdisj, hcov, hU⟩

/-- Let `f : X ⟶ S` be locally of finite type, `r : Z ⟶ S` étale and `p` a point of `X ×_S Z`
over `z : Z`. The first projection maps the connected component of `p` in the fibre over `z`
onto the connected component of its image in the fibre of `f` over `r z`: the map between these
fibres is open, the fibre of `r` being discrete, and closed, being the base change of the finite
morphism `Spec κ(z) ⟶ Spec κ(r z)`. -/
theorem connectedComponentIn_subset_image_pullback_fst {X S Z : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : Z ⟶ S) [Etale r] {z : Z} (p : ↑(pullback f r))
    (hp : pullback.snd f r p = z) :
    connectedComponentIn (f ⁻¹' {r z}) (pullback.fst f r p) ⊆
      pullback.fst f r '' connectedComponentIn (pullback.snd f r ⁻¹' {z}) p := by
  set F := pullback.snd f r ⁻¹' {z}
  set E := f ⁻¹' {r z}
  have hc (q : ↑(pullback f r)) : f (pullback.fst f r q) = r (pullback.snd f r q) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hpF : p ∈ F := hp
  let φ : F → E := fun q ↦ ⟨pullback.fst f r q, by simp [E, hc, show _ = z from q.2]⟩
  -- `φ` is an open map, since `z` is isolated in its fibre under `r`
  obtain ⟨N, hN, hNz⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    (r.isDiscrete_preimage_singleton (r z)) z rfl
  have hφo : IsOpenMap φ := by
    intro O hO
    obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.mp hO
    have : φ '' (Subtype.val ⁻¹' O') =
        Subtype.val ⁻¹' (pullback.fst f r '' (O' ∩ pullback.snd f r ⁻¹' N)) := by
      ext ⟨y, hy⟩
      constructor
      · rintro ⟨⟨q, hq⟩, hqO, hqy⟩
        refine ⟨q, ⟨hqO, ?_⟩, congrArg Subtype.val hqy⟩
        rw [Set.mem_preimage, show pullback.snd f r q = z from hq]
        exact ((Set.ext_iff.mp hNz z).mpr rfl).1
      · rintro ⟨q, ⟨hqO, hqN⟩, rfl⟩
        have hqz : pullback.snd f r q = z := by
          have : pullback.snd f r q ∈ N ∩ r ⁻¹' {r z} := ⟨hqN, by
            change r _ = r z
            rw [← hc]
            exact hy⟩
          rwa [hNz] at this
        exact ⟨⟨q, hqz⟩, hqO, rfl⟩
    rw [this]
    exact ((pullback.fst f r).isOpenMap _
      (hO'.inter (hN.preimage (pullback.snd f r).continuous))).preimage continuous_subtype_val
  -- `φ` is a closed map, being the base change of `Spec κ(z) ⟶ Spec κ(r z)` on fibres
  have H := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f r) z
  have : IsFinite (Spec.map (r.residueFieldMap z)) :=
    (IsFinite.SpecMap_iff _).mpr (r.finite_residueFieldMap z)
  obtain ⟨Φ, hΦ, hUC⟩ : ∃ Φ : (pullback.snd f r).fiber z ⟶ f.fiber (r z),
      Φ ≫ f.fiberι (r z) = (pullback.snd f r).fiberι z ≫ pullback.fst f r ∧
        UniversallyClosed Φ :=
    ⟨_, pullback.lift_fst _ _ _, MorphismProperty.of_isPullback H.flip inferInstance⟩
  have hφc : IsClosedMap φ := by
    convert (f.fiberHomeo (r z)).isClosedMap.comp
      (Φ.isClosedMap.comp ((pullback.snd f r).fiberHomeo z).symm.isClosedMap)
    funext q
    refine Subtype.ext ?_
    change _ = f.fiberι (r z) (Φ (((pullback.snd f r).fiberHomeo z).symm q))
    rw [← Scheme.Hom.comp_apply, hΦ, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_fiberHomeo_symm]
  -- the image of the connected component of `p` is clopen, hence contains that of `φ p`
  have hK : IsClopen (φ '' connectedComponent ⟨p, hpF⟩) :=
    ⟨hφc _ isClopen_connectedComponent.1, hφo _ isClopen_connectedComponent.2⟩
  have hpE : pullback.fst f r p ∈ E := (φ ⟨p, hpF⟩).2
  rw [connectedComponentIn_eq_image hpE, connectedComponentIn_eq_image hpF, Set.image_image]
  intro y ⟨y', hy', hy⟩
  obtain ⟨q, hq, hqy⟩ := hK.connectedComponent_subset (x := φ ⟨p, hpF⟩)
    (Set.mem_image_of_mem _ mem_connectedComponent) hy'
  exact ⟨q, hq, by rw [← hy, ← hqy]⟩

/-- A scheme `X` étale over a reduced scheme `Y` is reduced: every point of `X` has an affine
neighbourhood `U` mapping into an affine open `V` of `Y` with `Γ(Y, V) ⟶ Γ(X, U)` étale, so
`Γ(X, U)` is reduced by `Algebra.Etale.isReduced`, and so is its localisation, the stalk. -/
theorem isReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsReduced Y] :
    IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).isOpen
    have he := HasRingHomProperty.appLE @Etale f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV
    algebraize [(f.appLE V U hUV).hom]
    have : _root_.IsReduced Γ(X, U) := Algebra.Etale.isReduced Γ(Y, V) Γ(X, U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact @isReduced_localizationPreserves _ _ _ _ _ (X.presheaf.algebra_section_stalk ⟨x, hxU⟩)
      this ‹_›
  exact isReduced_of_isReduced_stalk X

end AlgebraicGeometry

/-!
# Restricting morphisms near the image of an open immersion

- `AlgebraicGeometry.isIso_morphismRestrict_of_le_opensRange`: an open immersion restricted
  to an open contained in its image is an isomorphism.
- `AlgebraicGeometry.morphismRestrict_comp_comp_image_iff`: for open immersions `ψ` and `e`, a
  property respecting isomorphisms holds for the restriction of `ψ ≫ q ≫ e` over `e(V)` if
  and only if it holds for `q ∣_ V`, provided `q⁻¹(V)` lies in the image of `ψ`.
- `AlgebraicGeometry.etale_morphismRestrict_of_le`: `f ∣_ V` is étale if `f` is étale on an
  open containing `f⁻¹(V)`.
- `AlgebraicGeometry.etale_basicOpen_ι_comp_SpecMap`: étaleness of `Spec.map f` on a basic open
  `D(s)` follows from étaleness of the localized ring map.
-/

@[expose] public section

open CategoryTheory


namespace AlgebraicGeometry

/-- An open immersion restricted to an open contained in its image is an isomorphism. -/
lemma isIso_morphismRestrict_of_le_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {V : Y.Opens} (hV : V ≤ f.opensRange) : IsIso (f ∣_ V) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
  obtain ⟨x, hx⟩ := hV y.2
  refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩
  · rw [Scheme.Hom.mem_preimage, hx]
    exact y.2
  · rw [morphismRestrict_base_coe]
    exact hx

/-- Let `ψ` and `e` be open immersions and let `V` be an open of the target of `q` such that
`q⁻¹(V)` lies in the image of `ψ`. A property of morphisms respecting isomorphisms holds for the
restriction of `ψ ≫ q ≫ e` over `e(V)` if and only if it holds for `q ∣_ V`. -/
lemma morphismRestrict_comp_comp_image_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {U Y Z T : Scheme.{u}} (ψ : U ⟶ Y) [IsOpenImmersion ψ] (q : Y ⟶ Z) (e : Z ⟶ T)
    [IsOpenImmersion e] {V : Z.Opens} (hV : q ⁻¹ᵁ V ≤ ψ.opensRange) :
    P ((ψ ≫ q ≫ e) ∣_ (e ''ᵁ V)) ↔ P (q ∣_ V) := by
  have : IsIso (ψ ∣_ ((q ≫ e) ⁻¹ᵁ e ''ᵁ V)) := isIso_morphismRestrict_of_le_opensRange ψ
    (by rwa [Scheme.Hom.comp_preimage, e.preimage_image_eq])
  have : IsIso (e ∣_ e ''ᵁ V) :=
    isIso_morphismRestrict_of_le_opensRange e (e.image_le_opensRange V)
  rw [morphismRestrict_comp, P.cancel_left_of_respectsIso, morphismRestrict_comp,
    P.cancel_right_of_respectsIso]
  exact P.arrow_mk_iso_iff (morphismRestrictEq q (e.preimage_image_eq V))

/-- If `f` is étale on an open `O` containing `f⁻¹(V)`, then `f ∣_ V` is étale. -/
lemma etale_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {O : X.Opens}
    [Etale (O.ι ≫ f)] {V : Y.Opens} (hV : f ⁻¹ᵁ V ≤ O) : Etale (f ∣_ V) := by
  have : Etale (f ∣_ V ≫ V.ι) := by
    rw [morphismRestrict_ι, ← X.homOfLE_ι hV, Category.assoc]
    infer_instance
  exact Etale.of_comp _ V.ι

/-- Let `f : R ⟶ S` be a ring map and `s ∈ S`. If `R ⟶ S[1/s]` is étale, then `Spec S ⟶ Spec R`
is étale on the basic open `D(s)`. -/
lemma etale_basicOpen_ι_comp_SpecMap {R S : CommRingCat.{u}} (f : R ⟶ S) (s : S)
    (h : ((algebraMap S (Localization.Away s)).comp f.hom).Etale) :
    Etale (Scheme.Opens.ι (X := Spec S) (PrimeSpectrum.basicOpen s) ≫ Spec.map f) := by
  rw [← basicOpenIsoSpecAway_hom_SpecMap, Category.assoc, ← Spec.map_comp]
  have := (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := f ≫ CommRingCat.ofHom (algebraMap S (Localization.Away s)))).mpr h
  infer_instance

/-- **Smooth morphisms and étale morphisms.** A morphism of schemes is smooth (Mathlib's
`AlgebraicGeometry.Smooth`: locally given by smooth ring maps, equivalently by standard smooth
presentations, `AlgebraicGeometry.Smooth.iff_forall_exists_isStandardSmooth`) of relative
dimension `n` if it is `SmoothOfRelativeDimension n`; the étale morphisms are exactly the smooth
morphisms of relative dimension zero.

(blueprint: `def-sbc-smooth-morphisms`) -/
theorem etale_iff_smoothOfRelativeDimension_zero {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Etale f ↔ SmoothOfRelativeDimension 0 f := by
  rw [Etale.eq_smoothOfRelativeDimension_zero]

/-- **Residue field extensions of an étale algebra are finite separable.** If
`Spec B ⟶ Spec A` is étale and `q` is a prime of `B` lying over the prime `p` of `A`, then
`κ(q)` is a finite separable extension of `κ(p)`.

(blueprint: `lem-weil-pbc-etale-algebra-residue-field-separable`) -/
theorem Etale.isSeparable_residueField_of_spec {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (h : Etale (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q)] :
    Algebra.IsSeparable p.ResidueField q.ResidueField ∧
      Module.Finite p.ResidueField q.ResidueField := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)] at h
  have : Algebra.Etale A B := RingHom.etale_algebraMap.mp h
  exact ⟨inferInstance, inferInstance⟩

/-- **Base change of an étale ring map is étale.** If `Spec A ⟶ Spec R` is étale, then so is
`Spec (S ⊗[R] A) ⟶ Spec S` for every `R`-algebra `S`.

(blueprint: `lem-weil-pbc-etale-ring-base-change`) -/
theorem Etale.spec_map_algebraMap_tensorProduct {R S A : Type u} [CommRing R] [CommRing S]
    [CommRing A] [Algebra R A] [Algebra R S]
    (h : Etale (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)] at h ⊢
  have : Algebra.Etale R A := RingHom.etale_algebraMap.mp h
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- **Shrinking a pointed étale neighbourhood to an affine open around the point.** Let
`f : V ⟶ S` be étale, `v : Spec Ω ⟶ V` a morphism from the spectrum of a field and `W` an open
of `V` containing the image of `v`. Then there is an open immersion `j : Spec R ⟶ V` whose image
contains the image of `v` and is contained in `W`; `j ≫ f` is étale and `v` factors uniquely
through `j`.

(blueprint: `lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink`) -/
theorem Scheme.exists_isOpenImmersion_spec_lift_of_etale {S V : Scheme.{u}} (f : V ⟶ S)
    [Etale f] {Ω : Type u} [Field Ω] (v : Spec (.of Ω) ⟶ V) (W : V.Opens)
    (hW : Set.range v.base ⊆ W) :
    ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ V), IsOpenImmersion j ∧
      Set.range v.base ⊆ Set.range j.base ∧ Set.range j.base ⊆ W ∧ Etale (j ≫ f) ∧
      ∃! v₀ : Spec (.of Ω) ⟶ Spec R, v₀ ≫ j = v := by
  obtain ⟨R, j, _, hv, hj⟩ := exists_affine_mem_range_and_range_subset
    (x := v.base default) (U := W) (hW ⟨default, rfl⟩)
  have hr : Set.range v.base ⊆ Set.range j.base := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  refine ⟨R, j, inferInstance, hr, hj, inferInstance,
    ⟨IsOpenImmersion.lift j v hr, IsOpenImmersion.lift_fac j v hr, fun w hw ↦ ?_⟩⟩
  rw [← cancel_mono j, hw, IsOpenImmersion.lift_fac]

open Polynomial in
/-- **The standard étale algebra of a monic polynomial localized at its derivative.** For a
monic `Q ∈ S[X]`, the algebra `S' = S[X][Y]/(Q, Y Q' - 1)` (the standard étale algebra of the
pair `(Q, Q')`) is étale over `S`, and for every `S`-algebra `L` and every `b ∈ L` with
`Q(b) = 0` and `Q'(b)` a unit there is exactly one `S`-algebra map `S' → L` sending the class of
`X` to `b`.

(blueprint: `lem-weil-pbc-standard-etale-monic-derivative`) -/
theorem StandardEtalePair.etale_ofMonic_and_existsUnique {S : Type u} [CommRing S] {Q : S[X]}
    (hQ : Q.Monic) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap S (StandardEtalePair.ofMonic hQ 1).Ring))) ∧
      ∀ (L : Type*) [CommRing L] [Algebra S L] (b : L), aeval b Q = 0 →
        IsUnit (aeval b (derivative Q)) →
        ∃! φ : (StandardEtalePair.ofMonic hQ 1).Ring →ₐ[S] L,
          φ (StandardEtalePair.ofMonic hQ 1).X = b := by
  refine ⟨?_, fun L _ _ b hb hb' ↦ ?_⟩
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  · have h : (StandardEtalePair.ofMonic hQ 1).HasMap b := ⟨hb, by simpa using hb'⟩
    refine ⟨(StandardEtalePair.ofMonic hQ 1).lift b h, StandardEtalePair.lift_X _ _ _,
      fun φ hφ ↦ ?_⟩
    exact StandardEtalePair.hom_ext (by rw [hφ, StandardEtalePair.lift_X])


end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization

/-!
# Affine curves over a field and the affine line

This file collects the algebro-geometric input for reducing statements about affine curves over a
field `k` to the affine line `𝔸¹_k = 𝔸(PUnit; Spec k)`.

## Main statements

- `Algebra.exists_finite_algHom_polynomial_of_ringKrullDim_le_one`: a finitely generated
  `k`-algebra of dimension at most one is finite over a polynomial ring `k[T]`.
- `AlgebraicGeometry.AffineSpace.exists_isFinite_of_ringKrullDim_le_one`: Noether normalization
  for affine curves; an affine scheme of finite type over `k` of dimension at most one admits a
  finite morphism to `𝔸¹_k` over `k`.
- `AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension_one_of_isOpenImmersion` and
  `AlgebraicGeometry.AffineSpace.geometricallyIrreducible_of_isOpenImmersion`: a nonempty open
  subscheme of `𝔸¹_k` is a smooth geometrically irreducible curve over `k`.
- `AlgebraicGeometry.AffineSpace.exists_basicOpen_le`: a nonempty open of `𝔸¹_k` contains a
  nonempty basic open.
- `AlgebraicGeometry.ringKrullDim_le_of_smoothOfRelativeDimension`: an affine scheme smooth of
  relative dimension `n` over a field has Krull dimension at most `n`;
  `AlgebraicGeometry.Scheme.Hom.ringKrullDim_fiber_le` is the variant for affine fibres of a
  smooth morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- A finitely generated algebra `B` of Krull dimension at most one over a field `K` is a finite
module over a polynomial ring `K[T]` (along some `K`-algebra map `K[T] → B`).

If `B = 0` any map works; otherwise Noether normalization gives a finite injective map from a
polynomial ring in `dim B ≤ 1` variables, and in zero variables we precompose with `T ↦ 0`. -/
theorem Algebra.exists_finite_algHom_polynomial_of_ringKrullDim_le_one
    (K B : Type*) [Field K] [CommRing B] [Algebra K B] [Algebra.FiniteType K B]
    (hB : ringKrullDim B ≤ 1) :
    ∃ g : Polynomial K →ₐ[K] B, g.Finite := by
  cases subsingleton_or_nontrivial B with
  | inl _ =>
    exact ⟨Polynomial.aeval 0, RingHom.Finite.of_surjective _ fun b ↦
      ⟨0, Subsingleton.elim _ _⟩⟩
  | inr _ =>
    obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg K B
    have hs : (s : WithBot ℕ∞) ≤ 1 := by
      rw [← ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial g hg hfin]
      exact hB
    have hs : s ≤ 1 := by exact_mod_cast hs
    obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
    · let e := MvPolynomial.isEmptyAlgEquiv K (Fin 0)
      refine ⟨(g.comp e.symm.toAlgHom).comp (Polynomial.aeval (0 : K)), ?_⟩
      refine RingHom.Finite.comp (RingHom.Finite.comp hfin
        (RingHom.Finite.of_surjective _ e.symm.surjective)) ?_
      exact RingHom.Finite.of_surjective _ fun a ↦ ⟨Polynomial.C a, by simp⟩
    · let e := MvPolynomial.uniqueAlgEquiv K (Fin 1)
      exact ⟨g.comp e.symm.toAlgHom, RingHom.Finite.comp hfin
        (RingHom.Finite.of_surjective _ e.symm.surjective)⟩

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

namespace AffineSpace

/-- **Noether normalization for affine curves.** An affine scheme `C` locally of finite type
over a field `k` with `dim Γ(C, ⊤) ≤ 1` admits a finite morphism `f : C ⟶ 𝔸¹_k` over `k`. -/
theorem exists_isFinite_of_ringKrullDim_le_one (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsAffine C] [LocallyOfFiniteType (C ↘ Spec (.of k))] (hC : ringKrullDim Γ(C, ⊤) ≤ 1) :
    ∃ f : C ⟶ 𝔸(PUnit.{u + 1}; Spec (.of k)),
      IsFinite f ∧ f ≫ 𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k) = C ↘ Spec (.of k) := by
  let s := C ↘ Spec (.of k)
  let : Algebra k Γ(C, ⊤) := (s.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(C, ⊤) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appTop @LocallyOfFiniteType s ‹_›)
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  obtain ⟨g, hg⟩ := Algebra.exists_finite_algHom_polynomial_of_ringKrullDim_le_one k Γ(C, ⊤) hC
  let φ : MvPolynomial PUnit.{u + 1} k →ₐ[k] Γ(C, ⊤) :=
    g.comp (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}).toAlgHom
  have hφ : φ.Finite := RingHom.Finite.comp hg
    (RingHom.Finite.of_surjective _ (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}).surjective)
  refine ⟨C.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    (SpecIso PUnit.{u + 1} (.of k)).inv, ?_, ?_⟩
  · have : IsFinite (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
      (IsFinite.SpecMap_iff _).mpr hφ
    infer_instance
  · rw [Category.assoc, Category.assoc, SpecIso_inv_over, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    have e : φ.toRingHom.comp MvPolynomial.C =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop).hom := by
      ext a
      exact φ.commutes a
    rw [e, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

variable {V : Scheme.{u}} (v : V ⟶ 𝔸(PUnit.{u + 1}; Spec (.of k))) [IsOpenImmersion v]

/-- An open subscheme of the affine line over a field is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_of_isOpenImmersion :
    SmoothOfRelativeDimension 1 (v ≫ 𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) := by
  have := AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k))
  rw [Nat.card_unique] at this
  rw [show 1 = 0 + 1 from rfl]
  infer_instance

/-- A nonempty open subscheme of the affine line over a field is geometrically irreducible. -/
theorem geometricallyIrreducible_of_isOpenImmersion [Nonempty V] :
    GeometricallyIrreducible (v ≫ 𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) :=
  GeometricallyIrreducible.comp_of_isOpenImmersion v _

/-- A nonempty open subscheme of the affine line over a field is geometrically connected. -/
theorem geometricallyConnected_of_isOpenImmersion [Nonempty V] :
    GeometricallyConnected (v ≫ 𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) :=
  have := geometricallyIrreducible_of_isOpenImmersion v
  GeometricallyConnected.of_geometricallyIrreducible _

/-- A nonempty open `U` of an affine space over an affine base contains a nonempty basic open
`D(g)`, which is affine. -/
theorem exists_basicOpen_le {n : Type u} {S : Scheme.{u}} [IsAffine S] (U : 𝔸(n; S).Opens)
    (hU : (U : Set 𝔸(n; S)).Nonempty) :
    ∃ g : Γ(𝔸(n; S), ⊤), 𝔸(n; S).basicOpen g ≤ U ∧
      ((𝔸(n; S).basicOpen g : 𝔸(n; S).Opens) : Set 𝔸(n; S)).Nonempty := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen 𝔸(n; S)) (U := U) (x := x) hx
  exact ⟨g, hgU, x, hxg⟩

end AffineSpace

/-- An affine scheme `X` smooth of relative dimension `n` over a field has
`dim Γ(X, ⊤) ≤ n`. -/
theorem ringKrullDim_le_of_smoothOfRelativeDimension {K : Type u} [Field K] {X : Scheme.{u}}
    [IsAffine X] (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] :
    ringKrullDim Γ(X, ⊤) ≤ n := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (IsHomeomorph.topologicalKrullDim_eq _ X.isoSpec.hom.homeomorph.isHomeomorph).symm.trans_le
    (topologicalKrullDim_le_of_smoothOfRelativeDimension f n)

/-- The affine fibres of a morphism `h` smooth of relative dimension `n` have Krull dimension at
most `n`: the fibre `h.fiber y` is smooth of relative dimension `n` over the residue field of
`y`, by base change. -/
theorem Scheme.Hom.ringKrullDim_fiber_le {U Y : Scheme.{u}} (h : U ⟶ Y) (n : ℕ)
    [SmoothOfRelativeDimension n h] (y : Y) [IsAffine (h.fiber y)] :
    ringKrullDim Γ(h.fiber y, ⊤) ≤ n := by
  have : SmoothOfRelativeDimension n (h.fiberToSpecResidueField y) :=
    inferInstanceAs (SmoothOfRelativeDimension n (pullback.snd _ _))
  exact ringKrullDim_le_of_smoothOfRelativeDimension (h.fiberToSpecResidueField y) n

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart
public import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.KrullDimension.Field

/-!

# Quasi-finite coordinates

Let `f : X ⟶ T` be locally of finite presentation over an affine scheme `T` (for instance a
scheme of finite type over the trait `S = Spec k'⟦t⟧`, `AlgebraicGeometry.trait`), and let `x` be
a point of `X` with local fibre dimension `q = dim_x X_{f(x)}`. Then there are an open
neighbourhood `V` of `x` and a locally quasi-finite morphism `b : V ⟶ 𝔸^q_T` over `T`
(blueprint `lemma-quasi-finite-coordinates`), and the base change of `V` to any field-valued
point `Spec K ⟶ T` (for instance the geometric generic point of the trait) has dimension at
most `q`.

## Main results

- `AlgebraicGeometry.exists_quasiFinite_affineSpace_chart`: the open neighbourhood `V` and the
  quasi-finite coordinates `b : V ⟶ 𝔸^q_T`, with `q = dim_x X_{f(x)}`.
- `AlgebraicGeometry.topologicalKrullDim_pullback_le_of_chart`: `dim (V ×_T Spec K) ≤ q`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

section LocalDimension

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

/-- An inducing map does not decrease the local dimension. -/
theorem topologicalKrullDimAt_le_of_isInducing {g : A → B} (hg : IsInducing g) (a : A) :
    topologicalKrullDimAt a ≤ topologicalKrullDimAt (g a) := by
  refine le_iInf₂ fun U ha ↦ ?_
  let V : TopologicalSpace.Opens A := ⟨g ⁻¹' U, U.isOpen.preimage hg.continuous⟩
  exact (iInf₂_le V ha).trans ((hg.restrictPreimage (U : Set B)).topologicalKrullDim_le)

/-- An open embedding preserves the local dimension. -/
theorem topologicalKrullDimAt_eq_of_isOpenEmbedding {g : A → B} (hg : IsOpenEmbedding g)
    (a : A) : topologicalKrullDimAt a = topologicalKrullDimAt (g a) := by
  refine le_antisymm (topologicalKrullDimAt_le_of_isInducing hg.isInducing a) ?_
  let e := hg.isEmbedding.toHomeomorph
  rw [← hg.isOpen_range.topologicalKrullDimAt_eq ⟨a, rfl⟩]
  exact (topologicalKrullDimAt_le_of_isInducing e.symm.isEmbedding.isInducing (e a)).trans_eq
    (congrArg _ (e.symm_apply_apply a))

end LocalDimension

/-- **Quasi-finite coordinates** (blueprint `lemma-quasi-finite-coordinates`, existence part):
for `f : X ⟶ T` locally of finite presentation over an affine scheme `T` and a point `x` of `X`,
with `q = dim_x X_{f(x)}` the local dimension of its fibre, there are an open neighbourhood `V`
of `x` and a locally quasi-finite morphism `b : V ⟶ 𝔸^q_T` over `T`, locally of finite
presentation. It is the affine chart `exists_quasiFinite_polynomial_chart` (Stacks 00QE) on an
affine open neighbourhood of `x`, moved into `X`. -/
theorem exists_quasiFinite_affineSpace_chart {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [LocallyOfFinitePresentation f] (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ (n : ℕ) (b : V.toScheme ⟶ 𝔸(ULift.{u} (Fin n); T)),
      LocallyOfFinitePresentation b ∧ LocallyQuasiFinite b ∧
      b ≫ (𝔸(ULift.{u} (Fin n); T) ↘ T) = V.ι ≫ f ∧
      topologicalKrullDimAt (f.asFiber x) = n := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  change X.Opens at W
  have : IsAffine W := hW
  obtain ⟨U, -, hyU, n, e, he₁, he₂, he₃, hn⟩ :=
    exists_quasiFinite_polynomial_chart (W.ι ≫ f) ⟨x, hxW⟩
  refine ⟨W.ι ''ᵁ U, ⟨⟨x, hxW⟩, hyU, rfl⟩, n, (W.ι.isoImage U).inv ≫ e, inferInstance,
    inferInstance, ?_, ?_⟩
  · rw [Category.assoc, he₃, Scheme.Hom.isoImage_inv_ι_assoc]
  · rw [← hn]
    have h := topologicalKrullDimAt_eq_of_isOpenEmbedding
      (PolynomialChart.fibreInclusion f W (f (W.ι ⟨x, hxW⟩))).isOpenEmbedding
      (PolynomialChart.fibrePoint f W ⟨x, hxW⟩)
    rw [PolynomialChart.fibreInclusion_asFiber] at h
    exact h.symm

/-- **The generic fibre of quasi-finite coordinates** (blueprint
`lemma-quasi-finite-coordinates`, dimension part): if `b : V ⟶ 𝔸^n_T` is locally quasi-finite
over `T`, then for every field-valued point `g : Spec K ⟶ T` (for instance the geometric
generic point of the trait), the base change `V ×_T Spec K` has dimension at most `n`: it maps
locally quasi-finitely to `𝔸^n_K`. -/
theorem topologicalKrullDim_pullback_le_of_chart {X T : Scheme.{u}} {V : X.Opens} (f : X ⟶ T)
    {n : ℕ} (b : V.toScheme ⟶ 𝔸(ULift.{u} (Fin n); T)) [LocallyQuasiFinite b]
    (hb : b ≫ (𝔸(ULift.{u} (Fin n); T) ↘ T) = V.ι ≫ f) {K : Type u} [Field K]
    (g : Spec (.of K) ⟶ T) :
    topologicalKrullDim (pullback (V.ι ≫ f) g : Scheme.{u}) ≤ n := by
  let φ : pullback (V.ι ≫ f) g ⟶ pullback (𝔸(ULift.{u} (Fin n); T) ↘ T) g :=
    (pullback.congrHom hb.symm rfl).hom ≫
      (pullbackRightPullbackFstIso (𝔸(ULift.{u} (Fin n); T) ↘ T) g b).inv ≫
      pullback.snd b (pullback.fst (𝔸(ULift.{u} (Fin n); T) ↘ T) g)
  have : LocallyQuasiFinite φ := by dsimp [φ]; infer_instance
  refine φ.topologicalKrullDim_le_of_locallyQuasiFinite.trans (le_of_eq ?_)
  rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) g).isoPullback).isHomeomorph]
  have : IsNoetherianRing Γ(Spec (.of K), ⊤) :=
    isNoetherianRing_of_ringEquiv K (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  rw [topologicalKrullDim_affineSpace_of_isAffine]
  change topologicalKrullDim (PrimeSpectrum K) + _ = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  simp

end AlgebraicGeometry

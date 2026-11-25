/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Cohomology.RelativeSerre
public import WeilConjectures.AlgebraicGeometry.FibreDimension
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexFibre
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver

/-!
# Vanishing of the higher direct images above the fibre dimension

Let `f : X ⟶ T` be proper of finite presentation and `ℱ` an `𝒪_X`-module of finite presentation
which is flat over `T`. The higher direct images vanish above the dimension of the fibres:

- `AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_hFiber_eq_zero`: if the
  cohomology `H^q(X_t, ℱ_t)` of every fibre vanishes for `q > d`, then `R^q f_* ℱ = 0` for `q > d`.
  Locally `R f_* ℱ` is computed by a bounded complex `P` of finite free modules whose fibres
  `P ⊗ κ(t)` compute the fibre cohomology; a finite free complex whose fibres are exact in degree
  `q` is exact in degree `q`.
- `AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_restrict_of_topologicalKrullDim_le`:
  if the fibres of `f` over an open `U` have dimension at most `d`, then `R^q f_* ℱ|_U = 0` for
  `q > d`, by Grothendieck vanishing on the fibres.
- `exists_isZero_higherDirectImage_restrict_of_topologicalKrullDim_le`:
  every point of `T` has an open neighbourhood `U` over which the fibre dimension is bounded by
  some `d_U`, and then `R^q f_* ℱ|_U = 0` for `q > d_U`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

section Coherence

variable [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]

/-- **Vanishing of the higher direct images above the fibre cohomology.** With `f : X ⟶ T`
proper of finite presentation and `ℱ` an `𝒪_X`-module of finite presentation which is flat over
`T`, if the cohomology `H^q(X_t, ℱ_t)` of every fibre vanishes in degrees `q > d`, then
`R^q f_* ℱ = 0` for all `q > d`.

Near a point of `T`, `R f_* ℱ` is computed by a bounded complex `P` of finite free modules whose
fibres compute the fibre cohomology
(`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`); the fibres of
`P` are exact in degrees `q > d`, hence so is `P`
(`IsFiniteFreeComplex.isZero_homology_of_isZero_homology_pullback`).

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem isZero_higherDirectImage_of_hFiber_eq_zero (hℱ : ℱ.IsFlatOver f) {d : ℕ}
    (h : ∀ t q, d < q → ℱ.hFiber f q t = 0) {q : ℕ} (hq : d < q) :
    IsZero ((higherDirectImage f q).obj ℱ) := by
  refine isZero_of_forall_exists_isZero_restrict _ fun t ↦ ?_
  obtain ⟨U, P, d', htU, hP, hbc⟩ := exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ t
  refine ⟨U, htU, ?_⟩
  -- the complex `P` is exact in degree `q`
  have hPq : IsZero (P.homology q) := by
    refine hP.isZero_homology_of_isZero_homology_pullback q fun y ↦ ?_
    have hs : U.ι y ∈ U := y.2
    obtain ⟨g, hg⟩ := exists_comp_ι_eq_fromSpecResidueField hs
    obtain ⟨x⟩ : Nonempty (Spec (T.residueField (U.ι y))) := inferInstance
    refine ⟨T.residueField (U.ι y), Field.toIsField _, g, x, U.ι.isOpenEmbedding.injective ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, hg]
      exact (Scheme.range_fromSpecResidueField (U.ι y)).subset ⟨x, rfl⟩
    have := isGrothendieckAbelian (f.fiber (U.ι y))
    have sq : IsPullback (f.fiberι (U.ι y)) (f.fiberToSpecResidueField (U.ι y)) f (g ≫ U.ι) := by
      rw [hg]
      exact IsPullback.of_hasPullback _ _
    obtain ⟨e⟩ := hbc g _ _ sq q
    have : IsSeparated (f.fiberToSpecResidueField (U.ι y)) := by
      unfold Scheme.Hom.fiberToSpecResidueField
      infer_instance
    have : QuasiCompact (f.fiberToSpecResidueField (U.ι y)) := by
      unfold Scheme.Hom.fiberToSpecResidueField
      infer_instance
    let := f.fiberOverSpecResidueField (U.ι y)
    have := finiteDimensional_H_fiber f ℱ hℱ q (U.ι y)
    have : Subsingleton (((Modules.pullback (f.fiberι (U.ι y))).obj ℱ).H q) :=
      Module.finrank_zero_iff.mp (h _ q hq)
    exact (isZero_higherDirectImage_of_subsingleton_H _ _ q this).of_iso e
  -- `R^q f_* ℱ|_U` is the cohomology of `P`
  have := isGrothendieckAbelian (f ⁻¹ᵁ U).toScheme
  have sq : IsPullback (f ⁻¹ᵁ U).ι (f ∣_ U) f (𝟙 U.toScheme ≫ U.ι) := by
    rw [Category.id_comp]
    exact (isPullback_morphismRestrict f U).flip
  obtain ⟨e₁⟩ := nonempty_higherDirectImage_iso_restrict f ℱ U.ι _ _
    (isPullback_morphismRestrict f U).flip q
  obtain ⟨e₂⟩ := hbc (𝟙 _) _ _ sq q
  let e₃ : ((Modules.pullback (𝟙 U.toScheme)).mapHomologicalComplex _).obj P ≅ P :=
    HomologicalComplex.Hom.isoOfComponents (fun n ↦ (Modules.pullbackId _).app (P.X n))
      (fun i j _ ↦ ((Modules.pullbackId _).hom.naturality (P.d i j)).symm)
  exact hPq.of_iso (e₁.symm ≪≫ e₂.symm ≪≫ HomologicalComplex.homologyMapIso e₃ q)

/-- **Vanishing of the higher direct images above the fibre dimension.** With `f : X ⟶ T`
proper of finite presentation and `ℱ` an `𝒪_X`-module of finite presentation which is flat over
`T`, if the fibres `X_t` of `f` over the points `t` of an open `U` of `T` have dimension at most
`d`, then `R^q f_* ℱ|_U = 0` for all `q > d`.

By Grothendieck vanishing on the Noetherian schemes `X_t`, the fibre cohomology `H^q(X_t, ℱ_t)`
vanishes for `q > d`, and the statement is
`AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_hFiber_eq_zero` for the restriction
of `f` over `U`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem isZero_higherDirectImage_restrict_of_topologicalKrullDim_le (hℱ : ℱ.IsFlatOver f)
    (U : T.Opens) {d : ℕ} (hd : ∀ t ∈ U, topologicalKrullDim (f.fiber t) ≤ d) {q : ℕ}
    (hq : d < q) : IsZero (((higherDirectImage f q).obj ℱ).restrict U.ι) := by
  have := isGrothendieckAbelian (f ⁻¹ᵁ U).toScheme
  have sq : IsPullback (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι := (isPullback_morphismRestrict f U).flip
  obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ U.ι _ _ sq q
  refine IsZero.of_iso ?_ e.symm
  have hflat : ((Modules.pullback (f ⁻¹ᵁ U).ι).obj ℱ).IsFlatOver (f ∣_ U) :=
    IsFlatOver.of_comp_isOpenImmersion U.ι (by
      rw [← sq.w]
      exact hℱ.pullback_of_isOpenImmersion _)
  refine isZero_higherDirectImage_of_hFiber_eq_zero (f ∣_ U) _ hflat (d := d)
    (fun y q' hq' ↦ ?_) hq
  rw [hFiber_pullback_of_isPullback f ℱ U.ι _ _ sq]
  -- Grothendieck vanishing on the fibre
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (U.ι y)) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have := LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (U.ι y))
  have : IsNoetherian (f.fiber (U.ι y)) := ⟨⟩
  have : Subsingleton (((Modules.pullback (f.fiberι (U.ι y))).obj ℱ).H q') :=
    Modules.subsingleton_H_of_topologicalKrullDim_lt _
      ((hd _ y.2).trans_lt (by exact_mod_cast hq'))
  let := f.fiberOverSpecResidueField (U.ι y)
  exact Module.finrank_zero_of_subsingleton

/-- **Local vanishing of the higher direct images above the fibre dimension.** With `f : X ⟶ T`
proper of finite presentation and `ℱ` an `𝒪_X`-module of finite presentation which is flat over
`T`, every point of `T` has an open neighbourhood `U` over which the dimensions of the fibres of
`f` are bounded by some `d_U`, and then `R^q f_* ℱ|_U = 0` for all `q > d_U`.

For `U` one can take any affine neighbourhood: finitely many affine opens of finite type over `U`
cover `f⁻¹ U`, which bounds the fibre dimension
(`AlgebraicGeometry.exists_topologicalKrullDim_le_of_isPullback_of_compactSpace`), and the
vanishing is `isZero_higherDirectImage_restrict_of_topologicalKrullDim_le`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem exists_isZero_higherDirectImage_restrict_of_topologicalKrullDim_le
    (hℱ : ℱ.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (d : ℕ), t ∈ U ∧ (∀ s ∈ U, topologicalKrullDim (f.fiber s) ≤ d) ∧
      ∀ q, d < q → IsZero (((higherDirectImage f q).obj ℱ).restrict U.ι) := by
  obtain ⟨U, hU, htU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens) (show t ∈ ⊤ from trivial)
  change T.Opens at U
  have : IsAffine U := hU
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le_of_isPullback_of_compactSpace
    (pullback.snd f U.ι)
  have hd (s : T) (hs : s ∈ U) : topologicalKrullDim (f.fiber s) ≤ n := by
    obtain ⟨g, hg⟩ := exists_comp_ι_eq_fromSpecResidueField hs
    have H : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f (g ≫ U.ι) := by
      rw [hg]
      exact IsPullback.of_hasPullback _ _
    let p : f.fiber s ⟶ Limits.pullback f U.ι :=
      pullback.lift (f.fiberι s) (f.fiberToSpecResidueField s ≫ g) (by
        rw [H.w, Category.assoc])
    exact hn (T.residueField s) g p (f.fiberToSpecResidueField s)
      (IsPullback.of_right (by simpa [p] using H) (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback f U.ι))
  exact ⟨U, n, htU, hd, fun q hq ↦
    isZero_higherDirectImage_restrict_of_topologicalKrullDim_le f ℱ hℱ U hd hq⟩

end Coherence

end AlgebraicGeometry.Scheme.Modules

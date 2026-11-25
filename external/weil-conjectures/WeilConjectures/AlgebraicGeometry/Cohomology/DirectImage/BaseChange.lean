/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.Mathlib.Algebra.BigOperators.Intervals

/-!
# Fibre cohomology under base change and its local constancy

The fibre cohomology dimensions are compatible with base change, and the fibrewise Euler
characteristic is locally constant
(`AlgebraicGeometry.Scheme.Modules.isLocallyConstant_eulerCharFiber`).
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

omit [LocallyOfFinitePresentation f] [HasInjectiveResolutions X.Modules] in
/-- **The fibre dimension is invariant under base change.** Let `f' : X' ⟶ T'` and `g' : X' ⟶ X`
be the base change of `f` along `g : T' ⟶ T`, in the cartesian square `sq`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
and let `ℱ'` be the pullback of `ℱ` to `X'`. Then `h^q_{ℱ'}(t') = h^q_ℱ(g t')` for every point
`t'` of `T'`: the fibre `X'_{t'}` is the base change of `X_{g t'}` along the field extension
`κ(g t') ⟶ κ(t')`, and cohomology commutes with flat base change.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem hFiber_pullback_of_isPullback {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X)
    (f' : X' ⟶ T') (sq : IsPullback g' f' f g) (q : ℕ) (t' : T') :
    ((Modules.pullback g').obj ℱ).hFiber f' q t' = ℱ.hFiber f q (g.base t') := by
  let K := T.residueField (g.base t')
  let L := T'.residueField t'
  let : Algebra K L := (g.residueFieldMap t').hom.toAlgebra
  have hsq := isPullback_fiberToSpecResidueField_of_isPullback sq t'
  let := f.fiberOverSpecResidueField (g.base t')
  let := f'.fiberOverSpecResidueField t'
  have : QuasiCompact (f.fiber (g.base t') ↘ Spec (.of K)) := by
    change QuasiCompact (f.fiberToSpecResidueField _)
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have : QuasiSeparated (f.fiber (g.base t') ↘ Spec (.of K)) := by
    change QuasiSeparated (f.fiberToSpecResidueField _)
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have h := Modules.finrankH_pullback (k := K) L ((Modules.pullback (f.fiberι (g.base t'))).obj ℱ) q
  let φ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hsq' : IsPullback (pullback.map f' (T'.fromSpecResidueField t') f
      (T.fromSpecResidueField (g.base t')) g' (Spec.map (g.residueFieldMap t')) g
      (by simp [sq.w]) (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g t').symm)
      (f'.fiberToSpecResidueField t') (f.fiber (g.base t') ↘ Spec (.of K)) φ := hsq
  let e : f'.fiber t' ≅ Limits.pullback (f.fiber (g.base t') ↘ Spec (.of K)) φ :=
    hsq'.isoPullback
  have : e.hom.IsOver (Spec (.of L)) := by
    rw [Scheme.Hom.isOver_iff]
    exact hsq'.isoPullback_hom_snd
  have hcomp : f'.fiberι t' ≫ g' =
      e.hom ≫ pullback.fst _ _ ≫ f.fiberι (g.base t') := by
    rw [← Category.assoc, hsq'.isoPullback_hom_fst]
    simp [Scheme.Hom.fiberι]
  change ((Modules.pullback (f'.fiberι t')).obj ((Modules.pullback g').obj ℱ)).finrankH L q =
    ((Modules.pullback (f.fiberι (g.base t'))).obj ℱ).finrankH K q
  rw [← h, ← finrankH_pullback_of_isIso (k := L) e.hom]
  exact finrankH_congr _ ((pullbackComp _ _).app ℱ ≪≫ (pullbackCongr hcomp).app ℱ ≪≫
    ((pullbackComp _ _).app ℱ).symm ≪≫ (Modules.pullback e.hom).mapIso
      ((pullbackComp _ _).app ℱ).symm) q

omit [LocallyOfFinitePresentation f] [HasInjectiveResolutions X.Modules] in
/-- **The fibre Euler characteristic is invariant under base change**, in the situation of
`AlgebraicGeometry.Scheme.Modules.hFiber_pullback_of_isPullback`. -/
theorem eulerCharFiber_pullback_of_isPullback {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X)
    (f' : X' ⟶ T') (sq : IsPullback g' f' f g) (t' : T') :
    ((Modules.pullback g').obj ℱ).eulerCharFiber f' t' = ℱ.eulerCharFiber f (g.base t') := by
  simp only [eulerCharFiber, hFiber_pullback_of_isPullback f ℱ g g' f' sq]

/-- **The fibre Euler characteristic is locally constant.** With `f : X ⟶ T` proper of finite
presentation and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, the Euler
characteristic `t ↦ Σ_q (-1)^q dim_{κ(t)} H^q(X_t, ℱ_t)` of the fibres is locally constant on
`T`.

Near a point of `T` it is the alternating sum of the ranks of the bounded complex `P` of finite
free modules of `AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`,
since the Euler characteristic of a bounded complex of finite-dimensional vector spaces is that
of its cohomology.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem isLocallyConstant_eulerCharFiber (hℱ : ℱ.IsFlatOver f) :
    IsLocallyConstant (ℱ.eulerCharFiber f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  obtain ⟨U, P, d, htU, hP, hbc⟩ := exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ t
  choose r e using hP.exists_iso_free
  let e' n := (e n).some
  suffices h : ∀ s ∈ U, ℱ.eulerCharFiber f s =
      ∑ q ∈ Finset.range (d + 1), (-1) ^ q * (r q : ℤ) by
    filter_upwards [U.isOpen.mem_nhds htU] with s hs
    rw [h s hs, h t htU]
  intro s hs
  -- the fibre dimension in each degree, through the fibre `P ⊗ κ(s)`
  obtain ⟨g, hg⟩ := exists_comp_ι_eq_fromSpecResidueField hs
  have hh := hFiber_eq_finrank_homology f ℱ hbc g hg
  have hκ : IsField (T.residueField s) := Field.toIsField _
  have hf := finrank_homology_pullback_add_rank_add_rank e' hκ g
  let a : ℤ → ℕ := fun n ↦
    ((freeMatrix ((e' n).inv ≫ P.d n (n + 1) ≫ (e' (n + 1)).hom)).map g.appTop).rank
  have ha (n m : ℤ) (h : n + 1 = m) : a n =
      ((freeMatrix ((e' n).inv ≫ P.d n m ≫ (e' m).hom)).map g.appTop).rank := by
    subst h
    rfl
  have hq (q : ℕ) : (ℱ.hFiber f q s : ℤ) = r q - a q - a (q - 1) := by
    have := hf q
    rw [← ha (q - 1) q (by omega)] at this
    change _ + a q + _ = _ at this
    rw [hh q]
    omega
  have hzero (n : ℤ) (hn : IsZero (P.X n) ∨ IsZero (P.X (n + 1))) : a n = 0 := by
    have : P.d n (n + 1) = 0 := hn.elim (fun h ↦ h.eq_of_src _ _) (fun h ↦ h.eq_of_tgt _ _)
    simp [a, this, freeMatrix_zero]
  have hP₀ := hP.isStrictlyGE
  have hP₁ := hP.isStrictlyLE
  have ha₀ : a (-1) = 0 := hzero _ (.inl (P.isZero_of_isStrictlyGE 0 (-1) (by omega)))
  have ha₁ : a d = 0 := hzero _ (.inr (P.isZero_of_isStrictlyLE d (d + 1) (by omega)))
  have hvan (q : ℕ) (hq : d < q) : ℱ.hFiber f q s = 0 := by
    rw [hh q]
    have hX : IsZero (((Modules.pullback g).mapHomologicalComplex _).obj P |>.X q) :=
      (Modules.pullback g).map_isZero (P.isZero_of_isStrictlyLE d q (by omega))
    have hH : IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) :=
      ShortComplex.isZero_homology_of_isZero_X₂ _ hX
    have := ModuleCat.subsingleton_of_isZero
      ((moduleSpecΓFunctor (R := T.residueField s)).map_isZero hH)
    exact Module.finrank_zero_of_subsingleton
  rw [eulerCharFiber, finsum_eq_sum_of_support_subset (s := Finset.range (d + 1))]
  · have := Finset.sum_range_neg_one_pow_mul_add_sub_one (fun n ↦ (a n : ℤ)) d
    simp only [ha₀, ha₁, Nat.cast_zero, mul_zero, zero_add] at this
    rw [← sub_zero (∑ q ∈ Finset.range (d + 1), (-1) ^ q * (r q : ℤ)), ← this,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [hq]
    ring
  · intro q hq
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hq
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hq.2 (by rw [hvan q (by omega)]; simp)

/-- **The fibre dimension is locally constant on the perfect locus.** On the perfect locus `U_i`
the fibre dimension `t ↦ dim_{κ(t)} H^i(X_t, ℱ_t)` is locally constant: there it equals
`(-1)^i` times the fibre Euler characteristic, which is locally constant by
`AlgebraicGeometry.Scheme.Modules.isLocallyConstant_eulerCharFiber`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem isLocallyConstant_hFiber_restrict (hℱ : ℱ.IsFlatOver f) (i : ℕ) :
    IsLocallyConstant ((ℱ.perfectLocus f i).domRestrict (ℱ.hFiber f i)) := by
  have h : (ℱ.perfectLocus f i).domRestrict (ℱ.hFiber f i) =
      (fun n : ℤ ↦ ((-1) ^ i * n).toNat) ∘ ℱ.eulerCharFiber f ∘ Subtype.val := by
    ext ⟨t, ht⟩
    rw [Set.domRestrict_apply, Function.comp_apply, Function.comp_apply, eulerCharFiber,
      finsum_eq_single _ i fun q hq ↦ by simp [ht q hq], ← mul_assoc, ← mul_pow, neg_one_mul,
      neg_neg, one_pow, one_mul, Int.toNat_natCast]
  rw [h]
  exact ((isLocallyConstant_eulerCharFiber f ℱ hℱ).comp_continuous continuous_subtype_val).comp _

/-- **Openness of the rank-`r` perfect locus.** The locus `U_{i,r}` is open in `T`: it is the
preimage of `{r}` under the fibre dimension, which is locally constant on the open set `U_i` by
`AlgebraicGeometry.Scheme.Modules.isLocallyConstant_hFiber_restrict`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem isOpen_perfectLocusOfRank (hℱ : ℱ.IsFlatOver f) (i r : ℕ) :
    IsOpen (ℱ.perfectLocusOfRank f i r) := by
  convert (isOpen_perfectLocus f ℱ hℱ i).isOpenMap_subtype_val _
    ((isLocallyConstant_hFiber_restrict f ℱ hℱ i).isOpen_fiber r)
  ext t
  simp only [mem_perfectLocusOfRank, Set.mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, Set.domRestrict_apply]
  exact ⟨fun ⟨ht, hr⟩ ↦ ⟨ht, hr⟩, fun ⟨ht, hr⟩ ↦ ⟨ht, hr⟩⟩

/-- **Openness of `U_{i,r}`.** The locus of points `t` of `T` at which the fibre cohomology
`H^q(X_t, ℱ_t)` vanishes for all `q ≠ i` and has dimension `r` in degree `i` is open in `T`. This
is `AlgebraicGeometry.Scheme.Modules.isOpen_perfectLocusOfRank`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem isOpen_setOf_hFiber_eq (hℱ : ℱ.IsFlatOver f) (i r : ℕ) :
    IsOpen {t : T | (∀ q ≠ i, ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r} :=
  isOpen_perfectLocusOfRank f ℱ hℱ i r

end Coherence

end AlgebraicGeometry.Scheme.Modules

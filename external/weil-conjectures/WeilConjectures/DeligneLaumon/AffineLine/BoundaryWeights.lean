/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.PointCountFiber
public import WeilConjectures.WeilSheaf.FourierTrace
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity
public import WeilConjectures.WeilSheaf.ShiftedSheaf
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TraceBound

/-!
# The weights of the transform of the boundary sheaf

Let `M` be a lisse Weil sheaf on a dense open `j : U₀ ↪ 𝔸¹` with weights at most `w`, and let
`B = j_*M / j_!M` be its boundary sheaf, supported on the finite complement `S₀` of `U₀`. If the
Fourier transform of `B` is a shifted Weil sheaf `B'[1]`, then `B'` has weights at most `w`
(Step 4 of `lemma-fourier-transform-boundary-sequence`).

By boundary semicontinuity `j_*M`, hence its quotient `B`, has weights at most `w`. The Fourier
trace formula writes the trace function of `B'` as the finite sum

`t_{B'}(y) = ∑_{x ∈ S₀(𝔽_{qⁿ})} t_B(x) ψ(Tr(x y))`,

whose terms are bounded by `N q^{nw/2}` since the Artin–Schreier values `ψ(Tr(x y))` are roots
of unity, and which has at most `∑_{s ∈ S₀} deg s` terms. At a closed point `y` of degree `d`
the traces of the powers `F_yᵐ` are values of `t_{B'}` at `𝔽_{q^{md}}`-points over `y`, so
they are `O(q_y^{mw/2})`, and the eigenvalues of `F_y` have absolute value at most `q_y^{w/2}`
(`FrobeniusModule.hasWeightsAtMost_of_norm_map_trace_pow_le`).

## Main statements

- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_of_forall_norm_traceFunction_le`: a bound
  `O(q^{nw/2})` on the trace function gives weights at most `w`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isZero_upperStar_boundarySheaf`: the boundary
  sheaf vanishes on `U₀`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMost_of_iso_fourierTransform`: the
  weight bound for `B'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- A closed point `x` of degree `d` lies under an `𝔽_{q^{md}}`-rational point for every `m`:
its residue field embeds into the field with `q^{md}` elements. -/
theorem exists_fieldPoints_base_eq (x : X.finitePoints) (m : ℕ) (hm : m ≠ 0) :
    ∃ y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints
        (FiniteField.galoisExtension k₀ (m * (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1)),
      y.1.base (IsLocalRing.closedPoint _) = x.1 := by
  set f := X ↘ Spec (CommRingCat.of k₀)
  let := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := x.2
  have : FiniteDimensional k₀ (X.residueField x.1) := Module.Finite.of_finite
  have : Finite (FiniteField.galoisExtension k₀ (m * f.degreeOver x.1)) :=
    Module.finite_of_finite k₀
  have hd : f.degreeOver x.1 ≠ 0 := Scheme.Hom.degreeOver_ne_zero _ x.2
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := k₀) (K := X.residueField x.1)
    (L := FiniteField.galoisExtension k₀ (m * f.degreeOver x.1))
    (by rw [FiniteField.finrank_galoisExtension _ _ (mul_ne_zero hm hd)]; exact dvd_mul_left _ _)
  obtain ⟨y, hy⟩ := (f.exists_fieldPoints_base_eq_iff _ x.1).2
    ⟨CommRingCat.ofHom φ.toRingHom, RingHom.ext fun a ↦ φ.commutes a⟩
  exact ⟨y, (congrArg y.1.base (Subsingleton.elim _ _)).trans hy⟩

/-- **Weights from trace bounds.** If the trace function of a Weil sheaf `F` satisfies
`|ι t_{F,n}(y)| ≤ C q^{nw/2}` at all rational points, then `F` has weights at most `w`: at a
closed point `x` of degree `d` the trace of `F_xᵐ` is the value of the trace function at an
`𝔽_{q^{md}}`-point over `x`, so it is at most `C (q_x^{w/2})ᵐ`. -/
theorem hasWeightsAtMost_of_forall_norm_traceFunction_le (F : WeilSheaf k₀ l X)
    {ι : PadicAlgCl l →+* ℂ} {w C : ℝ}
    (h : ∀ n : ℕ, n ≠ 0 → ∀ y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n),
        ‖ι (F.traceFunction n y)‖ ≤ C * ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ n) :
    WeilSheaf.HasWeightsAtMost ι F w := by
  intro x
  set f := X ↘ Spec (CommRingCat.of k₀)
  have hd : f.degreeOver x.1 ≠ 0 := Scheme.Hom.degreeOver_ne_zero _ x.2
  have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
  refine FrobeniusModule.hasWeightsAtMost_of_norm_map_trace_pow_le
    (Nat.one_le_pow _ _ Nat.card_pos) _ (C := C) fun m hm ↦ ?_
  obtain ⟨y, hy⟩ := exists_fieldPoints_base_eq (k₀ := k₀) x m (by omega)
  have ht := F.traceFunction_eq_trace_frobeniusEnd_stalk_pow _ y x hy
  rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd)] at ht
  rw [← ht]
  refine (h _ (mul_ne_zero (by omega) hd) y).trans_eq ?_
  rw [Nat.cast_pow,
    ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul hq, ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul hq]
  congr 2
  push_cast
  ring

end WeilSheaf

namespace WeilSheaf.LisseOnDenseOpen

variable (D : LisseOnDenseOpen k₀ l)

/-- **The boundary sheaf vanishes on `U₀`**: the restriction of `j_!M ⟶ j_*M` to `U₀` is an
isomorphism, and the restriction is exact. -/
theorem isZero_upperStar_boundarySheaf :
    IsZero ((WeilSheaf.upperStar D.j).obj D.boundarySheaf) := by
  rw [isZero_iff_isZero_carrier]
  have hj : IsOpenImmersion (Scheme.Hom.geometricFiberMap D.j
      (comp_over D.j (Spec (CommRingCat.of k₀)))) := inferInstance
  set jb := Scheme.Hom.geometricFiberMap D.j (comp_over D.j (Spec (CommRingCat.of k₀)))
  let Φ := (WeilSheaf.objectProperty k₀ l (affineLine k₀)).ι ⋙
    IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀))
  have h₀ : PreservesFiniteColimits (C := WeilSheaf k₀ l (affineLine k₀))
      (WeilSheaf.objectProperty k₀ l (affineLine k₀)).ι := inferInstance
  have h₁ : PreservesColimitsOfShape (C := WeilSheaf k₀ l (affineLine k₀)) WalkingParallelPair
      (WeilSheaf.objectProperty k₀ l (affineLine k₀)).ι := inferInstance
  have h₂ : PreservesColimitsOfShape WalkingParallelPair
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀))) := inferInstance
  have : PreservesColimitsOfShape WalkingParallelPair Φ :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (_ ⋙ _))
  have : PreservesColimits (jb)^*ᵃ[l] :=
    (ProEtale.adicUpperStarLowerStarAdjunction l jb).leftAdjoint_preservesColimits
  have hc : Φ.map ((WeilSheaf.extensionByZeroToDirectImage D.j).app D.sheaf) =
      (ProEtale.adicOpenImmersionLowerShriekToLowerStar l jb).app D.sheaf.obj.carrier := rfl
  have : IsIso ((jb)^*ᵃ[l].map
      ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l jb).app D.sheaf.obj.carrier)) := by
    have : IsIso ((ProEtale.adicOpenImmersionLowerShriekAdjunction l jb).unit.app
        D.sheaf.obj.carrier ≫ (jb)^*ᵃ[l].map
          ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l jb).app D.sheaf.obj.carrier)) := by
      rw [ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((ProEtale.adicOpenImmersionLowerShriekAdjunction l jb).unit.app D.sheaf.obj.carrier) _
  have : Epi ((jb)^*ᵃ[l].map
      ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l jb).app D.sheaf.obj.carrier)) :=
    IsIso.epi_of_iso _
  change IsZero ((jb)^*ᵃ[l].obj (Φ.obj (cokernel
    ((WeilSheaf.extensionByZeroToDirectImage D.j).app D.sheaf))))
  refine IsZero.of_iso (isZero_cokernel_of_epi ((jb)^*ᵃ[l].map
      ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l jb).app D.sheaf.obj.carrier)))
    ((jb)^*ᵃ[l].mapIso (PreservesCokernel.iso Φ _ ≪≫ cokernel.mapIso _ _ (Iso.refl _)
      (Iso.refl _) (by rw [hc]; simp)) ≪≫ PreservesCokernel.iso _ _)

/-- A rational point of the affine line whose closed point lies in `U₀` comes from `U₀`. -/
private lemma exists_mapFieldPoints_eq {K : Type u} [Field K] [Algebra k₀ K]
    (y : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints K)
    (hy : y.1.base (IsLocalRing.closedPoint _) ∈ Set.range D.j.base) :
    ∃ y' : (D.U ↘ Spec (CommRingCat.of k₀)).fieldPoints K, D.j.mapFieldPoints _ y' = y := by
  obtain ⟨u, hu⟩ := hy
  have hr : Set.range y.1.base ⊆ Set.range D.j.base := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint _)]
    exact ⟨u, hu⟩
  refine ⟨⟨IsOpenImmersion.lift D.j y.1 hr, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  rw [← comp_over D.j (Spec (CommRingCat.of k₀)), ← Category.assoc, IsOpenImmersion.lift_fac]
  exact y.2

/-- The trace function of the boundary sheaf vanishes at the rational points of `U₀`. -/
theorem traceFunction_boundarySheaf_eq_zero {n : ℕ}
    (y : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n))
    (hy : y.1.base (IsLocalRing.closedPoint _) ∈ Set.range D.j.base) :
    D.boundarySheaf.traceFunction n y = 0 := by
  obtain ⟨y', rfl⟩ := D.exists_mapFieldPoints_eq y hy
  rw [← traceFunction_upperStar]
  exact traceFunction_eq_zero_of_isZero _ D.isZero_upperStar_boundarySheaf n y'

/-- The boundary sheaf has weights at most `w` when `M` has: it is a quotient of `j_*M`, which
has weights at most `w` by boundary semicontinuity. -/
theorem hasWeightsAtMost_boundarySheaf {ι : PadicAlgCl l →+* ℂ} {w : ℝ}
    (h : D.sheaf.HasWeightsAtMost ι w) : D.boundarySheaf.HasWeightsAtMost ι w := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have : GeometricallyConnected (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  exact HasWeightsAtMost.of_epi (cokernel.π _)
    (WeilSheaf.hasWeightsAtMost_directImage D.j ι D.lisse h)

omit [Fact (ringChar k₀ ≠ l)] in
/-- The values of an additive character of a finite field have absolute value one: they are
roots of unity. -/
private lemma norm_map_addChar (ι : PadicAlgCl l →+* ℂ) (ψ : AddChar k₀ (PadicAlgCl l))
    (a : k₀) : ‖ι (ψ a)‖ = 1 := by
  have : Fintype k₀ := Fintype.ofFinite k₀
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card k₀) ?_ Nat.card_pos.ne'
  rw [← map_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.card_eq_fintype_card,
    FiniteField.cast_card_eq_zero, zero_mul, AddChar.map_zero_eq_one, map_one]

/-- **The trace bound for the transform of the boundary sheaf.** There is a constant `C` such
that `|ι ∑_x t_B(x) ψ(Tr(x y))| ≤ C q^{nw/2}` at every `𝔽_{qⁿ}`-point `y`: only the finitely
many points over the boundary contribute, each by at most `N q^{nw/2}`. -/
theorem exists_forall_norm_sum_traceFunction_boundarySheaf_le (ψ : AddChar k₀ (PadicAlgCl l))
    {ι : PadicAlgCl l →+* ℂ} {w : ℝ} (hB : D.boundarySheaf.HasWeightsAtMost ι w) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ y : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
        (FiniteField.galoisExtension k₀ n),
      ‖ι (∑ᶠ x : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
          (FiniteField.galoisExtension k₀ n),
        D.boundarySheaf.traceFunction n x * ψ (Algebra.trace k₀ (FiniteField.galoisExtension k₀ n)
          (AffineSpace.fieldPointsEquiv k₀ _ x * AffineSpace.fieldPointsEquiv k₀ _ y)))‖ ≤
        C * ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ n := by
  classical
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  -- the boundary is a finite set of closed points
  have : Nonempty (affineLine k₀) :=
    ⟨(AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k₀))) 0).base (IsLocalRing.closedPoint k₀)⟩
  have hU : (Set.range D.j.base).Nonempty := by
    have : Nonempty D.U := D.j.denseRange.nonempty_iff.2 ‹_›
    exact Set.range_nonempty _
  have := LocallyOfFiniteType.isLocallyNoetherian (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian (affineLine k₀) := ⟨⟩
  have hfin : (Set.range D.j.base)ᶜ.Finite :=
    D.j.isOpenEmbedding.isOpen_range.finite_compl_of_topologicalKrullDim_le_one
      (topologicalKrullDim_le_of_smoothOfRelativeDimension
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) 1) hU
  let S : Finset (affineLine k₀).finitePoints :=
    (hfin.preimage Subtype.val_injective.injOn).toFinset
  have hS (x : (affineLine k₀).finitePoints) : x ∈ S ↔ x.1 ∉ Set.range D.j.base := by
    simp [S]
  let N : ℕ := S.sup fun x ↦ Module.finrank (PadicAlgCl l) (D.boundarySheaf.stalk x).carrier
  let d : ℕ := ∑ x ∈ S, (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).degreeOver x.1
  refine ⟨d * N, fun n y ↦ ?_⟩
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  have := (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).finite_fieldPoints
    (FiniteField.galoisExtension k₀ n)
  set s := {x : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
    (FiniteField.galoisExtension k₀ n) | x.1.base (IsLocalRing.closedPoint _) ∉ Set.range D.j.base}
  have hs : s.Finite := Set.toFinite s
  have hq : (0 : ℝ) ≤ ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ n := by positivity
  -- only the points over the boundary contribute
  rw [finsum_eq_sum_of_support_subset _ (s := hs.toFinset) fun x hx ↦ ?_]
  swap
  · rw [Set.Finite.coe_toFinset]
    by_contra hxs
    rw [Function.mem_support] at hx
    exact hx (by
      change D.boundarySheaf.traceFunction n x * _ = 0
      rw [D.traceFunction_boundarySheaf_eq_zero x (not_not.1 hxs), zero_mul])
  rw [map_sum]
  -- each term is at most `N q^{nw/2}`
  have hterm (x) (hx : x ∈ hs.toFinset) : ‖ι (D.boundarySheaf.traceFunction n x *
      ψ (Algebra.trace k₀ (FiniteField.galoisExtension k₀ n)
        (AffineSpace.fieldPointsEquiv k₀ _ x * AffineSpace.fieldPointsEquiv k₀ _ y)))‖ ≤
      N * ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ n := by
    rw [map_mul, norm_mul, norm_map_addChar, mul_one]
    refine (norm_map_traceFunction_le hB n x).trans ?_
    gcongr
    exact_mod_cast Finset.le_sup (f := fun x ↦ Module.finrank (PadicAlgCl l)
      (D.boundarySheaf.stalk x).carrier) ((hS (finitePointOfFieldPoint x)).2 (hs.mem_toFinset.1 hx))
  -- there are at most `d` boundary points
  have hcard : hs.toFinset.card ≤ d := by
    rw [Finset.card_eq_sum_card_fiberwise (f := finitePointOfFieldPoint) (t := S)
      (fun x hx ↦ (hS _).2 (hs.mem_toFinset.1 hx))]
    refine Finset.sum_le_sum fun x hx ↦ ?_
    calc _ ≤ Nat.card {p : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
          (FiniteField.galoisExtension k₀ n) // p.1.base (IsLocalRing.closedPoint _) = x.1} := by
          rw [← Nat.card_eq_finsetCard]
          refine Nat.card_le_card_of_injective (fun p ↦ ⟨p.1, congrArg Subtype.val
            (Finset.mem_filter.1 p.2).2⟩) fun p p' h ↦ Subtype.ext (by
              simpa using congrArg Subtype.val h)
      _ ≤ _ := (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).card_fieldPoints_base_eq_le _ x.2
  calc ‖∑ x ∈ hs.toFinset, ι (D.boundarySheaf.traceFunction n x *
        ψ (Algebra.trace k₀ (FiniteField.galoisExtension k₀ n)
          (AffineSpace.fieldPointsEquiv k₀ _ x * AffineSpace.fieldPointsEquiv k₀ _ y)))‖
      ≤ ∑ x ∈ hs.toFinset, ‖ι (D.boundarySheaf.traceFunction n x *
        ψ (Algebra.trace k₀ (FiniteField.galoisExtension k₀ n)
          (AffineSpace.fieldPointsEquiv k₀ _ x * AffineSpace.fieldPointsEquiv k₀ _ y)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x ∈ hs.toFinset, N * ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ n := Finset.sum_le_sum hterm
    _ = hs.toFinset.card * (N * ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ n) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ d * (N * ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ n) := by gcongr
    _ = _ := by ring

/-- The Fourier trace formula as a sum over the rational points of the affine line:
`t_{FT_ψ(K)}(y) = -∑_x t_K(x) ψ(Tr(x y))`. -/
private lemma traceFunction_fourierTransform_eq_neg_finsum (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l (affineLine k₀)) {n : ℕ} (hn : n ≠ 0)
    (y : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n)) :
    ((fourierTransform ψ).obj K).traceFunction n y =
      -∑ᶠ x : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
          (FiniteField.galoisExtension k₀ n),
        K.traceFunction n x * ψ (Algebra.trace k₀ (FiniteField.galoisExtension k₀ n)
          (AffineSpace.fieldPointsEquiv k₀ _ x * AffineSpace.fieldPointsEquiv k₀ _ y)) := by
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  have : Fintype (FiniteField.galoisExtension k₀ n) := Fintype.ofFinite _
  have h := WeilComplex.traceFunction_fourierTransform ψ K hn
    (AffineSpace.fieldPointsEquiv k₀ _ y)
  simp only [WeilComplex.affineLineTraceFunction, Equiv.symm_apply_apply] at h
  rw [h, FiniteField.fourierTransform, ← finsum_eq_sum_of_fintype,
    ← finsum_comp_equiv (AffineSpace.fieldPointsEquiv k₀ _)]
  simp only [WeilComplex.affineLineTraceFunction, Equiv.symm_apply_apply]

/-- **The transform of the boundary sheaf has weights at most `w`** (Step 4 of
`lemma-fourier-transform-boundary-sequence`): if `FT_ψ(B) ≅ B'[1]` and `M` has weights at most `w`,
then `B'` has weights at most `w`. By the Fourier trace formula
`t_{B'}(y) = ∑_x t_B(x) ψ(Tr(x y))`, a sum over the points of the boundary, so the trace
function of `B'` is `O(q^{nw/2})`. (blueprint: `lemma-fourier-transform-boundary-sequence`) -/
theorem hasWeightsAtMost_of_iso_fourierTransform (ψ : AddChar k₀ (PadicAlgCl l))
    {ι : PadicAlgCl l →+* ℂ} {w : ℝ} (hw : D.sheaf.HasWeightsAtMost ι w)
    {B' : WeilSheaf k₀ l (affineLine k₀)}
    (e : (fourierTransform ψ).obj (WeilSheaf.toComplex.obj D.boundarySheaf) ≅
      WeilSheaf.toShiftedComplex.obj B') :
    B'.HasWeightsAtMost ι w := by
  obtain ⟨C, hC⟩ :=
    D.exists_forall_norm_sum_traceFunction_boundarySheaf_le ψ (D.hasWeightsAtMost_boundarySheaf hw)
  refine B'.hasWeightsAtMost_of_forall_norm_traceFunction_le (C := C) fun n hn y ↦ ?_
  have h := WeilComplex.traceFunction_eq_of_iso e n y
  rw [WeilComplex.traceFunction_toShiftedComplex,
    traceFunction_fourierTransform_eq_neg_finsum ψ _ hn] at h
  simp only [WeilComplex.traceFunction_toComplex] at h
  rw [← neg_inj.1 h]
  exact hC n y

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry

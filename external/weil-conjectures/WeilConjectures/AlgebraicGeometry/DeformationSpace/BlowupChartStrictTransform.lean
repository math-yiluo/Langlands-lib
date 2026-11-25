/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BlowupChart
public import WeilConjectures.Compactification.BoundarySeparationData

/-!
# The Rees chart is the complement of the strict transform of the zero fibre

Let `R` be a ring, `I ⊆ R` an ideal and `J = I R[t] + (t)`. In the blow-up
`Bl_J (Spec R[t])` let `S` be the inverse image of the part of the zero fibre `V(t) = Spec R`
lying off the center `V(J)`. Its closure is the (underlying set of the) strict transform of
`V(t)`. We show that the complement of this closure is exactly the basic open `D₊(t·X)`, which
is the spectrum of the extended Rees algebra `R[t, I t⁻¹]`
(`AlgebraicGeometry.AffineBlowup.deformationChart`). Hence, affine-locally,

`Spec R[t, I t⁻¹] ≅ Bl_{V(I) × 0} (Spec R × 𝔸¹) ∖ (strict transform of Spec R × 0)`,

which is the blow-up description of the deformation to the normal cone in blueprint
`definition-deformation-normal-bundle`.

The two inclusions:
- on `D₊(t·X) = Spec R[t, I t⁻¹]`, if `t` vanishes at a point then so does `x = (x t⁻¹)·t` for
  every `x ∈ I`, so the point lies over the center;
- on a chart `D₊(c·X)`, `c ∈ I`, with coordinate ring `R[t][J/c]` and `u = t / c`, every element
  is `κ(r) + u·e` with `r ∈ R_c`; so the kernel of `R[t][J/c] → R_c`, `t ↦ 0`, is `(u)`, and
  `V(u)` is the closure of the image of `Spec R_c`, which lies over `V(t)` off the center.
-/

@[expose] public section

universe u

open CategoryTheory Polynomial HomogeneousLocalization

namespace AlgebraicGeometry.AffineBlowup

variable {R : Type u} [CommRing R] (I : Ideal R)

variable (R) in
/-- The zero fibre `V(t) = Spec R ⟶ Spec R[t]`. -/
noncomputable def zeroFibre : Spec (.of R) ⟶ Spec (.of R[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.constantCoeff (R := R)))

/-- The complement of the center `V(J)`, `J = I R[t] + (t)`, in `Spec R[t]`. -/
noncomputable def centerCompl : (Spec (.of R[X])).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (deformationCenter I : Set R[X]))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- The points of the blow-up lying over the zero fibre `V(t)` but off the center. Its closure is
the strict transform of the zero fibre. -/
noncomputable abbrev zeroFibreOffCenter : Set (AffineBlowup (deformationCenter I)) :=
  toSpec (deformationCenter I) ⁻¹' ((centerCompl I : Set (Spec (.of R[X]))) ∩
    Set.range (zeroFibre R))

lemma X_mem_of_mem_range_zeroFibre {P : Spec (.of R[X])} (hP : P ∈ Set.range (zeroFibre R)) :
    (X : R[X]) ∈ P.asIdeal := by
  obtain ⟨Q, rfl⟩ := hP
  rw [zeroFibre, Spec.map_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  simp

/-- `D₊(t·X)` does not meet the locus over the zero fibre off the center. -/
lemma disjoint_opensRange_deformationChart :
    Disjoint ((deformationChart I).opensRange : Set (AffineBlowup (deformationCenter I)))
      (zeroFibreOffCenter I) := by
  rw [Set.disjoint_left]
  rintro y hy ⟨hU, hZ⟩
  obtain ⟨q, rfl⟩ := hy
  rw [← Scheme.Hom.comp_apply, deformationChart_toSpec] at hU hZ
  have hT : I.extendedReesAlgebraT ∈ q.asIdeal := by
    have := X_mem_of_mem_range_zeroFibre hZ
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at this
    simpa using this
  apply hU
  intro p hp
  change p ∈ (PrimeSpectrum.comap _ q).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, CommRingCat.hom_ofHom, ← X_mul_divX_add p,
    map_add, map_mul, Ideal.toExtendedReesAlgebra_X]
  refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hT) ?_
  have e : I.toExtendedReesAlgebra (Polynomial.C (p.coeff 0)) =
      ⟨LaurentPolynomial.C (p.coeff 0) * LaurentPolynomial.T (-1),
        Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra
          (coeff_zero_mem_of_mem_deformationCenter hp)⟩ * I.extendedReesAlgebraT := by
    apply Subtype.ext
    simp [LaurentPolynomial.mul_T_assoc]
  rw [e]
  exact Ideal.mul_mem_left _ _ hT

/-- The charts at `t·X` and at the `c·X`, `c ∈ I`, cover the blow-up. -/
lemma mem_opensRange_deformationChart_or_exists (y : AffineBlowup (deformationCenter I)) :
    y ∈ (deformationChart I).opensRange ∨
      ∃ (c : R) (hc : c ∈ I), y ∈ (chart (deformationCenter I) _
        (reesX_mem _ _ (C_mem_deformationCenter hc))).opensRange := by
  let f : Option I → reesAlgebra (deformationCenter I) := fun o ↦
    o.elim (reesX _ X X_mem_deformationCenter)
      (fun c ↦ reesX _ (Polynomial.C (c : R)) (C_mem_deformationCenter c.2))
  have hf : (HomogeneousIdeal.irrelevant (reesGrading (deformationCenter I))).toIdeal ≤
      Ideal.span (Set.range f) := by
    refine (irrelevant_le_span_range_reesX _).trans (Ideal.span_le.mpr ?_)
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have hx0 := coeff_zero_mem_of_mem_deformationCenter hx
    have hdeg0 : divX x ∈ deformationCenter I ^ 0 := by
      rw [pow_zero, Ideal.one_eq_top]; trivial
    have e : reesX _ x hx = reesMonomial _ (divX x) hdeg0 * f none + f (some ⟨_, hx0⟩) := by
      apply Subtype.ext
      simp only [f, Option.elim, MulMemClass.coe_mul, AddMemClass.coe_add, coe_reesX,
        coe_reesMonomial, monomial_mul_monomial, zero_add]
      rw [← map_add, divX_mul_X_add]
    change reesX _ x hx ∈ _
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨none, rfl⟩))
      (Ideal.subset_span ⟨some _, rfl⟩)
  have hy : y ∈ ⨆ o, Proj.basicOpen (reesGrading (deformationCenter I)) (f o) := by
    rw [Proj.iSup_basicOpen_eq_top _ f hf]; trivial
  obtain ⟨o, ho⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  cases o with
  | none => rw [opensRange_deformationChart]; exact Or.inl ho
  | some c => exact Or.inr ⟨c, c.2, by rw [opensRange_chart]; exact ho⟩

/-! ### The charts at `c·X`, `c ∈ I` -/

section Chart

variable {I} {c : R}

variable (c) in
/-- `R_c ⟶ R[t]_c`, induced by `R ⊆ R[t]`. -/
noncomputable def constAway : Localization.Away c →+* Localization.Away (Polynomial.C c : R[X]) :=
  IsLocalization.map (M := Submonoid.powers c) (S := Localization.Away c)
    (T := Submonoid.powers (Polynomial.C c)) _ (Polynomial.C : R →+* R[X])
    (Submonoid.powers_le.mpr (Submonoid.mem_powers _))

variable (c) in
/-- `R[t]_c ⟶ R_c`, induced by `t ↦ 0`. -/
noncomputable def evalAway : Localization.Away (Polynomial.C c : R[X]) →+* Localization.Away c :=
  IsLocalization.map (M := Submonoid.powers (Polynomial.C c : R[X]))
    (S := Localization.Away (Polynomial.C c : R[X])) (T := Submonoid.powers c) _
    (Polynomial.constantCoeff (R := R))
    (Submonoid.powers_le.mpr (by
      change Polynomial.constantCoeff (Polynomial.C c) ∈ Submonoid.powers c
      simp))

lemma evalAway_algebraMap (p : R[X]) :
    evalAway c (algebraMap _ _ p) = algebraMap R _ (p.coeff 0) := by
  simp [evalAway, IsLocalization.map_eq]

lemma constAway_algebraMap (a : R) :
    constAway c (algebraMap R _ a) = algebraMap R[X] _ (Polynomial.C a) := by
  simp [constAway, IsLocalization.map_eq]

lemma evalAway_constAway (r : Localization.Away c) : evalAway c (constAway c r) = r := by
  have : (evalAway c).comp (constAway c) = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers c) (by ext a; simp [constAway_algebraMap,
      evalAway_algebraMap])
  exact congr($this r)

lemma evalAway_chartFraction_X : evalAway c (chartFraction (Polynomial.C c) 1 X) = 0 := by
  unfold chartFraction
  rw [Localization.mk_eq_mk', evalAway, IsLocalization.map_mk']
  simp

lemma chartFraction_X_mem :
    chartFraction (Polynomial.C c) 1 X ∈ chartRing (deformationCenter I) (Polynomial.C c) :=
  chartFraction_mem_chartRing _ (by rw [pow_one]; exact X_mem_deformationCenter)

lemma algebraMap_X_eq :
    (algebraMap R[X] (Localization.Away (Polynomial.C c : R[X])) X) =
      chartFraction (Polynomial.C c) 1 X * algebraMap _ _ (Polynomial.C c) := by
  rw [← chartFraction_zero, ← chartFraction_zero, ← chartFraction_mul, chartFraction_eq_iff]
  exact ⟨0, by ring⟩

/-- Every element of the chart algebra `R[t][J/c]` is `κ(r) + (t/c)·e`. -/
lemma exists_eq_constAway_add {z : Localization.Away (Polynomial.C c : R[X])}
    (hz : z ∈ chartRing (deformationCenter I) (Polynomial.C c)) :
    ∃ r, constAway c r ∈ chartRing (deformationCenter I) (Polynomial.C c) ∧
      ∃ e ∈ chartRing (deformationCenter I) (Polynomial.C c),
        z = constAway c r + chartFraction (Polynomial.C c) 1 X * e := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨⟨x, hx⟩, rfl⟩ := hz
    have hx0 := coeff_zero_mem_of_mem_deformationCenter hx
    have hk : constAway c (Localization.mk (x.coeff 0) ⟨c ^ 1, 1, rfl⟩) =
        chartFraction (Polynomial.C c) 1 (Polynomial.C (x.coeff 0)) := by
      unfold chartFraction
      rw [Localization.mk_eq_mk', constAway, IsLocalization.map_mk',
        Localization.mk_eq_mk']
      congr 1
      exact Subtype.ext (by simp)
    refine ⟨Localization.mk (x.coeff 0) ⟨c ^ 1, 1, rfl⟩, ?_, algebraMap _ _ (divX x),
      Subalgebra.algebraMap_mem _ _, ?_⟩
    · rw [hk]
      exact chartFraction_mem_chartRing _ (by rw [pow_one]; exact C_mem_deformationCenter hx0)
    · change chartFraction (Polynomial.C c) 1 x = _
      rw [hk, ← chartFraction_zero, ← chartFraction_mul, add_zero, ← chartFraction_add,
        add_comm (Polynomial.C _), X_mul_divX_add]
  | algebraMap p =>
    refine ⟨algebraMap R _ (p.coeff 0), ?_, algebraMap _ _ (Polynomial.C c * divX p),
      Subalgebra.algebraMap_mem _ _, ?_⟩
    · rw [constAway_algebraMap]; exact Subalgebra.algebraMap_mem _ _
    · rw [constAway_algebraMap]
      conv_lhs => rw [← X_mul_divX_add p]
      rw [map_add, map_mul, map_mul, algebraMap_X_eq]
      ring
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, e, he, rfl⟩ := hx
    obtain ⟨r', hr', e', he', rfl⟩ := hy
    exact ⟨r + r', by rw [map_add]; exact Subalgebra.add_mem _ hr hr', e + e',
      Subalgebra.add_mem _ he he', by rw [map_add]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨r, hr, e, he, rfl⟩ := hx
    obtain ⟨r', hr', e', he', rfl⟩ := hy
    have hu := chartFraction_X_mem (I := I) (c := c)
    refine ⟨r * r', by rw [map_mul]; exact Subalgebra.mul_mem _ hr hr',
      e * constAway c r' + constAway c r * e' + chartFraction (Polynomial.C c) 1 X * e * e', ?_,
      by rw [map_mul]; ring⟩
    exact Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.mul_mem _ he hr')
      (Subalgebra.mul_mem _ hr he')) (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hu he) he')

/-- The kernel of `R[t][J/c] ⟶ R_c`, `t ↦ 0`, is generated by `t / c`. -/
lemma exists_eq_mul_of_evalAway_eq_zero {z : Localization.Away (Polynomial.C c : R[X])}
    (hz : z ∈ chartRing (deformationCenter I) (Polynomial.C c)) (h0 : evalAway c z = 0) :
    ∃ e ∈ chartRing (deformationCenter I) (Polynomial.C c),
      z = chartFraction (Polynomial.C c) 1 X * e := by
  obtain ⟨r, -, e, he, rfl⟩ := exists_eq_constAway_add hz
  rw [map_add, map_mul, evalAway_constAway, evalAway_chartFraction_X, zero_mul, add_zero] at h0
  exact ⟨e, he, by rw [h0, map_zero, zero_add]⟩

end Chart
/-! ### The chart at `c·X` in terms of the homogeneous localization -/

section AwayChart

variable {I} {c : R}

/-- The map `Away (reesGrading J) (c·X) ⟶ R_c`, `t ↦ 0`, through `R[t][J/c] ⊆ R[t]_c`. -/
noncomputable def chartToAway (hc : c ∈ I) :
    HomogeneousLocalization.Away (reesGrading (deformationCenter I))
      (reesX _ (Polynomial.C c) (C_mem_deformationCenter hc)) →+* Localization.Away c :=
  (evalAway c).comp ((chartRing _ _).val.toRingHom.comp
    (homogeneousAwayToChart _ (C_mem_deformationCenter hc)))

lemma homogeneousAwayToChart_isLocalizationElem (hc : c ∈ I) :
    (homogeneousAwayToChart _ (C_mem_deformationCenter hc)
      (Away.isLocalizationElem (reesX_mem _ _ (C_mem_deformationCenter hc))
        (reesX_mem _ X X_mem_deformationCenter)) : Localization.Away (Polynomial.C c : R[X])) =
      chartFraction (Polynomial.C c) 1 X := by
  have h1 : (X : R[X]) ∈ deformationCenter I ^ 1 := by
    rw [pow_one]; exact X_mem_deformationCenter
  have e : Away.isLocalizationElem (reesX_mem _ _ (C_mem_deformationCenter hc))
        (reesX_mem _ X X_mem_deformationCenter) =
      Away.mk _ (reesX_mem _ _ (C_mem_deformationCenter hc)) 1 (reesMonomial _ X h1)
        (by simpa using reesMonomial_mem _ X h1) := by
    simp only [Away.isLocalizationElem, pow_one]
    rfl
  rw [e, coe_homogeneousAwayToChart_mk]

lemma ker_chartToAway_le (hc : c ∈ I) :
    RingHom.ker (chartToAway hc) ≤ Ideal.span
      {Away.isLocalizationElem (reesX_mem _ _ (C_mem_deformationCenter hc))
        (reesX_mem _ X X_mem_deformationCenter)} := by
  intro z hz
  obtain ⟨e, he, h⟩ := exists_eq_mul_of_evalAway_eq_zero
    (homogeneousAwayToChart _ (C_mem_deformationCenter hc) z).2 (RingHom.mem_ker.mp hz)
  obtain ⟨e', he'⟩ := homogeneousAwayToChart_surjective _ (C_mem_deformationCenter hc) ⟨e, he⟩
  have : z = Away.isLocalizationElem (reesX_mem _ _ (C_mem_deformationCenter hc))
      (reesX_mem _ X X_mem_deformationCenter) * e' := by
    refine homogeneousAwayToChart_injective _ (C_mem_deformationCenter hc) (Subtype.ext ?_)
    rw [map_mul, Subalgebra.coe_mul, homogeneousAwayToChart_isLocalizationElem hc, he', h]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

lemma chartToAway_comp_awayAlgebraMap (hc : c ∈ I) :
    (chartToAway hc).comp (awayAlgebraMap _ _) =
      (algebraMap R (Localization.Away c)).comp Polynomial.constantCoeff := by
  refine RingHom.ext fun p ↦ ?_
  simp only [chartToAway, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Subalgebra.coe_val, homogeneousAwayToChart_awayAlgebraMap, Subalgebra.coe_algebraMap,
    evalAway_algebraMap, Polynomial.constantCoeff_apply]

/-- A point of the chart at `c·X` outside `D₊(t·X)` lies in the closure of the locus over the
zero fibre off the center. -/
lemma chart_mem_closure_zeroFibreOffCenter (hc : c ∈ I)
    (p : Spec (.of (HomogeneousLocalization.Away (reesGrading (deformationCenter I))
      (reesX _ (Polynomial.C c) (C_mem_deformationCenter hc)))))
    (hp : chart _ _ (reesX_mem _ _ (C_mem_deformationCenter hc)) p ∉
      (deformationChart I).opensRange) :
    chart _ _ (reesX_mem _ _ (C_mem_deformationCenter hc)) p ∈
      closure (zeroFibreOffCenter I) := by
  have hw : Away.isLocalizationElem (reesX_mem _ _ (C_mem_deformationCenter hc))
      (reesX_mem _ X X_mem_deformationCenter) ∈ p.asIdeal := by
    by_contra h
    apply hp
    have : p ∈ chart _ _ (reesX_mem _ _ (C_mem_deformationCenter hc)) ⁻¹ᵁ
        Proj.basicOpen _ (reesX _ X X_mem_deformationCenter) := by
      rw [chart, Proj.awayι_preimage_basicOpen _ _ one_pos _ one_pos]
      exact h
    rw [opensRange_deformationChart]
    exact this
  have hp' : p ∈ closure (Set.range (PrimeSpectrum.comap (chartToAway hc))) := by
    rw [PrimeSpectrum.closure_range_comap]
    exact fun z hz ↦ (Ideal.span_singleton_le_iff_mem _).mpr hw (ker_chartToAway_le hc hz)
  refine closure_mono ?_ (image_closure_subset_closure_image
    (chart _ _ (reesX_mem _ _ (C_mem_deformationCenter hc))).continuous ⟨p, hp', rfl⟩)
  rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
  have key : toSpec _ (chart _ _ (reesX_mem _ _ (C_mem_deformationCenter hc))
      (PrimeSpectrum.comap (chartToAway hc) r)) =
      zeroFibre R (PrimeSpectrum.comap (algebraMap R (Localization.Away c)) r) := by
    rw [← Scheme.Hom.comp_apply, chart_toSpec, zeroFibre, Spec.map_apply, Spec.map_apply,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, ← PrimeSpectrum.comap_comp_apply,
      ← PrimeSpectrum.comap_comp_apply, chartToAway_comp_awayAlgebraMap]
  change toSpec _ _ ∈ (centerCompl I : Set (Spec (.of R[X]))) ∩ Set.range (zeroFibre R)
  rw [key]
  refine ⟨fun hZ ↦ ?_, _, rfl⟩
  have hC := hZ (C_mem_deformationCenter hc)
  have hC' : algebraMap R (Localization.Away c) c ∈ r.asIdeal := by
    simpa [zeroFibre, Spec.map_apply] using hC
  exact r.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hC' (IsLocalization.Away.algebraMap_isUnit c))

end AwayChart

/-! ### The comparison -/

/-- **The Rees chart is the complement of the strict transform of the zero fibre**: in the
blow-up of `Spec R[t]` along `J = I R[t] + (t)`, the complement of the closure of the locus over
`V(t) ∖ V(J)` is the image of `Spec R[t, I t⁻¹]` (blueprint `definition-deformation-normal-bundle`,
affine-local form). -/
theorem compl_closure_zeroFibreOffCenter :
    (closure (zeroFibreOffCenter I))ᶜ =
      ((deformationChart I).opensRange : Set (AffineBlowup (deformationCenter I))) := by
  ext y
  constructor
  · intro hy
    by_contra hy'
    rcases mem_opensRange_deformationChart_or_exists I y with h | ⟨c, hc, h⟩
    · exact hy' h
    · obtain ⟨p, rfl⟩ := h
      exact hy (chart_mem_closure_zeroFibreOffCenter hc p hy')
  · intro hy hcl
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hcl _ (deformationChart I).opensRange.isOpen hy
    exact Set.disjoint_left.mp (disjoint_opensRange_deformationChart I) hz1 hz2
/-! ### The strict transform -/

section StrictTransform

variable {I}

instance : IsClosedImmersion (zeroFibre R) :=
  IsClosedImmersion.spec_of_surjective _ fun r ↦ ⟨Polynomial.C r, by simp⟩

lemma deformationCenter_fg (hI : I.FG) : (deformationCenter I).FG :=
  Submodule.FG.sup (hI.map _) (Submodule.fg_span_singleton _)

/-- For finitely generated `I`, the open locus of the strict transform of the zero fibre is
quasi-compact over the blow-up, so the strict transform is the closure of that locus. -/
lemma quasiCompact_strictTransformOpen_ι (hI : I.FG) :
    QuasiCompact (strictTransformOpen (zeroFibre R) (toSpec (deformationCenter I))
      (centerCompl I)).ι := by
  have : IsProper (toSpec (deformationCenter I)) := isProper_toSpec _ (deformationCenter_fg hI)
  have : QuasiSeparatedSpace ↥(Limits.pullback (zeroFibre R) (toSpec (deformationCenter I))) :=
    quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd _ _ ≫ toSpec (deformationCenter I))
  exact quasiCompact_strictTransformOpen_ι_of_isCompact _ _ _
    (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨_, deformationCenter_fg hI, rfl⟩).1

/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section,
affine-local form. For a finitely generated ideal `I ⊆ R` (the ideal of the section `s(B) = V(I)` in
`V = Spec R`), the Rees model `Spec R[t, I t⁻¹]` of the deformation to the normal cone is, via
`deformationChart`, the open complement in `Bl_{V(I) × 0} (Spec R[t])` of the strict transform of
the zero fibre `V × {0} = Spec R`. The chart lies over `Spec R[t]`
(`deformationChart_toSpec`), so `g̃` and the section `s̃` (`deformationChart_section`) of the
two models agree. -/
theorem opensRange_deformationChart_eq_compl_strictTransform (hI : I.FG) :
    ((deformationChart I).opensRange : Set (AffineBlowup (deformationCenter I))) =
      (Set.range (strictTransformMap (zeroFibre R) (toSpec (deformationCenter I))
        (centerCompl I)))ᶜ := by
  have := quasiCompact_strictTransformOpen_ι hI
  rw [range_strictTransformMap_eq_closure]
  exact (compl_closure_zeroFibreOffCenter I).symm

/-- The section `s̃ : 𝔸¹_{V(I)} ⟶ Spec R[t, I t⁻¹]` of the Rees model, given by
`R[t, I t⁻¹] ⟶ (R / I)[t]`, `x t⁻¹ ↦ 0`, maps to the blow-up over `V(I) × 𝔸¹ ⊆ Spec R[t]`. -/
lemma deformationChart_section :
    Spec.map (CommRingCat.ofHom (I.extendedReesAlgebraToPolynomial (Ideal.Quotient.mk I)
      Ideal.mk_ker.ge)) ≫ deformationChart I ≫ toSpec (deformationCenter I) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (Ideal.Quotient.mk I))) := by
  rw [deformationChart_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.extendedReesAlgebraToPolynomial_comp_toExtendedReesAlgebra]

variable (I) in
/-- The open complement `Bl_{V(I) × 0} (Spec R[t]) ∖ (strict transform of Spec R × 0)`. -/
noncomputable def strictTransformCompl : (AffineBlowup (deformationCenter I)).Opens :=
  ⟨(Set.range (strictTransformMap (zeroFibre R) (toSpec (deformationCenter I))
      (centerCompl I)))ᶜ,
    (strictTransformMap _ _ _).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section,
affine-local form as an isomorphism of schemes: for finitely generated `I`,
`Spec R[t, I t⁻¹] ≅ Bl_{V(I) × 0} (Spec R[t]) ∖ (strict transform of Spec R × 0)`. -/
noncomputable def extendedReesSpecIsoStrictTransformCompl (hI : I.FG) :
    Spec (.of I.extendedReesAlgebra) ≅ (strictTransformCompl I).toScheme :=
  IsOpenImmersion.isoOfRangeEq (deformationChart I) (strictTransformCompl I).ι (by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
    exact opensRange_deformationChart_eq_compl_strictTransform hI)

@[reassoc (attr := simp)]
lemma extendedReesSpecIsoStrictTransformCompl_hom_ι (hI : I.FG) :
    (extendedReesSpecIsoStrictTransformCompl hI).hom ≫ (strictTransformCompl I).ι =
      deformationChart I :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end StrictTransform

end AlgebraicGeometry.AffineBlowup

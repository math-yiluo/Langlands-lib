import Langlands.AlgebraicGeometry.ProjectiveSpace.RationalPointZeros
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.KrullDimension

/-! # Weight-block rational points of closed sets stable under a diagonal scaling -/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency false

section Algebra

variable {R : Type*} [CommRing R]

/-- **Greedy radical generation.** Let `A` be the set of indices `i` for which `x i` is not in
the radical of `J` together with the earlier elements `x j`, `j < i`. Then every `x i` lies in
the radical of `J` together with the elements indexed by `A`. -/
theorem mem_radical_sup_span_greedy {N : ℕ} (J : Ideal R) (x : Fin N → R) (i : Fin N) :
    x i ∈ (J ⊔ Ideal.span
      (x '' {j | x j ∉ (J ⊔ Ideal.span (x '' Set.Iio j)).radical})).radical := by
  induction i using WellFoundedLT.induction with
  | _ i ih =>
  by_cases hi : x i ∉ (J ⊔ Ideal.span (x '' Set.Iio i)).radical
  · exact Ideal.le_radical (Ideal.mem_sup_right (Ideal.subset_span ⟨i, hi, rfl⟩))
  · have hmem : x i ∈ (J ⊔ Ideal.span (x '' Set.Iio i)).radical := not_not.mp hi
    have hle : J ⊔ Ideal.span (x '' Set.Iio i) ≤
        (J ⊔ Ideal.span
          (x '' {j | x j ∉ (J ⊔ Ideal.span (x '' Set.Iio j)).radical})).radical := by
      refine sup_le (le_sup_left.trans Ideal.le_radical) (Ideal.span_le.mpr ?_)
      rintro _ ⟨j, hj, rfl⟩
      exact ih j hj
    have h := Ideal.radical_mono hle hmem
    rwa [Ideal.radical_idem] at h

/-- Comap of the image of an ideal containing `J` in `R ⧸ J`. -/
theorem comap_map_mk_of_le {J p : Ideal R} (h : J ≤ p) :
    (p.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = p := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr h]

/-- Passing to `R ⧸ J` is strictly monotone on ideals containing `J`. -/
theorem map_mk_lt_map_mk {J p q : Ideal R} (hp : J ≤ p) (hq : J ≤ q) (hpq : p < q) :
    p.map (Ideal.Quotient.mk J) < q.map (Ideal.Quotient.mk J) := by
  refine lt_of_le_of_ne (Ideal.map_mono hpq.le) fun h => hpq.ne ?_
  rw [← comap_map_mk_of_le hp, ← comap_map_mk_of_le hq, h]

/-- **Krull's height theorem modulo `J`.** If a prime `M ⊇ J` lies in the radical of `J` together
with finitely many elements `x i`, `i ∈ A`, of `M`, then the image of `M` in `R ⧸ J` has height at
most the number of these elements. -/
theorem height_map_mk_le_card [IsNoetherianRing R] {J M : Ideal R} [M.IsPrime] (hJM : J ≤ M)
    {ι : Type*} (x : ι → R) (A : Finset ι) (hM : M ≤ (J ⊔ Ideal.span (x '' A)).radical)
    (hxA : ∀ i ∈ A, x i ∈ M) :
    (M.map (Ideal.Quotient.mk J)).height ≤ A.card := by
  classical
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have : (M.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rwa [Ideal.mk_ker])
  set s : Finset (R ⧸ J) := A.image fun i => Ideal.Quotient.mk J (x i) with hs
  have hmin : M.map (Ideal.Quotient.mk J) ∈ (Ideal.span (s : Set (R ⧸ J))).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [Ideal.span_le]
      intro y hy
      rw [hs, Finset.coe_image] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      exact Ideal.mem_map_of_mem _ (hxA i hi)
    · rintro q ⟨hq, hsq⟩ -
      have hcomap : J ⊔ Ideal.span (x '' A) ≤ q.comap (Ideal.Quotient.mk J) := by
        refine sup_le ?_ (Ideal.span_le.mpr ?_)
        · intro r hr
          rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
          exact q.zero_mem
        · rintro _ ⟨i, hi, rfl⟩
          exact hsq (Ideal.subset_span (by
            rw [hs, Finset.coe_image]
            exact ⟨i, hi, rfl⟩))
      have hrad : M ≤ q.comap (Ideal.Quotient.mk J) :=
        hM.trans ((Ideal.radical_mono hcomap).trans (Ideal.IsPrime.radical inferInstance).le)
      calc M.map (Ideal.Quotient.mk J) ≤ (q.comap (Ideal.Quotient.mk J)).map
            (Ideal.Quotient.mk J) := Ideal.map_mono hrad
        _ = q := Ideal.map_comap_of_surjective _ hsurj q
  calc (M.map (Ideal.Quotient.mk J)).height ≤ s.card :=
        Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
    _ ≤ A.card := by exact_mod_cast Finset.card_image_le

end Algebra

variable {K : Type u} [Field K] {n : ℕ}

/-- Every nonzero vector is a system of homogeneous coordinates of some point. -/
theorem exists_hasCoordinates {c : Fin (n + 1) → K} (hc : c ≠ 0) :
    ∃ y : ProjectiveSpace K n, HasCoordinates y c :=
  ⟨_, hasCoordinates_fromOfGlobalSections (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c
    (irrelevant_map_eval_eq_top _ hc)⟩

/-- The homogeneous vanishing ideal of a set of points of projective space, as an ideal of the
homogeneous coordinate ring. -/
abbrev vanishingIdealOf (Z : Set (ProjectiveSpace K n)) : Ideal (ProjectiveCoordinateRing K n) :=
  (ProjectiveSpectrum.vanishingIdeal (𝒜 := projectiveSpaceGrading K n) Z).toIdeal

theorem mem_vanishingIdealOf {Z : Set (ProjectiveSpace K n)} {f : ProjectiveCoordinateRing K n} :
    f ∈ vanishingIdealOf Z ↔ ∀ x ∈ Z, f ∈ x.asHomogeneousIdeal :=
  ProjectiveSpectrum.mem_vanishingIdeal _ f

/-- Homogeneous components of elements of a homogeneous ideal lie in the ideal. -/
theorem homogeneousComponent_mem_vanishingIdealOf {Z : Set (ProjectiveSpace K n)}
    {f : ProjectiveCoordinateRing K n} (hf : f ∈ vanishingIdealOf Z) (d : ℕ) :
    homogeneousComponent d f ∈ vanishingIdealOf Z := by
  rw [mem_vanishingIdealOf] at hf ⊢
  intro x hx
  exact (mem_asHomogeneousIdeal_iff_homogeneousComponent x f).mp (hf x hx) d

/-- Homogeneous coordinates of a point of `Z` annihilate the homogeneous elements of the
vanishing ideal of `Z`. -/
theorem eval_eq_zero_of_mem {Z : Set (ProjectiveSpace K n)} {x : ProjectiveSpace K n}
    (hx : x ∈ Z) {c : Fin (n + 1) → K} (hc : HasCoordinates x c)
    {f : ProjectiveCoordinateRing K n} (hf : f ∈ vanishingIdealOf Z) {d : ℕ}
    (hd : f.IsHomogeneous d) : eval c f = 0 :=
  (hc d f hd).mp (mem_vanishingIdealOf.mp hf x hx)

/-- A point of projective space lies in a closed set `Z` as soon as its homogeneous coordinates
annihilate the homogeneous elements of the vanishing ideal of `Z`. -/
theorem mem_of_eval_eq_zero {Z : Set (ProjectiveSpace K n)} (hZ : IsClosed Z)
    {y : ProjectiveSpace K n} {c : Fin (n + 1) → K} (hy : HasCoordinates y c)
    (hc : ∀ f ∈ vanishingIdealOf Z, ∀ d : ℕ, f.IsHomogeneous d → eval c f = 0) : y ∈ Z := by
  have hZ' : IsClosed (X := ProjectiveSpectrum (projectiveSpaceGrading K n)) Z := hZ
  have hcl : ProjectiveSpectrum.zeroLocus (projectiveSpaceGrading K n)
      (ProjectiveSpectrum.vanishingIdeal (𝒜 := projectiveSpaceGrading K n) Z) = Z :=
    (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure _ _).trans hZ'.closure_eq
  have hy' : y ∈ ProjectiveSpectrum.zeroLocus (projectiveSpaceGrading K n)
      (ProjectiveSpectrum.vanishingIdeal (𝒜 := projectiveSpaceGrading K n) Z) := by
    refine (ProjectiveSpectrum.mem_zeroLocus _ _ _).mpr ?_
    intro f hf
    refine (mem_asHomogeneousIdeal_iff_homogeneousComponent y f).mpr fun d => ?_
    refine (hy d _ (homogeneousComponent_isHomogeneous d f)).mpr ?_
    exact hc _ (homogeneousComponent_mem_vanishingIdealOf hf d) d
      (homogeneousComponent_isHomogeneous d f)
  exact hcl ▸ hy'

/-- The irrelevant ideal of the homogeneous coordinate ring, as an ideal. -/
abbrev irrelevantIdeal (K : Type u) [Field K] (n : ℕ) : Ideal (ProjectiveCoordinateRing K n) :=
  (HomogeneousIdeal.irrelevant (projectiveSpaceGrading K n)).toIdeal

theorem mem_irrelevantIdeal_iff (f : ProjectiveCoordinateRing K n) :
    f ∈ irrelevantIdeal K n ↔ constantCoeff f = 0 := by
  change f ∈ HomogeneousIdeal.irrelevant (projectiveSpaceGrading K n) ↔ _
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    decompose_coe_eq_homogeneousComponent, homogeneousComponent_zero, C_eq_zero,
    constantCoeff_eq]

theorem X_mem_irrelevantIdeal (i : Fin (n + 1)) : (X i : ProjectiveCoordinateRing K n) ∈
    irrelevantIdeal K n := by
  rw [mem_irrelevantIdeal_iff, constantCoeff_X]

instance irrelevantIdeal_isMaximal : (irrelevantIdeal K n).IsMaximal := by
  have h : irrelevantIdeal K n = RingHom.ker (constantCoeff (σ := Fin (n + 1)) (R := K)) := by
    ext f
    rw [mem_irrelevantIdeal_iff, RingHom.mem_ker]
  rw [h]
  exact RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, constantCoeff_C _ a⟩

/-- The homogeneous prime of every point of projective space lies strictly inside the
irrelevant ideal. -/
theorem asHomogeneousIdeal_lt_irrelevantIdeal (x : ProjectiveSpace K n) :
    x.asHomogeneousIdeal.toIdeal < irrelevantIdeal K n := by
  refine lt_of_le_of_ne (fun f hf => ?_) fun h => x.not_irrelevant_le fun f hf => ?_
  · rw [mem_irrelevantIdeal_iff]
    have h0 := (mem_asHomogeneousIdeal_iff_homogeneousComponent x f).mp hf 0
    rw [homogeneousComponent_zero] at h0
    by_contra hne
    rw [constantCoeff_eq] at hne
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((IsUnit.mk0 _ hne).map C))
  · have hf' : f ∈ irrelevantIdeal K n := hf
    rw [← h] at hf'
    exact hf'

/-- **Chains of irreducible closed sets give height.** If a closed set `Z` of projective space has
topological Krull dimension at least `d`, then its vanishing ideal `J` lies in the irrelevant ideal
`M`, and the image of `M` in the homogeneous coordinate ring of `Z` has height at least `d + 1`. -/
theorem le_height_map_irrelevantIdeal {Z : Set (ProjectiveSpace K n)} (hZ : IsClosed Z) {d : ℕ}
    (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim Z) :
    vanishingIdealOf Z ≤ irrelevantIdeal K n ∧
      ((d + 1 : ℕ) : ℕ∞) ≤
        ((irrelevantIdeal K n).map (Ideal.Quotient.mk (vanishingIdealOf Z))).height := by
  classical
  set J := vanishingIdealOf Z with hJdef
  set M := irrelevantIdeal K n with hMdef
  unfold topologicalKrullDim at hd
  obtain ⟨s, hs⟩ := Order.le_krullDim_iff.mp hd
  have hirr : ∀ t : TopologicalSpace.IrreducibleCloseds Z,
      IsIrreducible (Subtype.val '' (t : Set Z)) :=
    fun t => t.isIrreducible.image _ continuous_subtype_val.continuousOn
  have hcl : ∀ t : TopologicalSpace.IrreducibleCloseds Z,
      IsClosed (Subtype.val '' (t : Set Z)) :=
    fun t => hZ.isClosedMap_subtype_val _ t.isClosed
  set g : TopologicalSpace.IrreducibleCloseds Z → ProjectiveSpace K n :=
    fun t => (hirr t).genericPoint with hgdef
  have hg : ∀ t, closure {g t} = Subtype.val '' (t : Set Z) := fun t => by
    have h := (hirr t).isGenericPoint_genericPoint_closure
    rw [(hcl t).closure_eq] at h
    exact h
  have hgZ : ∀ t, g t ∈ Z := fun t => by
    have h : g t ∈ closure {g t} := subset_closure rfl
    rw [hg t] at h
    obtain ⟨z, -, hz⟩ := h
    rw [← hz]
    exact z.2
  have hJg : ∀ t, J ≤ (g t).asHomogeneousIdeal.toIdeal := fun t f hf =>
    mem_vanishingIdealOf.mp hf (g t) (hgZ t)
  have hglt : ∀ t t' : TopologicalSpace.IrreducibleCloseds Z, t < t' →
      (g t').asHomogeneousIdeal.toIdeal < (g t).asHomogeneousIdeal.toIdeal := by
    intro t t' htt'
    have hsub : Subtype.val '' (t : Set Z) ⊆ Subtype.val '' (t' : Set Z) :=
      Set.image_mono htt'.le
    have hmem : g t ∈ closure {g t'} := by
      rw [hg t']
      apply hsub
      rw [← hg t]
      exact subset_closure rfl
    have hle : (g t').asHomogeneousIdeal.toIdeal ≤ (g t).asHomogeneousIdeal.toIdeal :=
      (ProjectiveSpectrum.le_iff_mem_closure (𝒜 := projectiveSpaceGrading K n) (g t') (g t)).mpr
        hmem
    refine lt_of_le_of_ne hle fun heq => htt'.ne' ?_
    have hgeq : g t' = g t := by
      have h1 : (g t').asHomogeneousIdeal = (g t).asHomogeneousIdeal :=
        HomogeneousIdeal.toIdeal_injective heq
      exact ProjectiveSpectrum.ext h1
    apply TopologicalSpace.IrreducibleCloseds.ext
    apply Set.image_injective.mpr Subtype.val_injective
    rw [← hg t, ← hg t', hgeq]
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have hJM : J ≤ M := (hJg s.head).trans (asHomogeneousIdeal_lt_irrelevantIdeal _).le
  refine ⟨hJM, ?_⟩
  have hMprime : (M.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rwa [Ideal.mk_ker])
  let Q : TopologicalSpace.IrreducibleCloseds Z → PrimeSpectrum (ProjectiveCoordinateRing K n ⧸ J) :=
    fun t => haveI := (g t).isPrime
      ⟨(g t).asHomogeneousIdeal.toIdeal.map (Ideal.Quotient.mk J),
        Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hJg t)⟩
  have hQ : ∀ t t', t < t' → Q t' < Q t := fun t t' h =>
    (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp (map_mk_lt_map_mk (hJg t') (hJg t) (hglt t t' h))
  let p : LTSeries (PrimeSpectrum (ProjectiveCoordinateRing K n ⧸ J)) :=
    s.reverse.map ⟨Q, fun {a b} h => hQ b a h⟩
  have hplast : p.last = Q s.head := by
    simp only [p, RelSeries.last_map, RelSeries.last_reverse]
    rfl
  have hlt : p.last < ⟨M.map (Ideal.Quotient.mk J), hMprime⟩ := by
    rw [hplast]
    exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp
      (map_mk_lt_map_mk (hJg _) hJM (asHomogeneousIdeal_lt_irrelevantIdeal _))
  have hlen := Order.length_le_height_last (p := p.snoc _ hlt)
  rw [RelSeries.last_snoc, RelSeries.snoc_length] at hlen
  calc ((d + 1 : ℕ) : ℕ∞) = ((p.length + 1 : ℕ) : ℕ∞) := by simp [p, hs]
    _ ≤ _ := hlen
    _ = _ := (PrimeSpectrum.height_eq_orderHeight _).symm

/-- **Weight-block points.** Let `k` be algebraically closed, let `Z` be a closed subset of
projective `n`-space over `k` stable under the scaling `zᵐ = (z ^ m i)ᵢ` of homogeneous
coordinates for every unit `z`, and let `d` be at most the topological Krull dimension of `Z`.
Then `Z` contains `d + 1` pairwise non-proportional rational points, each having homogeneous
coordinates supported on a single weight block `{i | m i = w}`. -/
theorem exists_weightBlock_points [IsAlgClosed K] (Z : Set (ProjectiveSpace K n))
    (hZ : IsClosed Z) (m : Fin (n + 1) → ℤ)
    (hstable : ∀ (z : Kˣ) (x : ProjectiveSpace K n) (c : Fin (n + 1) → K), x ∈ Z →
      HasCoordinates x c → ∀ y, HasCoordinates y (fun i => ((z ^ m i : Kˣ) : K) * c i) → y ∈ Z)
    (d : ℕ) (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim Z) :
    ∃ c : Fin (d + 1) → (Fin (n + 1) → K),
      (∀ j, c j ≠ 0) ∧ (∀ j y, HasCoordinates y (c j) → y ∈ Z) ∧
      (∀ j i l, c j i ≠ 0 → c j l ≠ 0 → m i = m l) ∧
      (∀ j j', j ≠ j' → ∀ a : K, c j' ≠ a • c j) := by
  classical
  set J := vanishingIdealOf Z with hJdef
  set σ := Tuple.sort m with hσdef
  have hmono : Monotone (m ∘ σ) := Tuple.monotone_sort m
  set x : Fin (n + 1) → ProjectiveCoordinateRing K n := fun i => X (σ i) with hxdef
  set A : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun i => x i ∉ (J ⊔ Ideal.span (x '' Set.Iio i)).radical with hAdef
  have hAset : (A : Set (Fin (n + 1))) =
      {i | x i ∉ (J ⊔ Ideal.span (x '' Set.Iio i)).radical} := by
    ext i
    simp [hAdef]
  obtain ⟨hJM, hheight⟩ := le_height_map_irrelevantIdeal hZ hd
  -- The irrelevant ideal is in the radical of `J` and the greedy coordinates.
  have hrad : irrelevantIdeal K n ≤ (J ⊔ Ideal.span (x '' (A : Set (Fin (n + 1))))).radical := by
    intro f hf
    have hspan : f ∈ Ideal.span ((X : Fin (n + 1) → ProjectiveCoordinateRing K n) '' Set.univ) := by
      rw [mem_ideal_span_X_image]
      intro e he
      rw [mem_irrelevantIdeal_iff, constantCoeff_eq] at hf
      have he0 : e ≠ 0 := by
        rintro rfl
        exact (mem_support_iff.mp he) hf
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he0
      exact ⟨i, Set.mem_univ _, hi⟩
    refine (Ideal.span_le.mpr ?_) hspan
    rintro _ ⟨l, -, rfl⟩
    have h := mem_radical_sup_span_greedy J x (σ.symm l)
    rw [← hAset] at h
    simpa [hxdef] using h
  have hcard : d + 1 ≤ A.card := by
    have h1 := height_map_mk_le_card hJM x A hrad fun i _ => X_mem_irrelevantIdeal (σ i)
    exact_mod_cast hheight.trans h1
  -- Nullstellensatz: points vanishing on the earlier coordinates but not on the current one.
  have hnull : ∀ i ∈ A, ∃ v : Fin (n + 1) → K, (∀ f ∈ J, eval v f = 0) ∧
      (∀ j < i, v (σ j) = 0) ∧ v (σ i) ≠ 0 := by
    intro i hi
    have hi' : x i ∉ (J ⊔ Ideal.span (x '' Set.Iio i)).radical := (Finset.mem_filter.mp hi).2
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K)] at hi'
    simp only [MvPolynomial.mem_vanishingIdeal_iff, not_forall] at hi'
    obtain ⟨v, hv, hvi⟩ := hi'
    rw [MvPolynomial.mem_zeroLocus_iff] at hv
    refine ⟨v, fun f hf => ?_, fun j hj => ?_, ?_⟩
    · simpa [coe_aeval_eq_eval] using hv f (Ideal.mem_sup_left hf)
    · simpa [hxdef, coe_aeval_eq_eval] using
        hv (x j) (Ideal.mem_sup_right (Ideal.subset_span ⟨j, hj, rfl⟩))
    · simpa [hxdef, coe_aeval_eq_eval] using hvi
  -- Choose `d + 1` greedy indices.
  let e : Fin (d + 1) → Fin (n + 1) := fun j => A.orderEmbOfFin rfl (Fin.castLE hcard j)
  have heA : ∀ j, e j ∈ A := fun j => A.orderEmbOfFin_mem rfl _
  have he : Function.Injective e :=
    (A.orderEmbOfFin rfl).injective.comp (Fin.castLE_injective hcard)
  choose v hvJ hv0 hvne using fun j => hnull (e j) (heA j)
  set c : Fin (d + 1) → Fin (n + 1) → K :=
    fun j => GroupScheme.FlagCore.weightPart m (v j) (m (σ (e j))) with hcdef
  have hcapply : ∀ j l, c j l = if m l = m (σ (e j)) then v j l else 0 := fun j l => rfl
  have hcself : ∀ j, c j (σ (e j)) ≠ 0 := fun j => by
    rw [hcapply]
    split_ifs with h
    · exact hvne j
    · exact absurd rfl h
  have hcne : ∀ j, c j ≠ 0 := fun j h => hcself j (by rw [h]; rfl)
  have hcearly : ∀ j i, i < e j → c j (σ i) = 0 := fun j i hi => by
    rw [hcapply]
    split_ifs
    · exact hv0 j i hi
    · rfl
  refine ⟨c, hcne, ?_, ?_, ?_⟩
  · -- the weight-block limit points lie in `Z`
    intro j y hy
    have hvj : v j ≠ 0 := fun h => hvne j (by rw [h]; rfl)
    obtain ⟨y0, hy0⟩ := exists_hasCoordinates hvj
    have hy0Z : y0 ∈ Z := mem_of_eval_eq_zero hZ hy0 fun f hf _ _ => hvJ j f hf
    refine mem_of_eval_eq_zero hZ hy fun f hf d' hd' => ?_
    refine GroupScheme.FlagCore.eval_weightPart_eq_zero hd' m (v j) (m (σ (e j))) ?_ ?_
    · intro l hl
      have hle : e j ≤ σ.symm l := by
        by_contra hlt
        push Not at hlt
        apply hl
        have h := hv0 j (σ.symm l) hlt
        rwa [Equiv.apply_symm_apply] at h
      have h := hmono hle
      simpa using h
    · intro z hz
      set w : Fin (n + 1) → K := fun i => (((Units.mk0 z hz) ^ m i : Kˣ) : K) * v j i with hw
      have hw' : w = fun i => z ^ m i * v j i := by
        funext i
        simp [hw, Units.val_zpow_eq_zpow_val]
      have hwne : w ≠ 0 := by
        intro h
        apply hvne j
        have h1 := congrFun h (σ (e j))
        simp only [hw, Pi.zero_apply, mul_eq_zero, Units.ne_zero, false_or] at h1
        exact h1
      obtain ⟨y1, hy1⟩ := exists_hasCoordinates hwne
      have hy1Z : y1 ∈ Z := hstable (Units.mk0 z hz) y0 (v j) hy0Z hy0 y1 hy1
      rw [← hw']
      exact eval_eq_zero_of_mem hy1Z hy1 hf hd'
  · intro j i l hi hl
    rw [hcapply] at hi hl
    split_ifs at hi hl with h1 h2
    · rw [h1, h2]
    all_goals exact absurd rfl ‹_›
  · intro j j' hjj' a ha
    rcases lt_or_gt_of_ne (he.ne hjj') with hlt | hlt
    · -- the earlier index `e j` is a zero coordinate of `c j'`
      have h1 := congrFun ha (σ (e j))
      rw [hcearly j' (e j) hlt, Pi.smul_apply, smul_eq_mul] at h1
      have ha0 : a = 0 := by
        rcases mul_eq_zero.mp h1.symm with h | h
        · exact h
        · exact absurd h (hcself j)
      apply hcne j'
      rw [ha, ha0, zero_smul]
    · have h1 := congrFun ha (σ (e j'))
      rw [Pi.smul_apply, smul_eq_mul, hcearly j (e j') hlt, mul_zero] at h1
      exact hcself j' h1

end Langlands.AlgebraicGeometry.ProjectiveSpace

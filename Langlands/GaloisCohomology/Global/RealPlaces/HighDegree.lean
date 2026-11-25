import Langlands.GaloisCohomology.Global.Finiteness
import Langlands.GaloisCohomology.Global.RealPlaces.LocalDuality
import Langlands.Global.Arithmetic.CMSubfield
import Langlands.Cohomology.Profinite.EulerCharacteristic

/-!
# The degrees above two and the real places

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K`, `G_S` the Galois
group of the maximal extension `K_S ⊆ Ω` unramified outside `S` and `ι : PlaceEmbeddings K Ω`. For a
finite smooth `G_S`-module `M` killed by `n ≠ 0` with the places above `n` in `S`:

* `bijective_realLocalization_of_odd_or_isTotallyComplex`: if `n` is odd or `K` is totally complex,
  `Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M)` is bijective for `r ≥ 3` (both sides vanish).
* `RealLocalizationDegreeThreeStatement`: the localization to the real places is bijective in degree
  `3` (Tate; NSW (8.6.10) (ii), Milne I.4.10 (c)). This file does not prove it; it is
  `realLocalizationDegreeThreeStatement` of `Langlands.GaloisCohomology.Global.RealPlaces.DegreeThreeProof`,
  from Poitou–Tate duality and the vanishing of the cohomology with compact support in degrees `≥ 4`.
* `bijective_realLocalization_of_degreeThree`: from `RealLocalizationDegreeThreeStatement`,
  bijectivity in every degree `r ≥ 3`, by the dimension shift `0 → M → Ind_U^{G_S} M → B → 0` with
  `U = G_S(K(i))`, which has `ℓ`-cohomological dimension `≤ 2` for the primes `ℓ` under `S` (`K(i)` is
  totally complex); the induced module is acyclic in degrees `≥ 3` and at the real places. The forms
  without the hypothesis are `bijective_realLocalization` and `bijective_realLocalization_of_nsmul` of
  `Langlands.GaloisCohomology.Global.RealPlaces.DegreeThreeProof`.
* `finite_cohomology`: `Hʳ(G_S, M)` is finite for every `r` (`S` finite), with no hypothesis: in
  degrees `≥ 3` it is a quotient of `H^{r-1}(G_S, B)`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory CategoryTheory.Limits Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain

universe u

noncomputable section

section Statement

/-- **The real places in degree three.** For every number field `K`, separable closure `Ω`, finite
set `S` of finite places, place embeddings `ι` and finite smooth `G_S`-module `M` killed by `n ≠ 0` such
that every finite place above `n` lies in `S`, the localization
`H³(G_S, M) → ∏_{w real} H³(K_w, M)` is bijective. -/
def RealLocalizationDegreeThreeStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ι : PlaceEmbeddings K Ω)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (n : ℕ), n ≠ 0 → (∀ m : M, n • m = 0) →
    (∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    Function.Bijective fun (x : cohomology M 3) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 3 x

end Statement

section Odd

variable {K : Type u} [Field K] [NumberField K]

/-- The Galois group of the closure of the completion at a real place has two elements. -/
theorem card_closureGalois (w : InfinitePlace K) (hw : w.IsReal) :
    Nat.card Gal(AlgebraicClosure w.Completion/w.Completion) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, closureConj w hw, (closureConj_ne_one w hw).symm, ?_⟩
  ext σ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact eq_one_or_eq_closureConj w hw σ

/-- In positive degree the cohomology of the Galois group of a real place is killed by `2`. -/
theorem two_nsmul_cohomology_closureGalois (w : InfinitePlace K) (hw : w.IsReal)
    (A : Rep.{u} (ULift.{u} ℤ) Gal(AlgebraicClosure w.Completion/w.Completion)) [IsSmoothRep A]
    {r : ℕ} (hr : r ≠ 0) (x : cohomology A r) : 2 • x = 0 := by
  obtain ⟨U, hU⟩ := exists_card_smul_eq_zero A hr x
  have hd : Nat.card (Gal(AlgebraicClosure w.Completion/w.Completion) ⧸ U.toSubgroup) ∣ 2 :=
    card_closureGalois w hw ▸ Subgroup.card_quotient_dvd_card _
  obtain ⟨c, hc⟩ := hd
  rw [hc, mul_comm, ← smul_smul, hU, smul_zero]

/-- For an odd `n`, the positive-degree cohomology of the Galois group of a real place with
coefficients killed by `n` vanishes. -/
theorem eq_zero_cohomology_closureGalois_of_odd (w : InfinitePlace K) (hw : w.IsReal)
    (A : Rep.{u} (ULift.{u} ℤ) Gal(AlgebraicClosure w.Completion/w.Completion)) [IsSmoothRep A]
    {n : ℕ} (hn : Odd n) (hA : ∀ a : A, n • a = 0) {r : ℕ} (hr : r ≠ 0) (x : cohomology A r) :
    x = 0 := by
  have h1 : n • x = 0 := nsmul_cohomology_eq_zero A hA r x
  have h2 := two_nsmul_cohomology_closureGalois w hw A hr x
  have hc : Nat.gcd n 2 = 1 := Nat.Coprime.symm ((Nat.coprime_two_left).2 hn)
  have h : addOrderOf x ∣ 1 := by
    rw [← hc]
    exact Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero h1) (addOrderOf_dvd_of_nsmul_eq_zero h2)
  have h0 := addOrderOf_nsmul_eq_zero x
  rwa [Nat.dvd_one.1 h, one_nsmul] at h0

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)

/-- **The real places above degree two, `n` odd or `K` totally complex.** Both sides vanish. -/
theorem bijective_realLocalization_of_odd_or_isTotallyComplex
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
    {n : ℕ} (hn : n ≠ 0) (hM : ∀ m : M, n • m = 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K) {r : ℕ} (hr : 3 ≤ r) :
    Function.Bijective fun (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 r x := by
  have hglob : Subsingleton (cohomology M r) :=
    cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le S hn hS hK M hM hr
  have hloc : ∀ (w : {w : InfinitePlace K // w.IsReal}) (y : cohomology (realLocalModule ι M w.1) r),
      y = 0 := by
    intro w y
    rcases hK with ho | hc
    · exact eq_zero_cohomology_closureGalois_of_odd w.1 w.2 _ ho (fun a => hM a) (by omega) y
    · exact absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.2 (hc.isComplex w.1))
  refine ⟨fun x y _ => Subsingleton.elim x y, fun t => ⟨0, funext fun w => ?_⟩⟩
  show realLocalization ι M w.1 r 0 = t w
  rw [map_zero, hloc w (t w)]

end Odd

section Imaginary

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **Open subgroups with a totally complex fixed field have cohomological dimension `≤ 2`.** Let
`L ⊆ K_S` be a totally complex finite extension of `K`, `U = G_S(L)` its fixing subgroup and `X` a
smooth `U`-module killed by `n ≠ 0` with the places above `n` in `S`. Then `Hʳ(U, X) = 0` for
`r ≥ 3`. -/
theorem subsingleton_cohomology_fixingOpenSubgroup_of_isTotallyComplex
    (L : IntermediateField K Ω) [NumberField L]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) (hLc : IsTotallyComplex L)
    {n : ℕ} (hn : n ≠ 0) (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (X : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S))) [IsSmoothRep X]
    (hX : ∀ x : X, n • x = 0) {r : ℕ} (hr : 3 ≤ r) : Subsingleton (cohomology X r) := by
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L), ((n : ℕ) : 𝓞 L) ∈ w.asIdeal →
      w ∈ finitePlacesAbove L S := fun w hw => by
    rw [mem_finitePlacesAbove_iff_under]
    refine hS _ ?_
    change algebraMap (𝓞 K) (𝓞 L) ((n : ℕ) : 𝓞 K) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  let e := GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL
  let φ : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S) →ₜ*
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) :=
    ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩
  let X' := Rep.res (φ : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S) →*
    (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S))) X
  have hv := cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le
    (K := L) (Ω := Ω) (finitePlacesAbove L S) hn hSL (Or.inr hLc) X' (fun x => hX x) hr
  have hiso := isIso_map_of_mulEquiv e.symm.toMulEquiv e.symm.continuous e.continuous (𝟙 X')
    Function.bijective_id r
  have hinj : Function.Injective (map φ (𝟙 X') r).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact hinj.subsingleton

/-- If `S` contains the places above `2`, the field `K(i)` lies in `K_S`. -/
theorem exists_sqrt_neg_one_mem (h2 : ∀ v : HeightOneSpectrum (𝓞 K), ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∃ i : Ω, i ^ 2 = -1 ∧ i ∈ maximalUnramifiedOutside K Ω S := by
  obtain ⟨i, hi⟩ : ∃ i : Ω, i ^ 2 = -1 := exists_sq_eq_neg_one (K := K)
  refine ⟨i, hi, mem_maximalUnramifiedOutside_of_pow_eq_one S (n := 4) (by norm_num)
    (fun v hv h => hv (h2 v ?_)) ?_⟩
  · have h4 : ((4 : ℕ) : 𝓞 K) = ((2 : ℕ) : 𝓞 K) * ((2 : ℕ) : 𝓞 K) := by push_cast; ring
    rw [h4] at h
    exact (v.isPrime.mem_or_mem h).elim id id
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hi]
    norm_num

/-- The field `K(i)` inside `K_S` (when `S` contains the places above `2`): a totally complex finite
extension of `K` contained in `K_S`. -/
theorem exists_isTotallyComplex_intermediateField
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∃ (i : Ω) (L : IntermediateField K Ω) (_ : NumberField L)
      (_ : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S),
      IsTotallyComplex L ∧ i ^ 2 = -1 ∧ i ∈ maximalUnramifiedOutside K Ω S ∧
        L = IntermediateField.adjoin K {i} := by
  obtain ⟨i, hi, hiS⟩ := exists_sqrt_neg_one_mem (Ω := Ω) S h2
  let L : IntermediateField K Ω := IntermediateField.adjoin K {i}
  have : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral i)
  have : NumberField L := NumberField.of_module_finite K L
  have hle : L ≤ maximalUnramifiedOutside K Ω S := IntermediateField.adjoin_simple_le_iff.2 hiS
  have hiL : i ∈ L := IntermediateField.mem_adjoin_simple_self K i
  refine ⟨i, L, inferInstance, fun x => hle x.2, ?_, hi, hiS, rfl⟩
  refine Langlands.Global.CMRealization.isTotallyComplex_of_sq_neg (a := -1) (x := ⟨i, hiL⟩)
    (by norm_num) ?_
  rw [map_neg, map_one]
  exact Subtype.ext hi

end Imaginary

section Shift

attribute [-instance] ULift.module

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K)))

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
/-- The unit `A → Ind_U^G A` is injective. -/
theorem coindUnit_injective (U : Subgroup G) (A : Rep.{u} (ULift.{u} ℤ) G) :
    Function.Injective (coindUnit U A).hom := fun a b h => by
  have e := congrArg (fun f : Rep.coind U.subtype (Rep.res U.subtype A) => f.1 1) h
  have e1 := coindUnit_hom_apply U A a 1
  have e2 := coindUnit_hom_apply U A b 1
  rw [map_one, Module.End.one_apply] at e1 e2
  exact e1.symm.trans (e.trans e2)

/-- The short exact sequence `0 → A → Ind_U^G A → B → 0`. -/
abbrev coindUnitSequence (U : Subgroup G) (A : Rep.{u} (ULift.{u} ℤ) G) :
    ShortComplex (Rep.{u} (ULift.{u} ℤ) G) :=
  cokerShortComplex (coindUnit U A)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
theorem coindUnitSequence_shortExact (U : Subgroup G) (A : Rep.{u} (ULift.{u} ℤ) G) :
    (coindUnitSequence U A).ShortExact :=
  cokerShortComplex_shortExact (coindUnit U A) (coindUnit_injective U A)

variable (U : OpenSubgroup G) (A : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep A]

instance isSmoothRep_coindUnitSequence_X₁ :
    IsSmoothRep (coindUnitSequence (U : Subgroup G) A).X₁ :=
  inferInstanceAs (IsSmoothRep A)

instance isSmoothRep_coindUnitSequence_X₂ :
    IsSmoothRep (coindUnitSequence (U : Subgroup G) A).X₂ :=
  inferInstanceAs (IsSmoothRep (Rep.coind (U : Subgroup G).subtype
    (Rep.res (U : Subgroup G).subtype A)))

instance isSmoothRep_coindUnitSequence_X₃ :
    IsSmoothRep (coindUnitSequence (U : Subgroup G) A).X₃ :=
  isSmoothRep_quotient _ _ _

omit [IsSmoothRep A] in
theorem finite_coindUnitSequence_X₃ [Finite A] : Finite (coindUnitSequence (U : Subgroup G) A).X₃ := by
  have : Finite (Rep.res (U : Subgroup G).subtype A) := inferInstanceAs (Finite A)
  have : Finite (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) :=
    finite_coind U _
  exact Finite.of_surjective _ (Submodule.mkQ_surjective _)

omit [IsTopologicalGroup G] [CompactSpace G] [IsSmoothRep A] in
theorem nsmul_coindUnitSequence_X₃ {n : ℕ} (hA : ∀ a : A, n • a = 0)
    (b : (coindUnitSequence (U : Subgroup G) A).X₃) : n • b = 0 := by
  obtain ⟨f, rfl⟩ : ∃ f, (coindUnitSequence (U : Subgroup G) A).g.hom f = b :=
    Submodule.mkQ_surjective _ b
  rw [← map_nsmul]
  have hf : n • f = 0 := Subtype.ext (funext fun x => hA _)
  rw [hf, map_zero]

/-- **Dimension shift.** If `Hʳ⁺¹(U, A) = 0`, every class of `Hʳ⁺¹(G, A)` is the connecting image of
a class of `Hʳ(G, B)`, `B = Ind_U^G A / A`. -/
theorem surjective_δ_coindUnitSequence (r : ℕ)
    (h : Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype A) (r + 1))) :
    Function.Surjective (δ (coindUnitSequence_shortExact (U : Subgroup G) A) r (r + 1) rfl).hom := by
  intro y
  have hI : Subsingleton (cohomology (coindUnitSequence (U : Subgroup G) A).X₂ (r + 1)) :=
    (shapiroIso U (Rep.res (U : Subgroup G).subtype A) (r + 1)).toLinearEquiv.toEquiv.subsingleton
  exact (ShortComplex.moduleCat_exact_iff _).1
    (cohomology_exact₁ (coindUnitSequence_shortExact (U : Subgroup G) A) r (r + 1) rfl) y
    (Subsingleton.elim _ _)

/-- **Dimension shift, injectivity.** If `Hʳ(U, A) = 0` with `r ≥ 1`, the connecting map
`Hʳ(G, B) → Hʳ⁺¹(G, A)` is injective. -/
theorem injective_δ_coindUnitSequence (r : ℕ)
    (h : Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype A) r)) :
    Function.Injective (δ (coindUnitSequence_shortExact (U : Subgroup G) A) r (r + 1) rfl).hom := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have hI : Subsingleton (cohomology (coindUnitSequence (U : Subgroup G) A).X₂ r) :=
    (shapiroIso U (Rep.res (U : Subgroup G).subtype A) r).toLinearEquiv.toEquiv.subsingleton
  obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (cohomology_exact₃ (coindUnitSequence_shortExact (U : Subgroup G) A) r (r + 1) rfl) x hx
  rw [Subsingleton.elim y 0, map_zero]
  exact Submodule.zero_mem _

end Shift

section Finiteness

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}

omit [NumberField K] in
/-- Places above `2` lie under `S` when `n` is even and the places above `n` lie under `S`. -/
theorem two_mem_of_even {n : ℕ} (hn : Even n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∀ v : HeightOneSpectrum (𝓞 K), ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := fun v hv => by
  obtain ⟨c, hc⟩ := even_iff_two_dvd.1 hn
  refine hS v ?_
  rw [hc, Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

/-- Finiteness in degrees `≤ 2` for modules killed by `n`. -/
theorem finite_cohomology_of_le_two_of_nsmul [Finite S] {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) (r : ℕ) (hr : r ≤ 2) : Finite (cohomology M r) := by
  have : Finite (Rep.res ((⊤ : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M) := inferInstanceAs (Finite M)
  have := finite_cohomology_res_of_le_two hn hS ⊤
    (Rep.res ((⊤ : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M) hM r hr
  exact Finite.of_injective _ (bijective_res_top M r).1

/-- **Finiteness in all degrees** for finite modules killed by `n`, with the places above `n` in a
finite `S`. -/
theorem finite_cohomology_of_nsmul [Finite S] {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) (r : ℕ) :
    ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M],
      (∀ m : M, n • m = 0) → Finite (cohomology M r) := by
  induction r with
  | zero => exact fun M _ _ hM => finite_cohomology_of_le_two_of_nsmul hn hS M hM 0 (by norm_num)
  | succ r ih =>
    intro M _ _ hM
    rcases le_or_gt (r + 1) 2 with hr | hr
    · exact finite_cohomology_of_le_two_of_nsmul hn hS M hM (r + 1) hr
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨i, L, _, hL, hLc, -, -, -⟩ :=
        exists_isTotallyComplex_intermediateField (Ω := Ω) S (two_mem_of_even he hS)
      let U := GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL
      have hU : Subsingleton (cohomology (Rep.res (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
          M) (r + 1)) :=
        subsingleton_cohomology_fixingOpenSubgroup_of_isTotallyComplex S L hL hLc hn hS _
          (fun m => hM m) (by omega)
      have := finite_coindUnitSequence_X₃ U M
      have hB := ih (coindUnitSequence (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) M).X₃
        (nsmul_coindUnitSequence_X₃ U M hM)
      exact Finite.of_surjective _ (surjective_δ_coindUnitSequence U M r hU)
    · have := cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le S hn hS (Or.inl ho)
        M hM (show 3 ≤ r + 1 by omega)
      exact Finite.of_subsingleton

variable (S) in
/-- **Finiteness of `Hʳ(G_S, M)` in all degrees.** For a finite set `S` of finite places and a finite
smooth `G_S`-module `M` such that every finite place above `#M` lies in `S`, `Hʳ(G_S, M)` is finite
for every `r`. -/
theorem finite_cohomology [Finite S]
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) (r : ℕ) :
    Finite (cohomology M r) :=
  finite_cohomology_of_nsmul Nat.card_pos.ne' hS r M fun _ => card_nsmul_eq_zero'

end Finiteness

section Conjugation

open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)
  {i : Ω} (hi : i ^ 2 = -1) (hiS : i ∈ maximalUnramifiedOutside K Ω S)

omit [NumberField K] [IsSepClosure K Ω] in
include hi in
/-- Every element of `G_S` sends `i` to `±i`. -/
theorem apply_sqrt_neg_one (g : GaloisGroupUnramifiedOutside K Ω S) :
    g ⟨i, hiS⟩ = ⟨i, hiS⟩ ∨ g ⟨i, hiS⟩ = -⟨i, hiS⟩ := by
  have hj : (⟨i, hiS⟩ : maximalUnramifiedOutside K Ω S) ^ 2 = -1 := Subtype.ext hi
  have hg : (g ⟨i, hiS⟩) ^ 2 = -1 := by rw [← map_pow, hj, map_neg, map_one]
  have h0 : (g ⟨i, hiS⟩ - ⟨i, hiS⟩) * (g ⟨i, hiS⟩ + ⟨i, hiS⟩) = 0 := by
    linear_combination hg - hj
  rcases mul_eq_zero.1 h0 with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (add_eq_zero_iff_eq_neg.1 h)

/-- An element of `G_S` fixing `i` fixes `K(i)`. -/
theorem mem_fixingOpenSubgroup_of_apply_eq {L : IntermediateField K Ω} [NumberField L]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    (hLi : L = IntermediateField.adjoin K {i}) (g : GaloisGroupUnramifiedOutside K Ω S)
    (hg : g ⟨i, hiS⟩ = ⟨i, hiS⟩) : g ∈ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL := by
  subst hLi
  rw [GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff]
  intro x
  set j : maximalUnramifiedOutside K Ω S := ⟨i, hiS⟩ with hj
  have hstab : g ∈ MulAction.stabilizer (GaloisGroupUnramifiedOutside K Ω S) j := hg
  have hjF : j ∈ IntermediateField.fixedField
      (MulAction.stabilizer (GaloisGroupUnramifiedOutside K Ω S) j) := fun τ => τ.2
  have hadj := IntermediateField.adjoin_simple_le_iff.2 hjF
  have hx : embeddingMaximalUnramifiedOutside hL x ∈ IntermediateField.adjoin K {j} := by
    have hmap := IntermediateField.adjoin_map K {j} (maximalUnramifiedOutside K Ω S).val
    have hxmem : (x : Ω) ∈ (IntermediateField.adjoin K {j}).map (maximalUnramifiedOutside K Ω S).val := by
      rw [hmap, Set.image_singleton]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hxmem
    have hye : y = embeddingMaximalUnramifiedOutside hL x := Subtype.ext hyx
    exact hye ▸ hy
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hadj hx) g hstab

variable (w : InfinitePlace K) (hw : w.IsReal)

include hi in
/-- The complex conjugation of a real place sends `i` to `-i`. -/
theorem realLocalizationHom_closureConj_apply :
    realLocalizationHom ι S w (closureConj w hw) ⟨i, hiS⟩ = -⟨i, hiS⟩ := by
  apply Subtype.ext
  refine (ι.infinite w).injective ((realLocalizationHom_apply ι S w (closureConj w hw) ⟨i, hiS⟩).trans ?_)
  change closureConj w hw (ι.infinite w i) = ι.infinite w (-i)
  have hne : ι.infinite w i ≠ 0 := by
    intro h0
    have := congrArg (· ^ 2) h0
    simp only [← map_pow, hi, map_neg, map_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    exact one_ne_zero (neg_eq_zero.1 this)
  have hsq : (ι.infinite w i) ^ 2 = -1 := by rw [← map_pow, hi, map_neg, map_one]
  have h4 : (Units.mk0 _ hne) ^ 4 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, show 4 = 2 * 2 from rfl, pow_mul, hsq]
    norm_num
  have h := closureConj_apply_of_pow_eq_one w hw (Units.mk0 _ hne) (by norm_num) h4
  rw [Units.val_mk0] at h
  rw [h, map_neg, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hmul : ι.infinite w i * -ι.infinite w i = 1 := by linear_combination -hsq
  exact (eq_inv_of_mul_eq_one_right hmul).symm

variable {L : IntermediateField K Ω} [NumberField L]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
  (hLi : L = IntermediateField.adjoin K {i})

include hi hiS hLi in
/-- The image of the complex conjugation does not fix `K(i)`. -/
theorem realLocalizationHom_closureConj_not_mem :
    realLocalizationHom ι S w (closureConj w hw) ∉
      GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL := by
  intro hmem
  have hiL : i ∈ L := hLi ▸ IntermediateField.mem_adjoin_simple_self K i
  have h1 := (GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff S hL _).1 hmem ⟨i, hiL⟩
  have he : embeddingMaximalUnramifiedOutside hL ⟨i, hiL⟩ = ⟨i, hiS⟩ := Subtype.ext rfl
  rw [he, realLocalizationHom_closureConj_apply S ι hi hiS w hw] at h1
  have h2 : (2 : Ω) * i = 0 := by
    have := congrArg Subtype.val h1
    change -i = i at this
    linear_combination -this
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hi0 : i = 0 := (mul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [hi0] at hi
  norm_num at hi

include hi hiS hLi in
/-- `G_S` is the union of the cosets of `G_S(K(i))` represented by `1` and the image of the
complex conjugation. -/
theorem mul_inv_realLocalizationHom_closureConj_mem (g : GaloisGroupUnramifiedOutside K Ω S)
    (hg : g ∉ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) :
    g * (realLocalizationHom ι S w (closureConj w hw))⁻¹ ∈
      GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL := by
  set c := realLocalizationHom ι S w (closureConj w hw)
  have hgi : g ⟨i, hiS⟩ = -⟨i, hiS⟩ := (apply_sqrt_neg_one S hi hiS g).resolve_left fun h =>
    hg (mem_fixingOpenSubgroup_of_apply_eq S hiS hL hLi g h)
  have hc : c ⟨i, hiS⟩ = -⟨i, hiS⟩ := realLocalizationHom_closureConj_apply S ι hi hiS w hw
  have hc' : c (-⟨i, hiS⟩) = ⟨i, hiS⟩ := by rw [map_neg, hc, neg_neg]
  have hci : c⁻¹ ⟨i, hiS⟩ = -⟨i, hiS⟩ := (AlgEquiv.symm_apply_eq c).2 hc'.symm
  refine mem_fixingOpenSubgroup_of_apply_eq S hiS hL hLi _ ?_
  change g (c⁻¹ ⟨i, hiS⟩) = ⟨i, hiS⟩
  rw [hci, map_neg, hgi, neg_neg]

end Conjugation

section Generic

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The connecting map of a short exact sequence whose middle term has no cohomology in degrees `r`
and `r + 1` is bijective. -/
theorem bijective_δ_of_subsingleton {X : ShortComplex (Rep.{u} k G)} [IsSmoothRep X.X₁]
    [IsSmoothRep X.X₂] [IsSmoothRep X.X₃] (hX : X.ShortExact) (r : ℕ)
    (h₁ : Subsingleton (cohomology X.X₂ r)) (h₂ : Subsingleton (cohomology X.X₂ (r + 1))) :
    Function.Bijective (δ hX r (r + 1) rfl).hom := by
  refine ⟨?_, fun y => (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hX r (r + 1) rfl) y
    (Subsingleton.elim _ _)⟩
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hX r (r + 1) rfl) x hx
  rw [Subsingleton.elim y 0, map_zero]
  exact Submodule.zero_mem _

end Generic

section LocalInduced

attribute [-instance] ULift.module

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)
  {i : Ω} (hi : i ^ 2 = -1) (hiS : i ∈ maximalUnramifiedOutside K Ω S)
  {L : IntermediateField K Ω} [NumberField L]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
  (hLi : L = IntermediateField.adjoin K {i}) (w : InfinitePlace K) (hw : w.IsReal)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]

/-- The module induced from `G_S(K(i))`, restricted to the Galois group of a real place, as functions
on that group. -/
def coindRealLocal :
    Rep.res (realLocalizationHom ι S w : Gal(AlgebraicClosure w.Completion/w.Completion) →*
        GaloisGroupUnramifiedOutside K Ω S)
      (Rep.coind ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (Rep.res ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)) ⟶
      discreteCoind (ULift.{u} ℤ) Gal(AlgebraicClosure w.Completion/w.Completion) M :=
  Rep.ofHom ⟨{ toFun := fun f => ⟨fun σ => f.1 (realLocalizationHom ι S w σ),
                (isLocallyConstant_coind (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) _
                  f).comp_continuous (realLocalizationHom ι S w).continuous⟩
               map_add' := fun _ _ => rfl
               map_smul' := fun _ _ => rfl },
    fun τ => LinearMap.ext fun f => LocallyConstant.ext fun σ => by
      change f.1 (realLocalizationHom ι S w σ * realLocalizationHom ι S w τ) =
        f.1 (realLocalizationHom ι S w (σ * τ))
      rw [map_mul]⟩

theorem coindRealLocal_apply
    (f : Rep.coind ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (Rep.res ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M))
    (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) :
    (coindRealLocal S ι hL w M).hom f σ = f.1 (realLocalizationHom ι S w σ) :=
  rfl

include hi hiS hLi hw in
/-- At a real place the module induced from `G_S(K(i))` is induced from the trivial group. -/
theorem bijective_coindRealLocal : Function.Bijective (coindRealLocal S ι hL w M).hom := by
  classical
  set U := (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)) with hU
  set c := realLocalizationHom ι S w (closureConj w hw) with hc
  have hcU : c ∉ U := realLocalizationHom_closureConj_not_mem S ι hi hiS w hw hL hLi
  have hgU : ∀ g, g ∉ U → g * c⁻¹ ∈ U := fun g hg =>
    mul_inv_realLocalizationHom_closureConj_mem S ι hi hiS w hw hL hLi g hg
  refine ⟨(injective_iff_map_eq_zero _).2 fun f hf => ?_, fun F => ?_⟩
  · have h1 : f.1 1 = 0 := by
      have h := congrArg (fun F : LocallyConstant _ _ => F 1) hf
      change f.1 (realLocalizationHom ι S w 1) = 0 at h
      rwa [map_one] at h
    have hc0 : f.1 c = 0 := congrArg (fun F : LocallyConstant _ _ => F (closureConj w hw)) hf
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ U
    · have e := f.2 ⟨g, hg⟩ 1
      rw [mul_one] at e
      change f.1 g = M.ρ g (f.1 1) at e
      rw [e, h1, map_zero]
      rfl
    · have e := f.2 ⟨g * c⁻¹, hgU g hg⟩ c
      rw [Subgroup.subtype_apply, inv_mul_cancel_right] at e
      change f.1 g = M.ρ (g * c⁻¹) (f.1 c) at e
      rw [e, hc0, map_zero]
      rfl
  · let f : GaloisGroupUnramifiedOutside K Ω S → M := fun g =>
      if g ∈ U then M.ρ g (F 1) else M.ρ (g * c⁻¹) (F (closureConj w hw))
    have hf : f ∈ Representation.coindV U.subtype (Rep.res U.subtype M).ρ := by
      intro u g
      by_cases hg : g ∈ U
      · have hug : (u : GaloisGroupUnramifiedOutside K Ω S) * g ∈ U := U.mul_mem u.2 hg
        simp only [f, Subgroup.subtype_apply, hg, hug, ↓reduceIte, map_mul,
          Module.End.mul_apply]
        rfl
      · have hug : (u : GaloisGroupUnramifiedOutside K Ω S) * g ∉ U := fun h =>
          hg (by simpa using U.mul_mem (U.inv_mem u.2) h)
        simp only [f, Subgroup.subtype_apply, hg, hug, ↓reduceIte, map_mul,
          Module.End.mul_apply]
        rfl
    refine ⟨⟨f, hf⟩, LocallyConstant.ext fun σ => ?_⟩
    rw [coindRealLocal_apply]
    rcases eq_one_or_eq_closureConj w hw σ with rfl | rfl
    · simp only [f, map_one, U.one_mem, ↓reduceIte, Module.End.one_apply]
    · simp only [f, ← hc, hcU, ↓reduceIte, mul_inv_cancel, map_one, Module.End.one_apply]

include hi hiS hLi hw in
/-- At a real place the module induced from `G_S(K(i))` has no cohomology in positive degree. -/
theorem subsingleton_cohomology_res_coind (q : ℕ) :
    Subsingleton (cohomology (Rep.res (realLocalizationHom ι S w :
        Gal(AlgebraicClosure w.Completion/w.Completion) →* GaloisGroupUnramifiedOutside K Ω S)
      (Rep.coind ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (Rep.res ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M))) (q + 1)) := by
  have e := repIsoOfBijective (coindRealLocal S ι hL w M)
    (bijective_coindRealLocal S ι hi hiS hL hLi w hw M)
  exact ModuleCat.subsingleton_of_isZero
    ((isZero_cohomology_discreteCoind (ULift.{u} ℤ) _ M q).of_iso (cohomologyIsoOfIso e (q + 1)))

end LocalInduced

section RealShift

attribute [-instance] ULift.module

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)
  {i : Ω} (hi : i ^ 2 = -1) (hiS : i ∈ maximalUnramifiedOutside K Ω S)
  {L : IntermediateField K Ω} [NumberField L]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
  (hLi : L = IntermediateField.adjoin K {i}) (hLc : IsTotallyComplex L)

include hi hiS hLi hLc in
/-- **Dimension shift for the real localization.** With `B = Ind_U^{G_S} M / M` for `U = G_S(K(i))`,
the localization of `M` to the real places in degree `r + 1` is bijective when that of `B` is in degree
`r`, `r ≥ 3`. -/
theorem bijective_realLocalization_succ {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 3 ≤ r)
    (hB : Function.Bijective fun (x : cohomology (coindUnitSequence
        ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
            Subgroup (GaloisGroupUnramifiedOutside K Ω S)) M).X₃ r)
        (w : {w : InfinitePlace K // w.IsReal}) => realLocalization ι _ w.1 r x) :
    Function.Bijective fun (x : cohomology M (r + 1)) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 (r + 1) x := by
  set U := GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL with hUdef
  let X := coindUnitSequence (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) M
  have hX : X.ShortExact := coindUnitSequence_shortExact _ M
  have hU : ∀ q, 3 ≤ q →
      Subsingleton (cohomology (Rep.res (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        M) q) := fun q hq =>
    subsingleton_cohomology_fixingOpenSubgroup_of_isTotallyComplex S L hL hLc hn hS _
      (fun m => hM m) hq
  have hI : ∀ q, 3 ≤ q → Subsingleton (cohomology X.X₂ q) := fun q hq => by
    have := hU q hq
    exact (shapiroIso U (Rep.res (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M)
      q).toLinearEquiv.toEquiv.subsingleton
  have hδ := bijective_δ_of_subsingleton hX r (hI r hr) (hI (r + 1) (by omega))
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  -- the local sequences
  have hXw : ∀ w : {w : InfinitePlace K // w.IsReal},
      (X.map (Rep.resFunctor (realLocalizationHom ι S w.1 :
        Gal(AlgebraicClosure w.1.Completion/w.1.Completion) →*
          GaloisGroupUnramifiedOutside K Ω S))).ShortExact :=
    fun w => (Rep.shortExact_res _).2 hX
  have hδw : ∀ w : {w : InfinitePlace K // w.IsReal},
      Function.Bijective (δ (hXw w) (q + 1) (q + 1 + 1) rfl).hom := fun w =>
    bijective_δ_of_subsingleton (hXw w) (q + 1)
      (subsingleton_cohomology_res_coind S ι hi hiS hL hLi w.1 w.2 M q)
      (subsingleton_cohomology_res_coind S ι hi hiS hL hLi w.1 w.2 M (q + 1))
  have hnat : ∀ (w : {w : InfinitePlace K // w.IsReal}) (x : cohomology X.X₃ (q + 1)),
      realLocalization ι M w.1 (q + 1 + 1) ((δ hX (q + 1) (q + 1 + 1) rfl).hom x) =
        (δ (hXw w) (q + 1) (q + 1 + 1) rfl).hom (realLocalization ι X.X₃ w.1 (q + 1) x) :=
    fun w x => congrArg (fun F => F.hom x)
      (δ_comp_map (realLocalizationHom ι S w.1) (𝟙 _) hX (hXw w) (q + 1) (q + 1 + 1) rfl)
  let Δ : (∀ w : {w : InfinitePlace K // w.IsReal}, cohomology (realLocalModule ι X.X₃ w.1) (q + 1)) →
      ∀ w : {w : InfinitePlace K // w.IsReal}, cohomology (realLocalModule ι M w.1) (q + 1 + 1) :=
    fun t w => (δ (hXw w) (q + 1) (q + 1 + 1) rfl).hom (t w)
  have hΔ : Function.Bijective Δ := by
    refine ⟨fun t t' h => funext fun w => (hδw w).1 (congrFun h w), fun s => ?_⟩
    exact ⟨fun w => ((hδw w).2 (s w)).choose, funext fun w => ((hδw w).2 (s w)).choose_spec⟩
  have hcomp : (fun (x : cohomology M (q + 1 + 1)) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 (q + 1 + 1) x) ∘ (δ hX (q + 1) (q + 1 + 1) rfl).hom =
      Δ ∘ fun (x : cohomology X.X₃ (q + 1)) (w : {w : InfinitePlace K // w.IsReal}) =>
        realLocalization ι X.X₃ w.1 (q + 1) x :=
    funext fun x => funext fun w => hnat w x
  refine (Function.Bijective.of_comp_iff _ hδ).1 ?_
  have h := hΔ.comp hB
  rw [← hcomp] at h
  exact h

end RealShift

section TateHighDegree

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ι : PlaceEmbeddings K Ω)

/-- **The real places above degree two, from degree three.** -/
theorem bijective_realLocalization_of_nsmul_of_degreeThree
    (h : RealLocalizationDegreeThreeStatement.{u})
    {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) {r : ℕ} (hr : 3 ≤ r) :
    ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M],
      (∀ m : M, n • m = 0) →
      Function.Bijective fun (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) =>
        realLocalization ι M w.1 r x := by
  induction r, hr using Nat.le_induction with
  | base => exact fun M _ _ hM => h K Ω S ι M n hn hM hS
  | succ r hr ih =>
    intro M _ _ hM
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨i, L, _, hL, hLc, hi, hiS, hLi⟩ :=
        exists_isTotallyComplex_intermediateField (Ω := Ω) S (two_mem_of_even he hS)
      let U := GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL
      have := finite_coindUnitSequence_X₃ U M
      exact bijective_realLocalization_succ S ι hi hiS hL hLi hLc hn hS M hM hr
        (ih _ (nsmul_coindUnitSequence_X₃ U M hM))
    · exact bijective_realLocalization_of_odd_or_isTotallyComplex S ι M hn hM hS (Or.inl ho)
        (by omega)

/-- **Tate's theorem on the real places.** Assume `RealLocalizationDegreeThreeStatement`. For a
finite set `S` of finite places and a finite smooth `G_S`-module `M` such that every finite place above
`#M` lies in `S`, the localization `Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M)` is bijective for every
`r ≥ 3`. -/
theorem bijective_realLocalization_of_degreeThree (h : RealLocalizationDegreeThreeStatement.{u})
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {r : ℕ} (hr : 3 ≤ r) :
    Function.Bijective fun (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 r x :=
  bijective_realLocalization_of_nsmul_of_degreeThree S ι h Nat.card_pos.ne' hS hr M
    fun _ => card_nsmul_eq_zero'

end TateHighDegree

end

end Langlands.GaloisCohomology

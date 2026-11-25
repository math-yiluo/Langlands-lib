import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.DegreeThree
import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.HighDegreeInflation
import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.RealComponents

/-!
# `Hʳ(Gal(Ω/K), Ωˣ)` for `r ≥ 4`: the real places

For `r ≥ 4` the localization `Hʳ(Gal(Ω/K), Ωˣ) → ∏_{w real} Hʳ(Gal(K̄_w/K_w), K̄_wˣ)` is bijective
(Neukirch–Schmidt–Wingberg (8.1.20) and its proof; Tate in Cassels–Fröhlich VII §11.4). The proof is
at finite Galois levels `E ⊆ Ω`:

* *Injectivity* (`eq_zero_of_realBrauerLocalization_eq_zero`). Let `x = infl a`, `a ∈ Hʳ(Gal(E/K), Eˣ)`,
  with trivial real localizations, and `b` the image of `a` in `Hʳ(Gal(E/K), J_E)`. The infinite
  components of `b` vanish (the real comparison is injective, and is the localization on principal
  classes); only finitely many finite components are nonzero, and they die at a level `L` whose local
  degrees there are divisible by `[E : K]²` (local Tate–Nakayama). Hence the inflation of `b` to `L`
  is zero (local triviality of idèle cohomology), the inflation of `a` is `δ c` with
  `c ∈ Hʳ⁻¹(Gal(L/K), C_L)`, and `c` dies at a level `L'` with `[L : K] ∣ [L' : L]`; so `x = 0`.
* *Surjectivity* (`exists_realBrauerLocalization_eq`). At the level `E = K(i)` every real place
  becomes complex and the real comparison at `w` is bijective; the sum `y` of the infinite local
  sections of the preimages of the given local classes lies in `Hʳ(Gal(E/K), J_E)`. Its image in
  `Hʳ(Gal(E/K), C_E)` dies at a level `L`, so the inflation of `y` to `L` is the image of a class
  `a'` of `Hʳ(Gal(L/K), Lˣ)`, and `infl a'` has the given real localizations.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Limits NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ProfiniteCohomology Langlands.Galois
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension IntermediateField

universe u

noncomputable section

attribute [local instance] isGalois_adicCompletion FiniteExtension.local_finite

/-- The foundations' cohomology of `K̄_wˣ` at a complex place vanishes in positive degree. -/
theorem subsingleton_cohomology_of_isComplex {K : Type u} [Field K] [NumberField K]
    {w : InfinitePlace K} (hw : w.IsComplex) (n : ℕ) :
    Subsingleton (cohomology (unitsModule w.Completion (AlgebraicClosure w.Completion)) (n + 1)) := by
  have : Subsingleton Gal(AlgebraicClosure w.Completion/w.Completion) :=
    ⟨fun a b => (eq_one_of_isComplex w hw a).trans (eq_one_of_isComplex w hw b).symm⟩
  have := ModuleCat.isZero_iff_subsingleton.1 (isZero_groupCohomology_succ_of_subsingleton
    (unitsModule w.Completion (AlgebraicClosure w.Completion)) n)
  exact (isoGroupCohomology (unitsModule w.Completion (AlgebraicClosure w.Completion))
    (n + 1)).toLinearEquiv.injective.subsingleton

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω)

/-- The infinite components of the image in idèle cohomology of a class whose inflation has
trivial real localizations vanish. -/
theorem ideleInfiniteLocalMap_principal_eq_zero (E : IntermediateField K Ω) [FiniteDimensional K E]
    [IsGalois K E] [NumberField E] (n : ℕ) (a : relativeCohomology K E (n + 1))
    (h : ∀ w : InfinitePlace K, w.IsReal →
      realBrauerLocalization ι w (n + 1) ((unitsInflation E (n + 1)).hom a) = 0)
    (w : InfinitePlace K) :
    ideleInfiniteLocalMap (F := K) (realPlace ι E w) (n + 1) (principalIdeleCohomologyMap K E (n + 1) a) =
      0 := by
  apply injective_realLocalComparison ι E w n
  rw [map_zero, ← ConcreteCategory.comp_apply, ← realIdeleComparison_eq,
    realIdeleComparison_principal]
  by_cases hw : w.IsReal
  · exact h w hw
  · exact (subsingleton_cohomology_of_isComplex (InfinitePlace.not_isReal_iff_isComplex.1 hw) n).elim _ _

/-- **Injectivity at a finite level.** A class of `Hⁿ⁺⁴(Gal(E/K), Eˣ)` whose inflation to
`Gal(Ω/K)` has trivial real localizations inflates to zero. -/
theorem unitsInflation_eq_zero_of_realBrauerLocalization (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsGalois K E] (n : ℕ) (a : groupCohomology (unitsModule K E) (n + 4))
    (h : ∀ w : InfinitePlace K, w.IsReal →
      realBrauerLocalization ι w (n + 4) ((unitsInflation E (n + 4)).hom a) = 0) :
    (unitsInflation E (n + 4)).hom a = 0 := by
  classical
  have : NumberField E := NumberField.of_module_finite K E
  set b := principalIdeleCohomologyMap K E (n + 4) a with hbdef
  have hinfE := ideleInfiniteLocalMap_principal_eq_zero ι E (n + 3) a h
  -- the finite components of `b`
  let wfE : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 E) := fun v => (placeAbove E v).1
  have hwfE : ∀ v, (wfE v).asIdeal.LiesOver v.asIdeal := fun v => (placeAbove E v).2
  have hT := finite_ideleLocalMap_ne_zero wfE (fun v => realPlace ι E v)
    (comap_realPlace_algebraMap ι E) (n + 3) b
  -- a level with large local degrees above the support
  have hpos : 0 < Module.finrank K E := Module.finrank_pos
  obtain ⟨L, hL, hLgal, hEL, hdvd⟩ := exists_le_localDegreesDvd_of_finset E hT.toFinset
    (Module.finrank K E * Module.finrank K E) (Nat.mul_ne_zero hpos.ne' hpos.ne')
  have : NumberField L := NumberField.of_module_finite K L
  let _ : Algebra E L := (IntermediateField.inclusion hEL).toRingHom.toAlgebra
  have _ : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
  let wfL : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L) := fun v =>
    (placeAbove L (wfE v)).1
  have hq1 : ∀ v, (wfL v).asIdeal.LiesOver (wfE v).asIdeal := fun v => (placeAbove L (wfE v)).2
  have hq2 : ∀ v, (wfL v).asIdeal.LiesOver v.asIdeal := fun v =>
    Ideal.LiesOver.trans (wfL v).asIdeal (wfE v).asIdeal v.asIdeal
  -- the inflation of `b` to `L` vanishes
  have hb : relativeIdeleInflation K E L (n + 4) b = 0 := by
    refine eq_zero_of_ideleLocalMap_eq_zero wfL (fun v => realPlace ι L v)
      (comap_realPlace_algebraMap ι L) (n + 3) _ (fun v => ?_) (fun v => ?_)
    · change ideleLocalMap v (wfL v) (n + 4) (relativeIdeleInflation K E L (n + 4) b) = 0
      rw [ideleLocalMap_relativeIdeleInflation v (wfE v) (wfL v)]
      by_cases hv : v ∈ hT.toFinset
      · have hd := hdvd v hv (wfL v)
        have hw := localDegree_dvd v (wfE v)
        have htower := Module.finrank_mul_finrank (v.adicCompletion K) ((wfE v).adicCompletion E)
          ((wfL v).adicCompletion L)
        change _ ∣ Module.finrank (v.adicCompletion K) ((wfL v).adicCompletion L) at hd
        rw [← htower] at hd
        have hpos' : 0 < Module.finrank (v.adicCompletion K) ((wfE v).adicCompletion E) :=
          Module.finrank_pos
        exact relativeInflation_adicCompletion_eq_zero_of_dvd v (wfE v) (wfL v)
          (Nat.dvd_of_mul_dvd_mul_left hpos' ((mul_dvd_mul hw hw).trans hd)) (n + 2) _
      · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
        rw [hv, map_zero]
    · apply injective_realLocalComparison ι L v (n + 3)
      rw [map_zero, ← ConcreteCategory.comp_apply, ← realIdeleComparison_eq,
        realIdeleComparison_inflation ι v hEL, realIdeleComparison_eq, ConcreteCategory.comp_apply,
        hinfE v, map_zero]
  -- the inflation of `a` to `L` is a connecting image
  have hprin : principalIdeleCohomologyMap K L (n + 4) (relativeInflation K E L (n + 4) a) = 0 := by
    rw [← ConcreteCategory.comp_apply, relativeInflation_comp_principal, ConcreteCategory.comp_apply]
    exact hb
  obtain ⟨c, hc⟩ : ∃ c : relativeIdeleClassCohomology K L (n + 3),
      groupCohomology.δ (ideleCoefficientSequence_shortExact K L) (n + 3) (n + 4) rfl c =
        relativeInflation K E L (n + 4) a := by
    have hex := (groupCohomology.mapShortComplex₁_exact (ideleCoefficientSequence_shortExact K L)
      (i := n + 3) (j := n + 4) rfl).moduleCat_range_eq_ker
    have ha : relativeInflation K E L (n + 4) a ∈ LinearMap.ker
        (groupCohomology.mapShortComplex₁ (ideleCoefficientSequence_shortExact K L)
          (i := n + 3) (j := n + 4) rfl).g.hom := hprin
    rw [← hex] at ha
    exact ha
  -- `c` dies at a further level
  obtain ⟨L', hL', hL'gal, hLL', hdvd'⟩ := exists_le_dvd_finrank L
  have : NumberField L' := NumberField.of_module_finite K L'
  let _ : Algebra L L' := (IntermediateField.inclusion hLL').toRingHom.toAlgebra
  have _ : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq' rfl
  have hc0 : relativeIdeleClassInflation K L L' ((n + 1) + 2) c = 0 :=
    relativeIdeleClassInflation_eq_zero_of_dvd hdvd' (n + 1) c
  have h4 : relativeInflation K L L' (n + 4) (relativeInflation K E L (n + 4) a) = 0 := by
    rw [← hc, relativeInflation_δ_apply]
    erw [hc0]
    exact map_zero _
  -- conclusion
  have h5 := ConcreteCategory.congr_hom (unitsInflationOfLE_comp_unitsInflation hEL (n + 4)) a
  have h6 := ConcreteCategory.congr_hom (unitsInflationOfLE_comp_unitsInflation hLL' (n + 4))
    ((unitsInflationOfLE hEL (n + 4)).hom a)
  rw [← h5]
  change (unitsInflation L (n + 4)).hom ((unitsInflationOfLE hEL (n + 4)).hom a) = 0
  rw [← h6]
  change (unitsInflation L' (n + 4)).hom ((unitsInflationOfLE hLL' (n + 4)).hom
    ((unitsInflationOfLE hEL (n + 4)).hom a)) = 0
  rw [unitsInflationOfLE_eq_relativeInflation hLL', unitsInflationOfLE_eq_relativeInflation hEL]
  change (unitsInflation L' (n + 4)).hom (relativeInflation K L L' (n + 4)
    (relativeInflation K E L (n + 4) a)) = 0
  rw [h4, map_zero]

/-- **Injectivity of the real localization in degrees `≥ 4`.** -/
theorem eq_zero_of_realBrauerLocalization_eq_zero (n : ℕ) (x : cohomology (unitsModule K Ω) (n + 4))
    (h : ∀ w : InfinitePlace K, w.IsReal → realBrauerLocalization ι w (n + 4) x = 0) : x = 0 := by
  obtain ⟨E, a, rfl⟩ := exists_unitsInflation_eq (n + 4) x
  exact unitsInflation_eq_zero_of_realBrauerLocalization ι E.toIntermediateField n a h

/-- **Surjectivity at a level containing `√-1`.** If the finite Galois level `E` contains a square
root of `-1`, every family of classes at the real places is the real localization of the inflation
of a class from some finite level above `E`. -/
theorem exists_realBrauerLocalization_eq_of_sq_eq_neg_one (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsGalois K E] [NumberField E] {i : E} (hi : i ^ 2 = -1) (n : ℕ)
    (β : ∀ w : {w : InfinitePlace K // w.IsReal},
      cohomology (unitsModule w.1.Completion (AlgebraicClosure w.1.Completion)) (n + 4)) :
    ∃ x : cohomology (unitsModule K Ω) (n + 4),
      ∀ w : {w : InfinitePlace K // w.IsReal}, realBrauerLocalization ι w.1 (n + 4) x = β w := by
  classical
  -- the local comparison is bijective at every real place
  have hbij : ∀ w : {w : InfinitePlace K // w.IsReal},
      Function.Bijective (realLocalComparison ι E w.1 (n + 4)) := by
    intro w
    refine bijective_realLocalComparison ι E w.1 ⟨realRestrict ι E w.1 (closureConj w.1 w.2),
      realRestrict_mem_stabilizer ι E w.1 _, ?_⟩ (n + 4)
    have hc := isConj_realRestrict_closureConj ι E w.1 w.2
    refine (ComplexEmbedding.isConj_ne_one_iff hc).2 fun hr => ?_
    exact sq_ne_neg_one_of_isReal hr _ hi
  choose γ hγ using fun w => (hbij w).2 (β w)
  -- the idèle class `y`
  have hfin : ∀ w : {w : InfinitePlace K // w.IsReal}, Fintype ((E ≃ₐ[K] E) ⧸
      (MulAction.stabilizer (E ≃ₐ[K] E) (realPlace ι E w.1)).subtype.range) :=
    fun w => Fintype.ofFinite _
  let y : relativeIdeleCohomology K E (n + 4) := ∑ w : {w : InfinitePlace K // w.IsReal},
    (ideleInfiniteLocalSection (F := K) (realPlace ι E w.1) (n + 4)).hom (γ w)
  have hy : ∀ w : {w : InfinitePlace K // w.IsReal},
      ideleInfiniteLocalMap (F := K) (realPlace ι E w.1) (n + 4) y = γ w := by
    intro w
    rw [map_sum, Finset.sum_eq_single w]
    · rw [← ConcreteCategory.comp_apply, ideleInfiniteLocalSection_comp_ideleInfiniteLocalMap]
      rfl
    · intro w₂ _ hw₂
      rw [← ConcreteCategory.comp_apply,
        ideleInfiniteLocalSection_comp_ideleInfiniteLocalMap_of_ne _ _ (fun g hg => hw₂ ?_)]
      · rfl
      · apply Subtype.ext
        have h1 := congrArg (fun p : InfinitePlace E => p.comap (algebraMap K E)) hg
        simp only [comap_infinitePlaceEquiv, comap_realPlace_algebraMap] at h1
        exact h1.symm
    · intro h
      exact absurd (Finset.mem_univ w) h
  -- kill the image of `y` in idèle-class cohomology
  obtain ⟨L, hL, hLgal, hEL, hdvd⟩ := exists_le_dvd_finrank E
  have : NumberField L := NumberField.of_module_finite K L
  let _ : Algebra E L := (IntermediateField.inclusion hEL).toRingHom.toAlgebra
  have _ : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
  have hq : ideleQuotientCohomologyMap K L (n + 4) (relativeIdeleInflation K E L (n + 4) y) = 0 := by
    rw [← ConcreteCategory.comp_apply, relativeIdeleInflation_comp_quotient,
      ConcreteCategory.comp_apply]
    exact relativeIdeleClassInflation_eq_zero_of_dvd hdvd (n + 2) _
  obtain ⟨a', ha'⟩ : ∃ a' : relativeCohomology K L (n + 4),
      principalIdeleCohomologyMap K L (n + 4) a' = relativeIdeleInflation K E L (n + 4) y := by
    have hex := (groupCohomology.mapShortComplex₂_exact
      (ideleCoefficientSequence_shortExact K L) (n + 4)).moduleCat_range_eq_ker
    have hk : relativeIdeleInflation K E L (n + 4) y ∈ LinearMap.ker
        (groupCohomology.mapShortComplex₂ (ideleCoefficientSequence K L) (n + 4)).g.hom := hq
    rw [← hex] at hk
    exact hk
  refine ⟨(unitsInflation L (n + 4)).hom a', fun w => ?_⟩
  rw [← realIdeleComparison_principal, ha', realIdeleComparison_inflation ι w.1 hEL,
    realIdeleComparison_eq, ConcreteCategory.comp_apply, hy w]
  exact hγ w

/-- **Surjectivity of the real localization in degrees `≥ 4`.** -/
theorem exists_realBrauerLocalization_eq (n : ℕ)
    (β : ∀ w : {w : InfinitePlace K // w.IsReal},
      cohomology (unitsModule w.1.Completion (AlgebraicClosure w.1.Completion)) (n + 4)) :
    ∃ x : cohomology (unitsModule K Ω) (n + 4),
      ∀ w : {w : InfinitePlace K // w.IsReal}, realBrauerLocalization ι w.1 (n + 4) x = β w := by
  by_cases hK : ∃ w : InfinitePlace K, w.IsReal
  swap
  · exact ⟨0, fun w => absurd ⟨w.1, w.2⟩ hK⟩
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one (K := K) (Ω := Ω)
  have hdeg : Module.finrank K K⟮i⟯ = 2 := finrank_adjoin_sqrt_neg_one hK hi
  have : Module.Finite K K⟮i⟯ := Module.finite_of_finrank_eq_succ hdeg
  have : Algebra.IsQuadraticExtension K K⟮i⟯ := ⟨hdeg⟩
  have : IsGalois K K⟮i⟯ := inferInstance
  have : NumberField K⟮i⟯ := NumberField.of_module_finite K K⟮i⟯
  exact exists_realBrauerLocalization_eq_of_sq_eq_neg_one ι K⟮i⟯
    (i := ⟨i, IntermediateField.mem_adjoin_simple_self K i⟩) (Subtype.ext hi) n β

/-- **`Hʳ(Gal(Ω/K), Ωˣ) ≅ ∏_{w real} Hʳ(Gal(K̄_w/K_w), K̄_wˣ)` for `r ≥ 4`**: the localization at the
real places is bijective. -/
theorem bijective_realBrauerLocalization (r : ℕ) (hr : 4 ≤ r) :
    Function.Bijective fun (x : cohomology (unitsModule K Ω) r)
      (w : {w : InfinitePlace K // w.IsReal}) => realBrauerLocalization ι w.1 r x := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 4 := ⟨r - 4, by omega⟩
  refine ⟨fun x y hxy => ?_, fun β => ?_⟩
  · rw [← sub_eq_zero]
    refine eq_zero_of_realBrauerLocalization_eq_zero ι n _ fun w hw => ?_
    rw [map_sub, sub_eq_zero]
    exact congrFun hxy ⟨w, hw⟩
  · obtain ⟨x, hx⟩ := exists_realBrauerLocalization_eq ι n β
    exact ⟨x, funext hx⟩

end

end Langlands.GaloisCohomology

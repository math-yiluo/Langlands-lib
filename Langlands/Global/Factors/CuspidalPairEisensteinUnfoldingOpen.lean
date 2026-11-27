import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingOpenMeasure

/-! # Integration over the open cell

For a function on `N₀(𝔸)` left invariant under the stabilizer `Λ_(J₀)(F) = N_(M')(F)` of the open
cell and integrable on a fundamental domain of it, the integral over that fundamental domain, for
the normalized Haar measure, is the iterated integral over `Y ∈ U'(𝔸)` of the integral over a
fundamental domain of `N_(t+1)(F) × N_(r+1)(F)` of the function at `diag(m) u'(Y)`. See the paired
Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open NumberField MeasureTheory Matrix Set

namespace Langlands.Global.CuspidalPairEisenstein.Unfolding

open RankinSelbergGlobal RowEchelon PrimitiveAdelicHeight LeftCosetSpace

variable (F : Type u) [Field F] [NumberField F] (r t : ℕ)

instance leviPartBorel : BorelSpace (LeviPart F r t) := Prod.borelSpace

instance radicalLeviBorel : BorelSpace (Radical F r t × LeviPart F r t) := Prod.borelSpace

instance leviRadicalBorel : BorelSpace (LeviPart F r t × Radical F r t) := Prod.borelSpace

instance haarN_sFinite : SFinite (haarN F r t) := by
  unfold haarN Semidirect.latticeNormalizedHaar
  infer_instance

instance haarM_sFinite : SFinite (haarM F r t) := by
  unfold haarM Semidirect.latticeNormalizedHaar
  infer_instance

instance haarH_sFinite : SFinite (haarH F r t) := by
  unfold haarH Semidirect.latticeNormalizedHaar
  infer_instance

instance haarN_isMulLeftInvariant : (haarN F r t).IsMulLeftInvariant := by
  unfold haarN Semidirect.latticeNormalizedHaar
  infer_instance

instance haarM_isMulLeftInvariant : (haarM F r t).IsMulLeftInvariant := by
  unfold haarM Semidirect.latticeNormalizedHaar
  infer_instance

instance haarH_isMulLeftInvariant : (haarH F r t).IsMulLeftInvariant := by
  unfold haarH Semidirect.latticeNormalizedHaar
  infer_instance

/-- Conjugation of the radical by the block diagonal group. -/
abbrev radicalConj (m : LeviPart F r t) : Radical F r t ≃ₜ* Radical F r t :=
  Semidirect.conj (radicalHom F r t) (leviHom F r t) (projHom F r t) (projHom_leviHom F r t)
    (exists_radicalHom_eq F r t) (projHom_radicalHom F r t) (isEmbedding_radicalHom F r t)
    (continuous_leviHom F r t) m

theorem radicalHom_radicalConj (m : LeviPart F r t) (n : Radical F r t) :
    radicalHom F r t (radicalConj F r t m n) =
      leviHom F r t m * radicalHom F r t n * (leviHom F r t m)⁻¹ :=
  Semidirect.i_conj _ _ _ _ _ _ _ _ m n

theorem continuous_radicalConj_uncurry :
    Continuous fun x : LeviPart F r t × Radical F r t => radicalConj F r t x.1 x.2 :=
  Semidirect.continuous_conjFun (leviHom F r t) (projHom F r t) (projHom_leviHom F r t)
    (exists_radicalHom_eq F r t) (projHom_radicalHom F r t) (isEmbedding_radicalHom F r t)
    (continuous_leviHom F r t)

theorem map_radicalConj_haarN (m : LeviPart F r t) :
    (haarN F r t).map (radicalConj F r t m) = haarN F r t := by
  have hN := isFiniteMeasure_radicalQuotient F r t
  have hM := isFiniteMeasure_leviQuotient F r t
  have hδ := Semidirect.mulEquivHaarChar_conj_eq_one_of_finiteCovolume (radicalHom F r t)
    (leviHom F r t) (projHom F r t) (projHom_leviHom F r t) (exists_radicalHom_eq F r t)
    (projHom_radicalHom F r t) (isEmbedding_radicalHom F r t) (continuous_leviHom F r t)
    (Γ₀ F (r + t + 2)) (leviLattice F r t) (isDiscrete_leviLattice F r t)
    (fun m hm => leviHom_mem_Γ₀ F r t hm) (isDiscrete_radicalLattice F r t) m
  have h := mulEquivHaarChar_smul_map (Measure.haar : Measure (Radical F r t))
    (radicalConj F r t m)
  rw [hδ, one_smul] at h
  rw [haarN, Semidirect.latticeNormalizedHaar, Measure.map_smul, h]
  exact (radicalConj F r t m).continuous.measurable.aemeasurable

/-- The change of variables `(Y, m) ↦ (m⁻¹ Y m, m)`. -/
def skewHomeomorph : Radical F r t × LeviPart F r t ≃ₜ Radical F r t × LeviPart F r t where
  toFun x := (radicalConj F r t x.2⁻¹ x.1, x.2)
  invFun x := (radicalConj F r t x.2 x.1, x.2)
  left_inv x := by
    apply Prod.ext
    · apply (isEmbedding_radicalHom F r t).injective
      simp only [radicalHom_radicalConj, map_inv]
      group
    · rfl
  right_inv x := by
    apply Prod.ext
    · apply (isEmbedding_radicalHom F r t).injective
      simp only [radicalHom_radicalConj, map_inv]
      group
    · rfl
  continuous_toFun := ((continuous_radicalConj_uncurry F r t).comp
    ((continuous_snd.inv).prodMk continuous_fst)).prodMk continuous_snd
  continuous_invFun := ((continuous_radicalConj_uncurry F r t).comp
    (continuous_snd.prodMk continuous_fst)).prodMk continuous_snd

theorem openProd_eq_skew (x : Radical F r t × LeviPart F r t) :
    openProd F r t x = leviHom F r t x.2 * radicalHom F r t (skewHomeomorph F r t x).1 := by
  rw [openProd_apply]
  change _ = leviHom F r t x.2 * radicalHom F r t (radicalConj F r t x.2⁻¹ x.1)
  rw [radicalHom_radicalConj, map_inv]
  group

theorem measurePreserving_skewHomeomorph :
    MeasurePreserving (skewHomeomorph F r t) ((haarN F r t).prod (haarM F r t))
      ((haarN F r t).prod (haarM F r t)) := by
  have hT : MeasurePreserving (fun p : LeviPart F r t × Radical F r t =>
      (id p.1, radicalConj F r t p.1⁻¹ p.2)) ((haarM F r t).prod (haarN F r t))
      ((haarM F r t).prod (haarN F r t)) := by
    refine (MeasurePreserving.id (haarM F r t)).skew_product (μc := haarN F r t)
      (μd := haarN F r t) (g := fun m n => radicalConj F r t m⁻¹ n) ?_ (ae_of_all _ fun m => ?_)
    · exact ((continuous_radicalConj_uncurry F r t).comp
        ((continuous_fst.inv).prodMk continuous_snd)).measurable
    · exact map_radicalConj_haarN F r t m⁻¹
  have hs1 := Measure.measurePreserving_swap (μ := haarN F r t) (ν := haarM F r t)
  have hs2 := Measure.measurePreserving_swap (μ := haarM F r t) (ν := haarN F r t)
  have := hs2.comp (hT.comp hs1)
  convert this using 1
  funext x
  rfl

omit [NumberField F] in
theorem fundamentalDomain_eq_univ {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (Λ : Subgroup H)
    (hΛ : IsDiscrete (Λ : Set H)) (h : Λ = ⊥) : fundamentalDomain Λ hΛ = univ := by
  ext x
  simp only [mem_univ, iff_true]
  obtain ⟨c, hc, -⟩ := fundamentalDomain_unique Λ hΛ x
  have hc1 : (c : H) = 1 := by
    have : (c : H) ∈ (⊥ : Subgroup H) := h ▸ c.2
    exact Subgroup.mem_bot.mp this
  simpa [hc1] using hc

/-- The chosen fundamental domain of `N_(t+1)(F) × N_(r+1)(F)`. -/
abbrev fdM : Set (LeviPart F r t) :=
  fundamentalDomain (leviLattice F r t) (isDiscrete_leviLattice F r t)

theorem isDiscrete_openLattice_comap :
    IsDiscrete (((openLattice F r t).comap (radicalHom F r t) : Subgroup (Radical F r t)) :
      Set (Radical F r t)) :=
  (isDiscrete_radicalLattice F r t).mono (Subgroup.comap_mono inf_le_left)

/-- The open cell product domain `{u'(Y) diag(m) : m ∈ fdM}`, a fundamental domain of
`Λ_(J₀)(F)`. -/
abbrev openDomain : Set (unipotentAdelic F (r + t + 2)) :=
  openProd F r t '' (univ ×ˢ fdM F r t)

theorem existsUnique_mem_openDomain (x : unipotentAdelic F (r + t + 2)) :
    ∃! l : openLattice F r t, (l : unipotentAdelic F (r + t + 2)) * x ∈ openDomain F r t := by
  have h := Semidirect.productFundamentalDomain_unique (radicalHom F r t) (leviHom F r t)
    (projHom F r t) (projHom_leviHom F r t) (exists_radicalHom_eq F r t)
    (projHom_radicalHom F r t) (isEmbedding_radicalHom F r t) (continuous_leviHom F r t)
    (continuous_projHom F r t) (openLattice F r t) (leviLattice F r t)
    (isDiscrete_leviLattice F r t) (fun m hm => leviHom_mem_openLattice F r t hm)
    (fun h hh => projHom_mem_leviLattice F r t hh.1) (isDiscrete_openLattice_comap F r t) x
  rwa [fundamentalDomain_eq_univ _ _ (comap_radicalHom_openLattice F r t)] at h

theorem measurableSet_openDomain : MeasurableSet (openDomain F r t) := by
  rw [openDomain, (openProd F r t).image_eq_preimage_symm]
  exact (openProd F r t).symm.continuous.measurable
    (MeasurableSet.univ.prod (measurableSet_fundamentalDomain _ _))

set_option synthInstance.maxHeartbeats 400000 in
instance openLatticeMulAction :
    MulAction (openLattice F r t) (unipotentAdelic F (r + t + 2)) :=
  inferInstance

instance openLatticeSMul : SMul (openLattice F r t) (unipotentAdelic F (r + t + 2)) :=
  (openLatticeMulAction F r t).toSMul

/-- **Integration over the open cell.** -/
theorem setIntegral_eq_iterated_open (f₀ : unipotentAdelic F (r + t + 2) → ℂ)
    (hinv : ∀ l ∈ openLattice F r t, ∀ x, f₀ (l * x) = f₀ x)
    {D : Set (unipotentAdelic F (r + t + 2))} (hDm : MeasurableSet D)
    (hD : ∀ x, ∃! l : openLattice F r t, (l : unipotentAdelic F (r + t + 2)) * x ∈ D)
    (hint : IntegrableOn f₀ D (haarH F r t)) :
    Integrable (fun p : Radical F r t × LeviPart F r t =>
        f₀ (leviHom F r t p.2 * radicalHom F r t p.1))
        ((haarN F r t).prod ((haarM F r t).restrict (fdM F r t))) ∧
      ∫ x in D, f₀ x ∂haarH F r t = ∫ n, ∫ m in fdM F r t,
        f₀ (leviHom F r t m * radicalHom F r t n) ∂haarM F r t ∂haarN F r t := by
  have hcount : Countable (openLattice F r t) :=
    countable_of_isDiscrete _ ((isDiscrete_Γ₀ F _).mono inf_le_left)
  have hfdD : IsFundamentalDomain (openLattice F r t) D (haarH F r t) :=
    IsFundamentalDomain.mk' hDm.nullMeasurableSet (fun x => hD x)
  have hfdE : IsFundamentalDomain (openLattice F r t) (openDomain F r t) (haarH F r t) :=
    IsFundamentalDomain.mk' (measurableSet_openDomain F r t).nullMeasurableSet
      (fun x => existsUnique_mem_openDomain F r t x)
  have hintE : IntegrableOn f₀ (openDomain F r t) (haarH F r t) :=
    (hfdD.integrableOn_iff hfdE (fun g x => hinv g g.2 x)).mp hint
  let Ψ : Radical F r t × LeviPart F r t → ℂ := fun p =>
    f₀ (leviHom F r t p.2 * radicalHom F r t p.1)
  have hcomp : f₀ ∘ openProd F r t = Ψ ∘ skewHomeomorph F r t := by
    funext p
    simp only [Function.comp_apply, Ψ]
    rw [openProd_eq_skew]
    rfl
  have hS := measurePreserving_skewHomeomorph F r t
  have hSemb : MeasurableEmbedding (skewHomeomorph F r t) :=
    (skewHomeomorph F r t).measurableEmbedding
  have hpre : (skewHomeomorph F r t) ⁻¹' (univ ×ˢ fdM F r t) = univ ×ˢ fdM F r t := by
    ext p
    simp [skewHomeomorph]
  have hΦemb : MeasurableEmbedding (openProd F r t) := (openProd F r t).measurableEmbedding
  have hrestrict : ((haarN F r t).prod (haarM F r t)).restrict (univ ×ˢ fdM F r t) =
      (haarN F r t).prod ((haarM F r t).restrict (fdM F r t)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hΨint : IntegrableOn Ψ (univ ×ˢ fdM F r t) ((haarN F r t).prod (haarM F r t)) := by
    have h1 := hintE
    rw [haarH_eq_map_prod, hΦemb.integrableOn_map_iff, (openProd F r t).preimage_image,
      hcomp, ← hpre] at h1
    exact (hS.integrableOn_comp_preimage hSemb).mp h1
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, hrestrict] at hΨint
    exact hΨint
  · have h2 : ∫ x in D, f₀ x ∂haarH F r t = ∫ x in openDomain F r t, f₀ x ∂haarH F r t :=
      hfdD.setIntegral_eq hfdE (fun g x => hinv g g.2 x)
    have h3 : ∫ x in openDomain F r t, f₀ x ∂haarH F r t =
        ∫ p in univ ×ˢ fdM F r t, f₀ (openProd F r t p) ∂((haarN F r t).prod (haarM F r t)) := by
      rw [haarH_eq_map_prod, (openProd F r t).isClosedEmbedding.setIntegral_map,
        (openProd F r t).preimage_image]
    have h4 : ∫ p in univ ×ˢ fdM F r t, f₀ (openProd F r t p) ∂((haarN F r t).prod (haarM F r t)) =
        ∫ p in univ ×ˢ fdM F r t, Ψ p ∂((haarN F r t).prod (haarM F r t)) := by
      have h5 : ∀ p, f₀ (openProd F r t p) = Ψ (skewHomeomorph F r t p) := fun p =>
        congrFun hcomp p
      simp_rw [h5]
      conv_lhs => rw [← hpre]
      exact hS.setIntegral_preimage_emb hSemb Ψ _
    rw [h2, h3, h4, hrestrict]
    rw [IntegrableOn, hrestrict] at hΨint
    exact integral_prod Ψ hΨint

end Langlands.Global.CuspidalPairEisenstein.Unfolding

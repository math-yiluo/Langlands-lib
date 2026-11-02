import Langlands.AlgebraicGeometry.Picard.TrivialLocusStrata

/-! # The triviality locus where sections are free of the expected rank is open

If the sections of all base changes of a line bundle `N` over a Noetherian base are free of the
rank `a` of global functions, then the fppf triviality locus of `N` is cut out by an open
immersion. Near a point of the locus, a second two-term complex and the polynomial trick of
`FrameCombinationTrivialization` give a flat finitely presented cover of an open neighbourhood
on which `N` is trivial.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
open Scheme.TwoAffineOpenCover (moduleSectionsOfHom specMap)
open Langlands.AlgebraicGeometry.AlgebraicSpace (specOver)

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

/-- Let `E` be an fppf-closed sieve on `Y` such that every point in the image of a member of
`E` has an open neighbourhood `V` with `V.ι ∈ E`. Then the union of these opens cuts out `E`. -/
lemma cutsOut_iSup_opens {Y : Scheme.{u}} {E : Sieve Y} (hE : Scheme.fppfTopology.IsClosed E)
    (h : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y), E g → ∀ x, ∃ V : Y.Opens, E V.ι ∧ g x ∈ V) :
    CutsOut (⨆ V : {V : Y.Opens // E V.ι}, V.1).ι E := by
  set U := ⨆ V : {V : Y.Opens // E V.ι}, V.1
  intro T g
  constructor
  · rintro ⟨k, rfl⟩
    refine hE _ (Scheme.fppfTopology.superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck
        (R := Presieve.ofArrows (fun V : {V : Y.Opens // E V.ι} => ((k ≫ U.ι) ⁻¹ᵁ V.1).toScheme)
          (fun V => ((k ≫ U.ι) ⁻¹ᵁ V.1).ι)) ?_))
    · rw [Sieve.generate_le_iff]
      rintro _ _ ⟨V⟩
      change E (((k ≫ U.ι) ⁻¹ᵁ V.1).ι ≫ k ≫ U.ι)
      rw [← morphismRestrict_ι]
      exact E.downward_closed V.2 _
    · rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨fun t => ?_, fun V => ⟨inferInstance, inferInstance⟩⟩
      have h1 : U.ι (k t) ∈ U := by
        change U.ι (k t) ∈ (U : Set Y)
        rw [← Scheme.Opens.range_ι]
        exact ⟨k t, rfl⟩
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp h1
      exact ⟨V, by rw [Scheme.Opens.range_ι]; exact hV⟩
  · intro hg
    refine ⟨IsOpenImmersion.lift U.ι g ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨x, rfl⟩
    obtain ⟨V, hV, hx⟩ := h g hg x
    rw [Scheme.Opens.range_ι]
    exact (le_iSup (fun V : {V : Y.Opens // E V.ι} => V.1) ⟨V, hV⟩) hx

namespace RelativePicard

open Langlands.LinearAlgebra.KernelColumnSplit

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))

/-- `SectionsFree X N a`: for every `C`-algebra `A`, the global sections of the base change of
`N` along `Spec A ⟶ Spec C` form a free `A`-module of rank `a`. -/
def SectionsFree {C : Type u} [CommRing C] [Algebra k C]
    (N : LineBundle ((relativeSpace X.hom).obj (specOver k C))) (a : ℕ) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra C A],
    letI := moduleSectionsOfHom (pullback.snd (baseMap X C) (specMap C A))
      ((Scheme.Modules.pullback (pullback.fst (baseMap X C) (specMap C A))).obj N.obj) ⊤
    Nonempty (Γ((Scheme.Modules.pullback (pullback.fst (baseMap X C) (specMap C A))).obj N.obj,
      ⊤) ≃ₗ[A] (Fin a → A))

set_option backward.isDefEq.respectTransparency.types false in
/-- If the sections of all base changes of `N` are free of rank `a`, then every point in the
image of a member of the triviality locus has an open neighbourhood `V` with `V.ι` in the
triviality locus. -/
theorem exists_open_of_mem_trivialLocus [IsProper X.hom] {a : ℕ} (ha : SectionsRank X a)
    {C : Type u} [CommRing C] [IsNoetherianRing C] [Algebra k C]
    {N : LineBundle ((relativeSpace X.hom).obj (specOver k C))} (hfree : SectionsFree X N a)
    {T' : Scheme.{u}} {g : T' ⟶ Spec (.of C)} (hg : trivialLocus X.hom (specOver k C) N g)
    (x : T') :
    ∃ V : (Spec (.of C)).Opens, trivialLocus X.hom (specOver k C) N V.ι ∧ g x ∈ V := by
  have hN := isInvertible_of_isLocallyFreeRankOne N.property
  obtain ⟨G, ε₀, ε, hcompat⟩ :=
    Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange (baseMap X C) N.obj
      hN.exists_trivialization
  obtain ⟨K, _, _, hker, hK⟩ := exists_field_of_mem_trivialLocus X hg x
  obtain ⟨S, hcard, htx⟩ := exists_columnSplit_of_mem_trivialLocus X ha G ε hg x
  have htK : IsUnit (algebraMap C K S.t) := by
    rw [isUnit_iff_ne_zero]
    intro h
    exact htx (hker ▸ RingHom.mem_ker.mpr h)
  obtain ⟨eC⟩ := hfree (Localization.Away S.t)
  have h0 := S.schurMatrix_map_eq_zero (IsLocalization.Away.algebraMap_isUnit S.t)
    ((ε (Localization.Away S.t)).symm.trans
      (eC.trans (LinearEquiv.funCongrLeft _ _ (Fintype.equivFinOfCardEq hcard))))
  obtain ⟨n, hn⟩ := S.exists_pow_smul_schurMatrix_eq_zero S.t (Localization.Away S.t) h0
  have huK : IsUnit (algebraMap C K (S.t ^ n)) := by
    rw [map_pow]
    exact htK.pow n
  let m : S.α → Γ(N.obj, ⊤) := fun j =>
    ε₀.symm ⟨S.kerVector (S.t ^ n) j, S.kerVector_mem_ker hn j⟩
  obtain ⟨eK⟩ := nonempty_pullback_iso_trivial_of_mem X.hom hK
    (pullback.fst (baseMap X C) (specMap C K)) (pullback.snd (baseMap X C) (specMap C K))
    pullback.condition
  have hspan : ∀ s : Γ((Scheme.Modules.pullback
      (pullback.fst (baseMap X C) (specMap C K))).obj N.obj, ⊤),
      letI := moduleSectionsOfHom (pullback.snd (baseMap X C) (specMap C K))
        ((Scheme.Modules.pullback (pullback.fst (baseMap X C) (specMap C K))).obj N.obj) ⊤
      ∃ c : S.α → K, s = ∑ j, c j • FrameCombination.pullbackGlobalSection
        (pullback.fst (baseMap X C) (specMap C K)) (m j) := by
    intro s
    let := moduleSectionsOfHom (pullback.snd (baseMap X C) (specMap C K))
      ((Scheme.Modules.pullback (pullback.fst (baseMap X C) (specMap C K))).obj N.obj) ⊤
    obtain ⟨c, hc⟩ := S.exists_eq_sum_kerVector hn K htK huK (ε K s : K ⊗[C] G.C0) (ε K s).2
    refine ⟨c, (ε K).injective (Subtype.ext ?_)⟩
    rw [hc, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Submodule.coe_smul]
    congr 1
    have := hcompat K (m j)
    change ε K (FrameCombination.pullbackGlobalSection _ (m j)) = _ at this
    rw [this, CoherentBaseChange.TwoTermComplex.kerBaseChangeHom_apply_coe,
      LinearMap.baseChange_tmul]
    simp [m]
  obtain ⟨A, _, _, hflat, hfp, ⟨q, hq⟩, htrivA⟩ :=
    FrameCombination.exists_flat_trivialization_of_span (baseMap X C) N.obj hN m K
      ⟨(LineBundle.forget _).mapIso eK⟩ hspan
  let π := specMap C A
  have hπ : isoLocus X.hom (specOver k C) N (LineBundle.trivial _) π := by
    rw [isoLocus_trivial_iff]
    obtain ⟨e⟩ := htrivA
      ((relativeSpace X.hom).map (Over.homMk π : Over.mk (π ≫ (specOver k C).hom) ⟶ specOver k C))
      (pullback.fst _ X.hom) (relativeSpace_isPullback X.hom _).w
    exact ⟨ObjectProperty.isoMk _ e⟩
  have : Flat π := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  have : LocallyOfFinitePresentation π := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    change (algebraMap C A).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    exact hfp
  let V : (Spec (.of C)).Opens := ⟨Set.range π, π.isOpenMap.isOpen_range⟩
  refine ⟨V, ?_, ⟨q, PrimeSpectrum.ext (hq.trans hker)⟩⟩
  apply trivialLocus_isClosed X.hom _ N V.ι
  refine Scheme.fppfTopology.superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck (R := Presieve.singleton (pullback.snd π V.ι)) ?_)
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    change trivialLocus X.hom _ N (pullback.snd π V.ι ≫ V.ι)
    rw [← pullback.condition]
    exact GrothendieckTopology.le_close _ _ _
      ((isoLocus X.hom (specOver k C) N (LineBundle.trivial _)).downward_closed hπ _)
  · rw [Scheme.fppfPrecoverage, Scheme.singleton_mem_precoverage_iff]
    refine ⟨fun v => ?_, inferInstance, inferInstance⟩
    have hv : V.ι v ∈ Set.range π := by
      change V.ι v ∈ (V : Set (Spec (.of C)))
      rw [← Scheme.Opens.range_ι]
      exact ⟨v, rfl⟩
    have : v ∈ Set.range (pullback.snd π V.ι) := by
      rw [Scheme.Pullback.range_snd]
      exact hv
    exact this

/-- If the sections of all base changes of `N` are free of rank `a`, then the triviality locus
of `N` is cut out by an open immersion. -/
theorem hasImmersionLocus_of_sectionsFree [IsProper X.hom] {a : ℕ} (ha : SectionsRank X a)
    {C : Type u} [CommRing C] [IsNoetherianRing C] [Algebra k C]
    {N : LineBundle ((relativeSpace X.hom).obj (specOver k C))} (hfree : SectionsFree X N a) :
    HasImmersionLocus X.hom (specOver k C) N :=
  ⟨_, _, inferInstance, cutsOut_iSup_opens (trivialLocus_isClosed _ _ _)
    fun _ _ hg x => exists_open_of_mem_trivialLocus X ha hfree hg x⟩

end RelativePicard

end Langlands.AlgebraicGeometry.Picard

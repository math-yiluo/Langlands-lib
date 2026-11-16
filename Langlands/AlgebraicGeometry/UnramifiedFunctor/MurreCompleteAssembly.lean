import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteMono
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalReduction
import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingRepr

/-! # Assembly of Step 2a of Murre's induction

The representing scheme is glued, by Murre's Lemma 3 (`ChartGluing.murreChartGluing`), from the
representing scheme over the punctured spectrum and the closed-fibre charts `Spec B_y`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompleteLocal

open Charts LocalToGlobal

variable {R : CommRingCat.{u}} [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R] {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

/-- Step 2a, given the infinitesimal étaleness of the closed-fibre charts away from their
closed points. -/
theorem unramifiedRepresentable_of_chartEtale (hF : MurreConditions F)
    {X' : Scheme.{u}} {q' : X' ⟶ (puncturedSpectrum R).toScheme}
    (e' : (baseChange (puncturedSpectrum R).ι F).RepresentableBy (Over.mk q'))
    [LocallyOfFiniteType q'] [FormallyUnramified q']
    {Y : ℕ → Scheme.{u}} {q : ∀ k, Y k ⟶ Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (k + 1)))}
    (e : ∀ k, (baseChange (maximalIdealPowQuotientMap R k) F).RepresentableBy (Over.mk (q k)))
    [hfu : ∀ k, FormallyUnramified (q k)] [hlft : ∀ k, LocallyOfFiniteType (q k)]
    (het : ∀ (y : Y 0) (z : (chartU e y).left), z ≠ closedPoint (ChartRing e y) →
      InfinitesimallyEtaleAt F (chartElem e hF.2.2.2.2.1 y) z) :
    UnramifiedRepresentable F := by
  obtain ⟨hS, hZ, hF1b, hF2, hF3, -, -, hF6, -, -⟩ := id hF
  let j := (puncturedSpectrum R).ι
  let U : Option (Y 0) → Over (Spec R) := fun i ↦ match i with
    | none => (Over.map j).obj (Over.mk q')
    | some y => chartU e y
  let ξ : ∀ i, F.obj (op (U i)) := fun i ↦ match i with
    | none => e'.homEquiv (𝟙 _)
    | some y => chartElem e hF3 y
  have hU : ∀ i, LocallyOfFiniteType (U i).hom ∧ FormallyUnramified (U i).hom ∧
      IsMonoElement F (ξ i) ∧ ∀ z, InfinitesimallyEtaleAt F (ξ i) z := by
    rintro (_ | y)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · change LocallyOfFiniteType (q' ≫ j)
        infer_instance
      · change FormallyUnramified (q' ≫ j)
        exact MorphismProperty.comp_mem @FormallyUnramified.{u} _ _ inferInstance inferInstance
      · exact isMonoElement_map j _ (isMonoElement_of_representableBy e')
      · exact fun z ↦ infinitesimallyEtaleAt_map j _ z
          (infinitesimallyEtaleAt_of_representableBy e' z)
    · refine ⟨inferInstanceAs (LocallyOfFiniteType (chartU e y).hom),
        inferInstanceAs (FormallyUnramified (chartU e y).hom),
        chartElem_isMonoElement e hF3 y hF1b hF6, fun z ↦ ?_⟩
      by_cases hz : z = closedPoint (ChartRing e y)
      · subst hz
        exact chart_infinitesimallyEtaleAt_closedPoint e hF3 y
      · exact het y z hz
  have hcov : ∀ (K : Type u) [Field K] (f : Spec (CommRingCat.of K) ⟶ Spec R)
      (η : F.obj (op (Over.mk f))), ∃ i, ∃ h : Over.mk f ⟶ U i, F.map h.op (ξ i) = η := by
    intro K _ f η
    obtain ⟨z₀⟩ : Nonempty (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Nonempty (PrimeSpectrum K))
    have hsub : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    by_cases hs : f z₀ = closedPoint R
    · -- over the closed point: a closed-fibre chart
      obtain ⟨φ, rfl⟩ := Spec.map_surjective f
      let : Algebra R K := φ.hom.toAlgebra
      have hK : ∀ r ∈ maximalIdeal R ^ (0 + 1), algebraMap R K r = 0 := by
        intro r hr
        rw [zero_add, pow_one] at hr
        have hx := congrArg PrimeSpectrum.asIdeal hs
        change Ideal.comap φ.hom (z₀.asIdeal) = maximalIdeal R at hx
        have hz : z₀.asIdeal = ⊥ := by
          have : z₀ = ⟨⊥, Ideal.isPrime_bot⟩ := Subsingleton.elim _ _
          rw [this]
        rw [hz] at hx
        rw [← hx, Ideal.mem_comap, Ideal.mem_bot] at hr
        exact hr
      obtain ⟨y, ψ, hψ⟩ := chart_cover e hF3 hK η
      exact ⟨some y, homR ψ, hψ⟩
    · -- over the punctured spectrum
      have hrange : Set.range f ⊆ Set.range j := by
        rintro _ ⟨z, rfl⟩
        rw [Subsingleton.elim z z₀, Scheme.Opens.range_ι]
        exact hs
      obtain ⟨g', rfl⟩ : ∃ g', g' ≫ j = f := ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
      let η' : (baseChange j F).obj (op (Over.mk g')) := η
      refine ⟨none, (Over.map j).map (e'.homEquiv.symm η'), ?_⟩
      change (baseChange j F).map (e'.homEquiv.symm η').op (e'.homEquiv (𝟙 _)) = η'
      rw [← e'.homEquiv_comp, Category.comp_id, Equiv.apply_symm_apply]
  obtain ⟨Z, qZ, eZ, hlftZ, hopen, hcovZ⟩ := ChartGluing.murreChartGluing (Spec R) F hS hZ hF1b
    hF2 hF3 (Option (Y 0)) U ξ (fun i ↦ (hU i).1) (fun i ↦ (hU i).2.2.1) (fun i ↦ (hU i).2.2.2)
    hcov
  refine ⟨Z, qZ, ⟨eZ⟩, isSeparated_of_representableBy qZ hF6 eZ, hlftZ, ?_⟩
  let 𝒰 : Z.OpenCover := Scheme.Cover.mkOfCovers (Option (Y 0)) (fun i ↦ (U i).left)
    (fun i ↦ (eZ.homEquiv.symm (ξ i)).left) (fun z ↦ by
      obtain ⟨i, x, hx⟩ := hcovZ z
      exact ⟨i, x, hx⟩) hopen
  have : IsZariskiLocalAtSource @FormallyUnramified.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FormallyUnramified)
  refine IsZariskiLocalAtSource.of_openCover (P := @FormallyUnramified.{u}) 𝒰 (fun i ↦ ?_)
  have hw := Over.w (eZ.homEquiv.symm (ξ i))
  simp only [Over.mk_hom] at hw
  change FormallyUnramified ((eZ.homEquiv.symm (ξ i)).left ≫ qZ)
  rw [hw]
  exact (hU i).2.1

end CompleteLocal

end Langlands.AlgebraicGeometry.UnramifiedFunctor

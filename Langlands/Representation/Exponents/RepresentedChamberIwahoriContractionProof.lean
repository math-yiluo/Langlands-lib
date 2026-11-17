import Langlands.Representation.Exponents.RepresentedCanonicalSectionStatements
import Langlands.Representation.Exponents.SplitComponentOppositeContractionProof
import Langlands.Representation.Exponents.LeviJacquetOppositePairingStructure
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation

/-! # A chamber of Iwahori contractions for a represented parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Strict character inequalities on a finite set imply eventual membership of powers
in every positive chamber, without a lattice-image hypothesis. -/
theorem eventually_pow_characterNorm_lt {k : Type u} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A : CommGroupScheme (Spec (CommRingCat.of k)))
    {Δ : Set (characterLattice A)} (hΔ : Δ.Finite) {t : rationalPoints A.toGrp}
    (ht : ∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      ∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α (t ^ r) < ε := by
  have hev : ∀ α ∈ Δ, ∀ᶠ r in Filter.atTop,
      CocharacterUniformizer.characterNorm k A α (t ^ r) < ε := by
    intro α hα
    have hpow : ∀ r : ℕ, CocharacterUniformizer.characterNorm k A α (t ^ r) =
        CocharacterUniformizer.characterNorm k A α t ^ r := by
      intro r
      simp [CocharacterUniformizer.characterNorm, map_pow]
    simp only [hpow]
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.coe_nonneg _) (ht α hα)).eventually
      (gt_mem_nhds hε)
  exact Filter.eventually_atTop.1 ((Filter.eventually_all_finite hΔ).2 hev)

/-- Every positive chamber of the restricted complementary simple roots is nonempty. -/
theorem represented_chamber_nonempty {k : Type u} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {G P M : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {m : M ⟶ P} {a : A.toGrp ⟶ M}
    (pres : ParabolicRootPresentation p m a) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : rationalPoints A.toGrp,
      ∀ α ∈ (fun β => pres.data.f ≫ β) ''
          (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J),
        CocharacterUniformizer.characterNorm k A α t < ε := by
  obtain ⟨ζ, hζ⟩ := pres.exists_standardCocharacter
  obtain ⟨mu, hmu⟩ := pres.exists_standardCocharacter_lift hζ
  let t := CocharacterUniformizer.latticeSection k A (Multiplicative.ofAdd mu)
  have ht : ∀ α ∈ (fun β => pres.data.f ≫ β) ''
      (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J),
      CocharacterUniformizer.characterNorm k A α t < 1 := by
    rintro _ ⟨β, hβ, rfl⟩
    apply CocharacterUniformizer.characterNorm_latticeSection_lt_one
    rw [RelativeRoot.latticePairing_restrict_cocharacterMapInt, hmu]
    exact hζ.2.2 β hβ.1 hβ.2
  obtain ⟨r, hr⟩ := eventually_pow_characterNorm_lt A
    (pres.finite_simpleRoots.sdiff.image _) ht hε
  exact ⟨t ^ r, hr r le_rfl⟩

/-- Every point of a sufficiently small chamber is an Iwahori contraction for any
compact open subgroup having the stated ordered Iwahori decomposition. -/
theorem representedChamberIwahoriContraction :
    RepresentedChamberIwahoriContractionStatement.{u} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P Pbar M N Nbar p m n hp hm hn hmul pbar mbar nbar hpbar hmbar hnbar hmulbar
    hP hPP K hK hfactor A a pres Δ incG
  have := hG.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have hΔ : Δ.Finite := pres.finite_simpleRoots.sdiff.image _
  have hMN := pointImage_le_normalizer p m n hn
  have hMNbar : pointImage (m ≫ p) ≤
      Subgroup.normalizer (pointImage (nbar ≫ pbar) : Set (rationalPoints G)) := by
    rw [← hP]
    exact pointImage_le_normalizer pbar mbar nbar hnbar
  have hNc := isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup
  have hNbarc := isClosed_pointImage_comp pbar nbar hpbar.isClosedSubgroup hnbar.1.isClosedSubgroup
  let C : Set (rationalPoints G) := (K : Set (rationalPoints G)) ∩ pointImage (n ≫ p)
  let Cbar : Set (rationalPoints G) := (K : Set (rationalPoints G)) ∩ pointImage (nbar ≫ pbar)
  have hC : IsCompact C := hK.inter_right hNc
  have hCbar : IsCompact Cbar := hK.inter_right hNbarc
  have hGeo := splitComponentOppositeContraction k G hG P Pbar M N Nbar p m n hp hm hn hmul
    pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP A a pres
  obtain ⟨ε₀, hε₀, hεC⟩ := hGeo C hC Set.inter_subset_right Cbar hCbar Set.inter_subset_right
    (K : Set (rationalPoints G)) (K.isOpen.mem_nhds K.one_mem)
  let ε : ℝ := min ε₀ 1
  have hε : 0 < ε := lt_min hε₀ zero_lt_one
  have hε₁ : ε ≤ 1 := min_le_right _ _
  refine ⟨ε, hε, hε₁, represented_chamber_nonempty pres hε, ?_⟩
  intro t ht
  have ht₀ : ∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t < ε₀ :=
    fun α hα => (ht α hα).trans_le (min_le_left _ _)
  have ht₁ : ∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t < 1 :=
    fun α hα => (ht α hα).trans_le hε₁
  obtain ⟨hup, hlow⟩ := hεC t ht₀
  have hincG : incG t = rationalPoints.map (m ≫ p) (rationalPoints.map a t) := by
    simp only [incG, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  have hg : incG t ∈ pointImage (m ≫ p) := ⟨rationalPoints.map a t, hincG.symm⟩
  have hcent : ∀ x ∈ pointImage (m ≫ p), x * incG t = incG t * x := by
    intro x hx
    rw [hincG]
    exact (splitComponent_point_comm pres t x hx).symm
  refine
    { mem_levi := hg
      factor := hfactor
      upper := ?_
      levi := ?_
      lower := ?_
      exhaust := ?_
      contract := ?_ }
  · intro x hx
    exact ⟨hup x hx, (Subgroup.mem_normalizer_iff.mp (hMN hg) x).mp hx.2⟩
  · intro x hx
    have heq : (incG t)⁻¹ * x * incG t = x := by
      rw [mul_assoc, hcent x hx.2, ← mul_assoc, inv_mul_cancel, one_mul]
    simpa only [heq] using hx
  · intro x hx
    refine ⟨hlow x hx, ?_⟩
    have h := (Subgroup.mem_normalizer_iff.mp (hMNbar (Subgroup.inv_mem _ hg)) x).mp hx.2
    simpa using h
  · intro x hx
    obtain ⟨δ, hδ, hδC⟩ := hGeo {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx)
      Cbar hCbar Set.inter_subset_right
      (K : Set (rationalPoints G)) (K.isOpen.mem_nhds K.one_mem)
    obtain ⟨r, hr⟩ := eventually_pow_characterNorm_lt A hΔ ht₁ hδ
    refine ⟨r, ?_⟩
    simpa [incG] using (hδC (t ^ r) (hr r le_rfl)).1 x (Set.mem_singleton x)
  · intro L
    obtain ⟨δ, hδ, hδC⟩ := hGeo C hC Set.inter_subset_right Cbar hCbar Set.inter_subset_right
      (L : Set (rationalPoints G)) (L.isOpen.mem_nhds L.one_mem)
    obtain ⟨s, hs⟩ := eventually_pow_characterNorm_lt A hΔ ht₁ hδ
    refine ⟨s, fun l hl => ?_⟩
    simpa [incG] using (hδC (t ^ s) (hs s le_rfl)).2 l hl

end Langlands.Aubert.General.RepresentedParabolic

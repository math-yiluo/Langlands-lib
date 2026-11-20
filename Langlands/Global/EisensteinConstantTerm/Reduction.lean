import Langlands.Global.EisensteinConstantTerm.Core
import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Global.RepresentedAdelicSubgroupQuotient

/-! # The constant-term formula from absolute convergence and the geometric lemma

`Langlands.Global.eisensteinConstantTerm_of_convergence_of_unfolding` proves
`EisensteinConstantTermStatement` (Bernstein–Lapid (6.17), Mœglin–Waldspurger II.1.7) from two
named premises: the published `EisensteinAbsoluteConvergenceStatement` and
`GeometricLemmaUnfoldingStatement`; `EisensteinConstantTermReductionStatement` records this
implication as a proposition, proved by `eisensteinConstantTermReductionStatement_proof`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology
open scoped CategoryTheory.MonObj ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global.EisensteinConstantTerm

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Global.AdelicGroupPoints

section Lift

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] (Γ : Subgroup H)

/-- A compact quotient `Γ \ H` of a locally compact group has a compact set of representatives
up to `Γ`: every point is `δ v₀` with `δ ∈ Γ` and `v₀` in a fixed compact set. -/
theorem exists_isCompact_mul_mem [CompactSpace (LeftCosetSpace Γ)] :
    ∃ C : Set H, IsCompact C ∧ ∀ v : H, ∃ δ ∈ Γ, ∃ v₀ ∈ C, v = δ * v₀ := by
  classical
  choose K hK hKn using fun x : H => exists_compact_mem_nhds x
  let O : H → Set (LeftCosetSpace Γ) := fun x => LeftCosetSpace.mk Γ '' interior (K x)
  have hO : ∀ x, IsOpen (O x) := fun x =>
    (LeftCosetSpace.isOpenQuotientMap_mk Γ).isOpenMap _ isOpen_interior
  have hcover : univ ⊆ ⋃ x, O x := by
    intro z _
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ z
    exact mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hKn x), rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  refine ⟨⋃ x ∈ t, K x, t.isCompact_biUnion fun x _ => hK x, fun v => ?_⟩
  have hv := ht (mem_univ (LeftCosetSpace.mk Γ v))
  simp only [mem_iUnion] at hv
  obtain ⟨x, hx, v₀, hv₀, hmk⟩ := hv
  rw [LeftCosetSpace.mk_eq_mk_iff] at hmk
  refine ⟨v * v₀⁻¹, hmk, v₀, mem_biUnion hx (interior_subset hv₀), by group⟩

end Lift

section Twist

variable {F : Type u} [Field F] [NumberField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] [IsAffine H.X.left] (j : H ⟶ G)
  [IsClosedImmersion j.hom.hom.left]

/-- A factor that is left invariant under `H(𝔸)` comes out of the constant term along `H`. -/
theorem subgroupConstantTerm_mul_invariant (φ m : AdelicGroupPoints F G → ℂ)
    (hm : ∀ u ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j), ∀ z,
      m (u * z) = m z) (z : AdelicGroupPoints F G) :
    subgroupConstantTerm F j (fun x => φ x * m x) z = subgroupConstantTerm F j φ z * m z := by
  unfold subgroupConstantTerm
  rw [← integral_mul_const]
  congr 1
  funext x
  beta_reduce
  rw [hm _ (Quotient.out x).2 z]

end Twist

end Langlands.Global.EisensteinConstantTerm

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
open EisensteinConstantTerm

/-- **The constant-term formula** (Bernstein–Lapid Lemma 6.10 (6.17), Mœglin–Waldspurger
II.1.7), from the absolute convergence of Eisenstein series and the integration identity of the
geometric lemma. -/
theorem eisensteinConstantTerm_of_convergence_of_unfolding
    (hconv : EisensteinAbsoluteConvergenceStatement.{u})
    (hunf : GeometricLemmaUnfoldingStatement.{u}) :
    EisensteinConstantTermStatement.{u} := by
  intro F _ _ G P M U Q V A _ _ _ _ _ p _ iU l a r _ _ _ hA hT q iV _ I _ w P' U' Q' V' _ _ _
    f iU' g' iV' _ _ _ hG hU hq hV hw hP' hU' hQ' hV' hdat K hK hK' N d rho hsmooth hcalc φ
    hKmax hrho hφ
  classical
  obtain ⟨R₀, hR₀⟩ := hconv F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax
    hrho hφ
  refine ⟨R₀, fun lam hlam g => ?_⟩
  -- the twisted function `Φ = φ_λ` and its invariances
  set Φ := hK.parameterTwist φ lam with hΦdef
  have hφc : Continuous φ := hφ.2.1.1
  have hΦc : Continuous Φ := hK.continuous_parameterTwist hφc lam
  have hΦP : ∀ z ∈ rationalImage F p, ∀ x, Φ (z * x) = Φ x := by
    rintro _ ⟨y, rfl⟩ x
    have hz : map F P G p (rational F P y) ∈ parabolicQuotientSubgroup F p iU l :=
      rationalImage_le_parabolicQuotientSubgroup p iU l r.isCompatible.levi hU ⟨y, rfl⟩
    change φ (map F P G p (rational F P y) * x) *
        hK.heightPower lam (map F P G p (rational F P y) * x) = φ x * hK.heightPower lam x
    rw [hφ.1 _ hz x, hK.heightPower_rational_mul]
  have hΦU : ∀ u ∈ parabolicUnipotentImage F p iU, ∀ x, Φ (u * x) = Φ x := by
    rintro _ ⟨y, rfl⟩ x
    have hu : map F U G (iU ≫ p) y ∈ parabolicQuotientSubgroup F p iU l :=
      Subgroup.mem_sup_left ⟨y, rfl⟩
    change φ (map F U G (iU ≫ p) y * x) * hK.heightPower lam (map F U G (iU ≫ p) y * x) =
      φ x * hK.heightPower lam x
    rw [hφ.1 _ hu x, hK.heightPower_unipotent_mul hU.1.isUnipotent]
  -- compactness of `V(F) \ V(𝔸)` and normality of `V` in `Q`
  have hN : (SubgroupFunctor.range iV).IsNormal := hV.1.isNormal
  have : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
      (SubgroupFunctor.range (iV ≫ q))) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (iV ≫ q)
      hV.1.smooth hV.1.connectedSpace hV.1.isUnipotent
  -- the bound on the series of absolute values over `V(𝔸) g`
  obtain ⟨n, ⟨e⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  obtain ⟨CV, hCV, hCVrep⟩ := exists_isCompact_mul_mem
    (AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)))
  obtain ⟨b, hbsum, hb⟩ := hR₀ ((fun v : AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (iV ≫ q)) => (v : AdelicGroupPoints F G) * g) '' CV)
    (hCV.image (continuous_subtype_val.mul continuous_const)) n e {e.symm lam}
    isCompact_singleton (by
      rintro s rfl
      simpa using hlam)
  obtain ⟨-, -, v₁, hv₁, -⟩ := hCVrep 1
  have hbnn : ∀ c, 0 ≤ b c := fun c =>
    (norm_nonneg _).trans (hb c _ ⟨v₁, hv₁, rfl⟩ _ (mem_singleton _))
  have hΦPm : ∀ z ∈ (rationalSubgroup F P).map (map F P G p).toMonoidHom, ∀ x,
      ‖Φ (z * x)‖ₑ = ‖Φ x‖ₑ := by
    rw [← rationalImage_eq_map]
    intro z hz x
    rw [hΦP z hz x]
  set B₀ : ℝ≥0∞ := ENNReal.ofReal (∑' c, b c) with hB₀def
  have hS : ∀ v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)),
      ∑' c : ParabolicRationalCosets F p,
        ‖Φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) *
          ((v : AdelicGroupPoints F G) * g))‖ₑ ≤ B₀ := by
    intro v
    obtain ⟨δ, hδ, v₀, hv₀, rfl⟩ := hCVrep v
    have hδG : ((δ : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) :
        AdelicGroupPoints F G) ∈ rationalSubgroup F G :=
      rationalImage_le_rationalSubgroup _ ((mem_rationalSubgroup_range_iff _ _).mp hδ)
    have h := tsum_out_mul_left (Gr := rationalSubgroup F G)
      (P := (rationalSubgroup F P).map (map F P G p).toMonoidHom) (g := fun z => ‖Φ z‖ₑ)
      hΦPm hδG ((v₀ : AdelicGroupPoints F G) * g)
    rw [show (((δ * v₀ : AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (iV ≫ q)))) : AdelicGroupPoints F G) * g =
        ((δ : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) :
          AdelicGroupPoints F G) * ((v₀ : AdelicGroupPoints F G) * g) by simp [mul_assoc]]
    refine (le_of_eq h).trans ?_
    rw [hB₀def, ENNReal.ofReal_tsum_of_nonneg hbnn hbsum]
    refine ENNReal.tsum_le_tsum fun c => ?_
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have := hb c _ ⟨v₀, hv₀, rfl⟩ _ (mem_singleton _)
    rwa [LinearEquiv.apply_symm_apply] at this
  -- the constant-term computation, with the geometric lemma as identification
  have hcore := constantTerm_series_eq (q := q) (iV := iV) (p := p) hw
    (fun i => rationalImage F (g' i ≫ q)) (fun i => (hdat i).rationalImage_right) hN hΦc hΦP g
    B₀ ENNReal.ofReal_ne_top hS
    (fun i y => ∫ x, subgroupConstantTerm F (iU' i ≫ f i ≫ p) Φ
      ((innerAdelicPoint F G (w i))⁻¹ * ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (iV' i ≫ g' i ≫ q))) : AdelicGroupPoints F G) * y)
      ∂intertwiningMeasure F (f i ≫ p) (iU' i) (iV' i ≫ g' i ≫ q) (innerAdelicPoint F G (w i)))
    (fun i y => Integrable (fun x => subgroupConstantTerm F (iU' i ≫ f i ≫ p) Φ
      ((innerAdelicPoint F G (w i))⁻¹ * ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (iV' i ≫ g' i ≫ q))) : AdelicGroupPoints F G) * y))
      (intertwiningMeasure F (f i ≫ p) (iU' i) (iV' i ≫ g' i ≫ q) (innerAdelicPoint F G (w i))))
    (fun i y hfin => hunf F G P U Q V (P' i) (U' i) (Q' i) (V' i) p iU q iV (w i) (f i) (iU' i)
      (g' i) (iV' i) hG r.isCompatible.parabolic hU hq hV (hP' i) (hU' i) (hQ' i) (hV' i)
      (hdat i) Φ hΦc.measurable hΦU hΦP y hfin)
  -- twist matching
  have htw : ∀ i (y : AdelicGroupPoints F G),
      (hK' i).intertwiningIntegrand (iU' i) (iV' i ≫ g' i ≫ q) (w i)
        (subgroupConstantTerm F (iU' i ≫ f i ≫ p) φ) (parameterRestrict (f i) lam) y =
      fun x => subgroupConstantTerm F (iU' i ≫ f i ≫ p) Φ
        ((innerAdelicPoint F G (w i))⁻¹ * ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (iV' i ≫ g' i ≫ q))) : AdelicGroupPoints F G) * y) := by
    intro i y
    funext x
    have hm : ∀ u ∈ AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (iU' i ≫ f i ≫ p)), ∀ z,
        hK.heightPower lam (u * z) = hK.heightPower lam z := by
      intro u hu z
      obtain ⟨y', hy'⟩ : ∃ y' : AdelicGroupPoints F (U' i),
          map F (U' i) G (iU' i ≫ f i ≫ p) y' = u := hu
      subst hy'
      have := hK.heightPower_unipotent_mul (hU' i).1.isUnipotent (iU' i ≫ f i) lam y' z
      rwa [Category.assoc] at this
    simp only [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist]
    rw [hK.heightPower_restrict (f i) (hK' i) lam, hΦdef,
      show hK.parameterTwist φ lam = fun x => φ x * hK.heightPower lam x from rfl,
      subgroupConstantTerm_mul_invariant (iU' i ≫ f i ≫ p) φ _ hm]
  have hII : ∀ i (y : AdelicGroupPoints F G),
      (hK' i).intertwiningIntegral (iU' i) (iV' i ≫ g' i ≫ q) (w i)
        (subgroupConstantTerm F (iU' i ≫ f i ≫ p) φ) (parameterRestrict (f i) lam) y =
      ∫ x, subgroupConstantTerm F (iU' i ≫ f i ≫ p) Φ
        ((innerAdelicPoint F G (w i))⁻¹ * ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (iV' i ≫ g' i ≫ q))) : AdelicGroupPoints F G) * y)
        ∂intertwiningMeasure F (f i ≫ p) (iU' i) (iV' i ≫ g' i ≫ q)
          (innerAdelicPoint F G (w i)) := by
    intro i y
    unfold IsIwasawaCompact.intertwiningIntegral
    rw [htw]
  obtain ⟨h1, h2, h3⟩ := hcore
  refine ⟨fun i c => ?_, fun i => ?_, ?_⟩
  · rw [htw]
    exact h1 i c
  · simp only [hII]
    exact h2 i
  · simp only [hII]
    exact h3

/-- The constant-term formula `EisensteinConstantTermStatement` follows from the absolute
convergence of Eisenstein series (`EisensteinAbsoluteConvergenceStatement`) and the integration
identity of the geometric lemma (`GeometricLemmaUnfoldingStatement`). -/
def EisensteinConstantTermReductionStatement : Prop :=
  EisensteinAbsoluteConvergenceStatement.{u} → GeometricLemmaUnfoldingStatement.{u} →
    EisensteinConstantTermStatement.{u}

theorem eisensteinConstantTermReductionStatement_proof :
    EisensteinConstantTermReductionStatement.{u} :=
  eisensteinConstantTerm_of_convergence_of_unfolding

end Langlands.Global

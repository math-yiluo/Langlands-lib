import Langlands.Global.AdelicIntertwiningCenterIdealReductionStatement
import Langlands.Global.AdelicIntertwiningLeviRestriction
import Langlands.Global.AdelicIntertwiningLeftInvariance
import Langlands.Global.InfiniteAdelicIntegrationByParts
import Langlands.Global.InfiniteAdelicRestrictionSmooth
import Langlands.Global.ReductiveInfiniteAdelicManifold
import Langlands.Automorphic.GroupSchemeActualDifferential
import Langlands.Global.AdelicIntertwiningConvergenceProof

/-! # A center ideal common to all regular intertwining integrals, from the Levi transfer

This module proves `IntertwiningUniformCenterIdealReductionStatement`: the normalized
Harish-Chandra transfer of `LeviRestrictionCenterTransferStatement` and the Haar factor of
`IntertwiningStabilizerModulusStatement` imply `IntertwiningUniformCenterIdealStatement`, with the
annihilator ideal of the inducing function and the threshold of the absolute convergence theorem.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]

local notation "Ainf" => CommAlgCat.of F (InfiniteAdeleRing F)

theorem pair_affinePointsTarget_mul {G H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [IsAffine H.X.left] (j : H ⟶ G) (m : InfiniteAdelicGroupPoints F H)
    (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G) :
    pair F G (H.affinePointsTarget j Ainf m * a) b =
      map F H G j (ofInfinite F H m) * pair F G a b := by
  rw [map_ofInfinite, ofInfinite_eq_pair, pair_mul, one_mul]

theorem ofInfinite_mul_eq_pair {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    (x : InfiniteAdelicGroupPoints F G) (h : AdelicGroupPoints F G) :
    ofInfinite F G x * h = pair F G (x * infinite F G h) (finite F G h) := by
  conv_lhs => rw [← pair_projections F G h]
  rw [ofInfinite_eq_pair, pair_mul, one_mul]

theorem parameterPower_at_one {H : GroupScheme (Spec (CommRingCat.of F))}
    (lam : ComplexCharacterParameter F H) : parameterPower F H lam 1 = 1 := by
  simp [parameterPower, characterLog_one]

variable {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
  [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left]
  {iU : U ⟶ P} {l : M ⟶ P} {iV : V ⟶ Q} {l' : M' ⟶ Q}
  [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M} {π' : Q ⟶ M'}
  {K : Subgroup (AdelicGroupPoints F G)}

local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))

/-- Given an element `y` of the enveloping algebra of `M'(F_∞)` that realizes a central `z` on the
normalized Levi restrictions for both parabolics, `z` annihilates every plot-smooth infinite slice
of `M(w, λ)φ` as soon as it annihilates the slices of `φ` and the intertwining integrand is
locally uniformly dominated. -/
theorem IsIwasawaCompact.centerAction_intertwiningOperator_eq_zero
    (hK : IsIwasawaCompact p K) (hK' : IsIwasawaCompact q K)
    (hC : IntertwiningStabilizerModulusStatement.{u})
    (hG : IsConnectedReductive G) (hp : IsParabolicSubgroup p)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hl : IsRationalLeviSubgroup l)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hl' : IsRationalLeviSubgroup l') (hw : IsWeylConjugation p l q l' w c)
    (hπ : l' ≫ π' = 𝟙 M') {d d' : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (hsmooth' : SmoothOfRelativeDimension d' M'.X.hom)
    (hcalc' : AdelicDifferentialCommutator F M' hsmooth')
    {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ)
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hφs : ∀ b, functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G)
    (z : AdelicEnvelopingCenter F G hsmooth)
    (hz : ∀ b (h : functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G),
      plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G φ b, h⟩ = 0)
    (y : AdelicEnvelopingAlgebra F M' hsmooth')
    (hy1 : ∀ (f : InfiniteAdelicGroupPoints F G → ℂ) (hf : f ∈ InfinitePlotSmoothFunctions F G),
      (∀ (v : InfiniteAdelicGroupPoints F V) (x : InfiniteAdelicGroupPoints F G),
        f (V.affinePointsTarget (iV ≫ q) Ainf v * x) = f x) →
      ∀ (g : InfiniteAdelicGroupPoints F G)
        (h : (fun m => parameterPower F Q (-halfModulusParameter F Q)
            (map F M' Q l' (ofInfinite F M' m)) * f (M'.affinePointsTarget (l' ≫ q) Ainf m * g)) ∈
          InfinitePlotSmoothFunctions F M'),
        ((plotSmoothEnvelopingAction F M' hsmooth' hcalc' y) ⟨_, h⟩ :
            InfiniteAdelicGroupPoints F M' → ℂ) =
          fun m => parameterPower F Q (-halfModulusParameter F Q)
            (map F M' Q l' (ofInfinite F M' m)) *
            (plotSmoothCenterAction F G hsmooth hcalc z ⟨f, hf⟩ :
              InfiniteAdelicGroupPoints F G → ℂ) (M'.affinePointsTarget (l' ≫ q) Ainf m * g))
    (hy2 : ∀ (f : InfiniteAdelicGroupPoints F G → ℂ) (hf : f ∈ InfinitePlotSmoothFunctions F G),
      (∀ (u : InfiniteAdelicGroupPoints F U) (x : InfiniteAdelicGroupPoints F G),
        f (U.affinePointsTarget (iU ≫ p) Ainf u * x) = f x) →
      ∀ (g : InfiniteAdelicGroupPoints F G)
        (h : (fun m => parameterPower F P (-halfModulusParameter F P)
            (map F M' P (c ≫ l) (ofInfinite F M' m)) *
            f (M'.affinePointsTarget (c ≫ l ≫ p) Ainf m * g)) ∈ InfinitePlotSmoothFunctions F M'),
        ((plotSmoothEnvelopingAction F M' hsmooth' hcalc' y) ⟨_, h⟩ :
            InfiniteAdelicGroupPoints F M' → ℂ) =
          fun m => parameterPower F P (-halfModulusParameter F P)
            (map F M' P (c ≫ l) (ofInfinite F M' m)) *
            (plotSmoothCenterAction F G hsmooth hcalc z ⟨f, hf⟩ :
              InfiniteAdelicGroupPoints F G → ℂ) (M'.affinePointsTarget (c ≫ l ≫ p) Ainf m * g))
    (lam : ComplexCharacterParameter F P)
    (hdom : ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∃ bd : LeftCosetSpace (intertwiningRationalSubgroup F p iU (iV ≫ q)
          (innerAdelicPoint F G w)) → ℝ,
        Integrable bd (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)) ∧
        ∀ r, ∀ g ∈ C, ‖hK.intertwiningIntegrand iU (iV ≫ q) w φ lam g r‖ ≤ bd r)
    (b : FiniteAdelicGroupPoints F G)
    (h : functionInfiniteSlice F G (hK.intertwiningOperator hK' iU l iV c π' w φ lam) b ∈
      InfinitePlotSmoothFunctions F G) :
    plotSmoothCenterAction F G hsmooth hcalc z
      ⟨functionInfiniteSlice F G (hK.intertwiningOperator hK' iU l iV c π' w φ lam) b, h⟩ = 0 := by
  have hUrad : IsUnipotentRadical iU := hU.1
  have hφU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx g => hφ x (Subgroup.mem_sup_left hx) g
  have : IsClosedImmersion iU.hom.hom.left := hUrad.isClosedSubgroup
  have : IsAffine U.X.left := isAffine_of_isAffineHom iU.hom.hom.left
  set T := hK.intertwiningOperator hK' iU l iV c π' w φ lam with hTdef
  apply Subtype.ext
  funext a
  -- smoothness of the target Levi restriction of the slice
  have hδQ := parameterPower_map_ofInfinite_mem_infinitePlotSmoothFunctions (G := M') (H := Q) l'
    (-halfModulusParameter F Q)
  have hcompQ : (fun m => functionInfiniteSlice F G T b (M'.affinePointsTarget (l' ≫ q) Ainf m * a))
      ∈ InfinitePlotSmoothFunctions F M' := by
    have := comp_affinePointsTarget_mem_infinitePlotSmoothFunctions (l' ≫ q) 1 a h
    simpa only [one_mul] using this
  have hΨ := mul_mem_infinitePlotSmoothFunctions hδQ hcompQ
  have hVinv : ∀ (v : InfiniteAdelicGroupPoints F V) (x : InfiniteAdelicGroupPoints F G),
      functionInfiniteSlice F G T b (V.affinePointsTarget (iV ≫ q) Ainf v * x) =
        functionInfiniteSlice F G T b x := by
    intro v x
    change T (pair F G (V.affinePointsTarget (iV ≫ q) Ainf v * x) b) = T (pair F G x b)
    rw [pair_affinePointsTarget_mul, hTdef]
    exact IsIwasawaCompact.intertwiningOperator_leftInvariant (iU := iU) (iV := iV) (π' := π')
      (hK := hK) (hK' := hK') (hU := hU) (hV := hV) (hφ := hφ) (lam := lam) (hw := hw) (hl := hl)
      _ (Subgroup.mem_sup_left ⟨ofInfinite F V v, rfl⟩) _
  have hA1 := hy1 (functionInfiniteSlice F G T b) h hVinv a hΨ
  have hval := congrFun hA1 1
  simp only [map_one, parameterPower_at_one, one_mul] at hval
  change (plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G T b, h⟩ :
    InfiniteAdelicGroupPoints F G → ℂ) a = 0
  rw [← hval]
  -- the right Haar measure on `M'(F_∞)`
  let ν : Measure (InfiniteAdelicGroupPoints F M') :=
    (Measure.haar : Measure (InfiniteAdelicGroupPoints F M')).inv
  have : ν.IsMulRightInvariant := by dsimp only [ν]; infer_instance
  have : IsFiniteMeasureOnCompacts ν := by dsimp only [ν]; infer_instance
  have : ν.IsOpenPosMeasure := by dsimp only [ν]; infer_instance
  have : SFinite ν := by dsimp only [ν, Measure.inv]; infer_instance
  suffices hzero : ((plotSmoothEnvelopingAction F M' hsmooth' hcalc' y) ⟨_, hΨ⟩ :
      InfiniteAdelicGroupPoints F M' → ℂ) = 0 by
    rw [hzero]
    rfl
  refine eq_zero_of_forall_integral_compactPlotSmooth F M' hsmooth' ν
    (continuous_of_mem_infinitePlotSmoothFunctions hsmooth'
      ((plotSmoothEnvelopingAction F M' hsmooth' hcalc' y) ⟨_, hΨ⟩).property) ?_
  intro ψ
  obtain ⟨T₀, hT₀⟩ := exists_envelopingAction_transpose F M' hsmooth' hcalc' ν y
  rw [hT₀ ⟨_, hΨ⟩ ψ]
  set ϑ : InfiniteAdelicGroupPoints F M' → ℂ :=
    (((T₀ ψ : compactPlotSmoothFunctions F M') : InfinitePlotSmoothFunctions F M') :
      InfiniteAdelicGroupPoints F M' → ℂ) with hϑdef
  have hϑc : Continuous ϑ :=
    continuous_of_mem_infinitePlotSmoothFunctions hsmooth' (T₀ ψ).val.property
  have hϑs : HasCompactSupport ϑ := (T₀ ψ).property
  have hδP := parameterPower_map_ofInfinite_mem_infinitePlotSmoothFunctions (G := M') (H := P)
    (c ≫ l) (-halfModulusParameter F P)
  have hδPc := continuous_of_mem_infinitePlotSmoothFunctions hsmooth' hδP
  -- the restriction formula at every Levi point
  have hrest : ∀ m, parameterPower F Q (-halfModulusParameter F Q)
      (map F M' Q l' (ofInfinite F M' m)) *
      functionInfiniteSlice F G T b (M'.affinePointsTarget (l' ≫ q) Ainf m * a) =
      parameterPower F P (-halfModulusParameter F P) (map F M' P (c ≫ l) (ofInfinite F M' m)) *
        hK'.heightPower (-weylParameter l c π' lam) (pair F G a b) *
        ∫ r : LeftCosetSpace (intertwiningRationalSubgroup F p iU (iV ≫ q)
            (innerAdelicPoint F G w)), φ (map F P G p (map F M' P (c ≫ l) (ofInfinite F M' m)) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * pair F G a b)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * pair F G a b)
          ∂intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w) := by
    intro m
    change _ * T (pair F G (M'.affinePointsTarget (l' ≫ q) Ainf m * a) b) = _
    rw [pair_affinePointsTarget_mul, map_comp_eq_map_map l' q, hTdef]
    exact hK.intertwiningOperator_levi_mul hK' hC hG hp hU hl hq hV hl' hw hπ hφc hφU lam
      (ofInfinite F M' m) (pair F G a b)
  have : SFinite (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV ≫ q))) := by
    have hclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)
    have : LocallyCompactSpace Vₐ := hclosed.locallyCompactSpace
    have : PolishSpace Vₐ := hclosed.polishSpace
    unfold AdelicSubgroupPoints.normalizedHaarMeasure
    infer_instance
  have : SFinite (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)) := by
    unfold intertwiningMeasure LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
    infer_instance
  -- the dominating function on the translated support
  have hsuppc : HasCompactSupport (fun m => ϑ m * parameterPower F P (-halfModulusParameter F P)
      (map F M' P (c ≫ l) (ofInfinite F M' m))) := hϑs.mul_right
  have hCc : IsCompact ((fun m => map F Q G q (map F M' Q l' (ofInfinite F M' m)) * pair F G a b) ''
      tsupport (fun m => ϑ m * parameterPower F P (-halfModulusParameter F P)
        (map F M' P (c ≫ l) (ofInfinite F M' m)))) :=
    hsuppc.isCompact.image (((map F Q G q).continuous.comp ((map F M' Q l').continuous.comp
      (ofInfinite F M').continuous)).mul continuous_const)
  obtain ⟨bd, hbd, hbd2⟩ := hdom _ hCc
  have hint := hK.integrable_leviIntegrand_prod hC hG hp hU hl hq hV hl' hw hφc hφU lam
    (pair F G a b) ν (hϑc.mul hδPc) hsuppc hbd (fun m hm r => hbd2 r _ ⟨m, hm, rfl⟩)
  -- vanishing on every fibre
  have hfiber : ∀ r : LeftCosetSpace (intertwiningRationalSubgroup F p iU (iV ≫ q)
      (innerAdelicPoint F G w)),
      ∫ m, (ϑ m * parameterPower F P (-halfModulusParameter F P)
          (map F M' P (c ≫ l) (ofInfinite F M' m))) * (φ (map F P G p (map F M' P (c ≫ l) (ofInfinite F M' m)) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * pair F G a b)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * pair F G a b)) ∂ν = 0 := by
    intro r
    set hr := (innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * pair F G a b with hhr
    have hUinv : ∀ (u : InfiniteAdelicGroupPoints F U) (x : InfiniteAdelicGroupPoints F G),
        functionInfiniteSlice F G φ (finite F G hr) (U.affinePointsTarget (iU ≫ p) Ainf u * x) =
          functionInfiniteSlice F G φ (finite F G hr) x := by
      intro u x
      change φ (pair F G (U.affinePointsTarget (iU ≫ p) Ainf u * x) (finite F G hr)) =
        φ (pair F G x (finite F G hr))
      rw [pair_affinePointsTarget_mul]
      exact hφU _ ⟨ofInfinite F U u, rfl⟩ _
    have hcompP : (fun m => functionInfiniteSlice F G φ (finite F G hr)
        (M'.affinePointsTarget (c ≫ l ≫ p) Ainf m * infinite F G hr)) ∈
          InfinitePlotSmoothFunctions F M' := by
      have := comp_affinePointsTarget_mem_infinitePlotSmoothFunctions (c ≫ l ≫ p) 1
        (infinite F G hr) (hφs (finite F G hr))
      simpa only [one_mul] using this
    have hΦ := mul_mem_infinitePlotSmoothFunctions hδP hcompP
    have hA2 := hy2 _ (hφs (finite F G hr)) hUinv (infinite F G hr) hΦ
    rw [hz (finite F G hr) (hφs (finite F G hr))] at hA2
    have hyzero : ∀ m, ((plotSmoothEnvelopingAction F M' hsmooth' hcalc' y) ⟨_, hΦ⟩ :
        InfiniteAdelicGroupPoints F M' → ℂ) m = 0 := by
      intro m
      rw [hA2]
      simp
    have hT := hT₀ ⟨_, hΦ⟩ ψ
    have hΦzero : ∫ m, (parameterPower F P (-halfModulusParameter F P)
          (map F M' P (c ≫ l) (ofInfinite F M' m)) *
          functionInfiniteSlice F G φ (finite F G hr)
            (M'.affinePointsTarget (c ≫ l ≫ p) Ainf m * infinite F G hr)) * ϑ m ∂ν = 0 :=
      hT.symm.trans (integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => by
        simp only [Pi.zero_apply]
        rw [hyzero x, zero_mul]))
    have hF : ∀ m, (ϑ m * parameterPower F P (-halfModulusParameter F P)
          (map F M' P (c ≫ l) (ofInfinite F M' m))) *
          (φ (map F P G p (map F M' P (c ≫ l) (ofInfinite F M' m)) * hr) *
            hK.heightPower lam hr) =
        hK.heightPower lam hr * ((parameterPower F P (-halfModulusParameter F P)
          (map F M' P (c ≫ l) (ofInfinite F M' m)) *
          functionInfiniteSlice F G φ (finite F G hr)
            (M'.affinePointsTarget (c ≫ l ≫ p) Ainf m * infinite F G hr)) * ϑ m) := by
      intro m
      have hB : map F P G p (map F M' P (c ≫ l) (ofInfinite F M' m)) =
          ofInfinite F G (M'.affinePointsTarget (c ≫ l ≫ p) Ainf m) := by
        rw [← map_comp_eq_map_map, map_ofInfinite, Category.assoc]
      rw [hB, ofInfinite_mul_eq_pair]
      change _ * (functionInfiniteSlice F G φ (finite F G hr)
        (M'.affinePointsTarget (c ≫ l ≫ p) Ainf m * infinite F G hr) * _) = _
      ring
    simp_rw [hF]
    rw [integral_const_mul, hΦzero, mul_zero]
  calc (∫ m, (parameterPower F Q (-halfModulusParameter F Q)
          (map F M' Q l' (ofInfinite F M' m)) *
          functionInfiniteSlice F G T b (M'.affinePointsTarget (l' ≫ q) Ainf m * a)) * ϑ m ∂ν)
      = ∫ m, hK'.heightPower (-weylParameter l c π' lam) (pair F G a b) *
          ∫ r : LeftCosetSpace (intertwiningRationalSubgroup F p iU (iV ≫ q)
            (innerAdelicPoint F G w)), (ϑ m * parameterPower F P (-halfModulusParameter F P)
              (map F M' P (c ≫ l) (ofInfinite F M' m))) * (φ (map F P G p (map F M' P (c ≫ l) (ofInfinite F M' m)) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * pair F G a b)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * pair F G a b))
            ∂intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w) ∂ν := by
        congr 1
        funext m
        rw [hrest m, integral_const_mul]
        ring
    _ = hK'.heightPower (-weylParameter l c π' lam) (pair F G a b) *
          ∫ r : LeftCosetSpace (intertwiningRationalSubgroup F p iU (iV ≫ q)
            (innerAdelicPoint F G w)), ∫ m, (ϑ m * parameterPower F P (-halfModulusParameter F P)
              (map F M' P (c ≫ l) (ofInfinite F M' m))) * (φ (map F P G p (map F M' P (c ≫ l) (ofInfinite F M' m)) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * pair F G a b)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * pair F G a b)) ∂ν
            ∂intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w) := by
        rw [integral_const_mul, integral_integral_swap (f := fun m r =>
          (ϑ m * parameterPower F P (-halfModulusParameter F P)
            (map F M' P (c ≫ l) (ofInfinite F M' m))) * (φ (map F P G p (map F M' P (c ≫ l) (ofInfinite F M' m)) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * pair F G a b)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * pair F G a b))) hint]
    _ = 0 := by
        simp_rw [hfiber]
        simp

/-- `LeviRestrictionCenterTransferStatement` and `IntertwiningStabilizerModulusStatement` imply
`IntertwiningUniformCenterIdealStatement`: the annihilator ideal of `φ` in the center annihilates
every plot-smooth infinite slice of `M(w, λ)φ` above the threshold of the absolute convergence
theorem. -/
theorem intertwiningUniformCenterIdealReduction :
    IntertwiningUniformCenterIdealReductionStatement.{u} := by
  intro hA hC F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hAs hT q _ iV l' _ π' w c
    hG hU hq hV hl' hmul hπ hw K hK hK' N d rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨R, hR⟩ := intertwiningAbsoluteConvergence F G P M U Q M' V A p iU l a r hAs hT q iV l'
    w c hG hU hq hV hl' hmul hw K hK rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨hleft, hsm, -, ⟨J, hJfin, hJ⟩, -⟩ := hφ
  refine ⟨R, J, hJfin, ?_⟩
  intro lam hlam z hz b h
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : LocallyOfFiniteType Q.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := q) ‹IsClosedImmersion q.hom.hom.left›
  have : LocallyOfFiniteType V.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := iV ≫ q) ‹IsClosedImmersion (iV ≫ q).hom.hom.left›
  have : IsAffineHom V.X.hom := isAffineHom_of_isAffine _
  have hM' : IsConnectedReductive M' := hl'.isConnectedReductive
  have : IsAffine M'.X.left := hM'.affineScheme
  have : Smooth M'.X.hom := hM'.smooth
  obtain ⟨d', hsmooth'⟩ := hM'.exists_smoothOfRelativeDimension
  have hcalc' := adelicDifferentialCommutator_of_smooth F M' hsmooth'
  have hp := r.isCompatible.parabolic
  have hl := r.isCompatible.levi
  obtain ⟨y, hy1, hy2⟩ := hA F G P M U Q M' V p iU l q iV l' w c hG hp hU hl hq hV hl' hw
    hsmooth hcalc hsmooth' hcalc' z
  have hdom : ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∃ bd : LeftCosetSpace (intertwiningRationalSubgroup F p iU (iV ≫ q)
          (innerAdelicPoint F G w)) → ℝ,
        Integrable bd (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)) ∧
        ∀ r, ∀ g ∈ C, ‖hK.intertwiningIntegrand iU (iV ≫ q) w φ lam g r‖ ≤ bd r := by
    intro C hCc
    obtain ⟨n, ⟨e⟩⟩ := exists_complexParameterEquiv hG hp
    have hsingle : ∀ s ∈ ({e.symm lam} : Set (Fin n → ℂ)), r.IsRegularParameter hAs hT R (e s) := by
      intro s hs
      rw [Set.mem_singleton_iff.mp hs, e.apply_symm_apply]
      exact hlam
    obtain ⟨bd, hbd, hbound⟩ := hR C hCc n e {e.symm lam} isCompact_singleton hsingle
    exact ⟨bd, hbd, fun x g hg => by
      simpa only [e.apply_symm_apply] using hbound x g hg (e.symm lam) (Set.mem_singleton _)⟩
  exact IsIwasawaCompact.centerAction_intertwiningOperator_eq_zero hK hK' hC hG hp hU hl hq hV hl' hw hπ hsmooth
    hcalc hsmooth' hcalc' hsm.1 hleft hsm.2.1 z (hJ z hz) y hy1 hy2 lam hdom b h

end Langlands.Global

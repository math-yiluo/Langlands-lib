import Langlands.Global.AdelicIntertwiningConvergenceStatement
import Langlands.Global.AdelicIntertwiningRadicalIntersection
import Langlands.Global.LeftCosetImageMajorant
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof

/-! # Absolute convergence of intertwining integrals from that of Eisenstein series

Mœglin–Waldspurger II.1.6 (i): the integrand `v ↦ φ_λ(w⁻¹ v g)` on
`(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)` is dominated by an integrable function as soon as the terms of the
Eisenstein series `E(·, φ, λ)` are dominated by a summable family uniformly on compact sets.
Write `V(𝔸) = V(F) Ω` with `Ω` compact. For `v = δ ω` the value `φ_λ(w⁻¹ δ · ω g)` is the
Eisenstein term at the coset `P(F) w⁻¹ δ` and the point `ω g` of the compact set `Ω C`, and
`δ ↦ P(F) w⁻¹ δ` is injective on `(V(F) ∩ wU(𝔸)w⁻¹) \ V(F)` because `w⁻¹ V w ∩ P ⊆ U`. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Opposite NumberField MeasureTheory Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open scoped CategoryTheory.MonObj ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global

namespace AdelicGroupPoints

section Rational

variable {F : Type u} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P}

/-- The rational points of `P` lie in `U(𝔸) M(F)`, for a rational Levi `l` and the geometric
unipotent radical `iU`: a rational point is `m u` with `m ∈ M(F)`, `u ∈ U(F)`. -/
theorem map_rational_mem_parabolicQuotientSubgroup_of_levi (hl : IsRationalLeviSubgroup l)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (x : RationalGroupPoints F P) :
    map F P G p (rational F P x) ∈ parabolicQuotientSubgroup F p iU l := by
  obtain ⟨U', j, hj, hmul⟩ := hl.exists_unipotentRadical
  let := hmul
  let T := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))
  let z : T ⟶ M.X ⊗ U'.X := x ≫ inv (subgroupMultiplication l j)
  let m : RationalGroupPoints F M := z ≫ fst M.X U'.X
  have hn : (z ≫ snd M.X U'.X) ≫ j.hom.hom ∈ (SubgroupFunctor.range iU).carrier T :=
    hU.1.greatest U' j hj.1.isClosedSubgroup hj.1.smooth hj.1.connectedSpace
      hj.1.isUnipotent hj.1.isNormal T ⟨z ≫ snd M.X U'.X, rfl⟩
  obtain ⟨n, hn⟩ := hn
  change RationalGroupPoints F U at n
  change n ≫ iU.hom.hom = (z ≫ snd M.X U'.X) ≫ j.hom.hom at hn
  have hz : lift (z ≫ fst M.X U'.X) (z ≫ snd M.X U'.X) = z := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hx : M.affinePointsTarget l (CommAlgCat.of F F) m *
      U.affinePointsTarget iU (CommAlgCat.of F F) n = x := by
    change (m ≫ l.hom.hom) * (n ≫ iU.hom.hom) = x
    have hcomp := comp_subgroupMultiplication l j (z ≫ fst M.X U'.X) (z ≫ snd M.X U'.X)
    rw [hz] at hcomp
    rw [hn, ← hcomp]
    simp [z]
  have hr (H : GroupScheme (Spec (CommRingCat.of F))) (f : H ⟶ P)
      (y : RationalGroupPoints F H) :
      map F P G p (rational F P (H.affinePointsTarget f (CommAlgCat.of F F) y)) =
        map F H G (f ≫ p) (rational F H y) := by
    rw [map_comp_apply_of_hom]
    exact congrArg (map F P G p) (DFunLike.congr_fun (rational_naturality F H f) y)
  rw [← hx, map_mul, map_mul, hr M l m, hr U iU n]
  exact mul_mem (Subgroup.mem_sup_right ⟨m, rfl⟩)
    (Subgroup.mem_sup_left ⟨rational F U n, rfl⟩)

variable [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} {φ : AdelicGroupPoints F G → ℂ}

/-- The twist `φ_λ` is invariant under left translation by rational points of `P`, for `φ`
left invariant under `U(𝔸) M(F)`. -/
theorem IsIwasawaCompact.parameterTwist_map_rational_mul (hK : IsIwasawaCompact p K)
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hl : IsRationalLeviSubgroup l) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (lam : ComplexCharacterParameter F P) (x : RationalGroupPoints F P)
    (g : AdelicGroupPoints F G) :
    hK.parameterTwist φ lam (map F P G p (rational F P x) * g) =
      hK.parameterTwist φ lam g := by
  rw [IsIwasawaCompact.parameterTwist, IsIwasawaCompact.parameterTwist,
    hφ _ (map_rational_mem_parabolicQuotientSubgroup_of_levi hl hU x) g,
    IsIwasawaCompact.heightPower, IsIwasawaCompact.heightPower, hK.height_rational_mul]

/-- The Eisenstein term at the coset `P(F) ρ₀` is `φ_λ(ρ₀ g)` for every representative `ρ₀`. -/
theorem IsIwasawaCompact.eisensteinTerm_mk (hK : IsIwasawaCompact p K)
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hl : IsRationalLeviSubgroup l) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G)
    (ρ₀ : rationalSubgroup F G) :
    hK.eisensteinTerm φ lam g (Quotient.mk _ ρ₀) = hK.parameterTwist φ lam (ρ₀.val * g) := by
  have hrel := QuotientGroup.rightRel_apply.mp (Quotient.exact
    (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel (parabolicRationalSubgroup F p)) ρ₀)))
  rw [parabolicRationalSubgroup, Subgroup.mem_subgroupOf] at hrel
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hrel
  change map F P G p (rational F P x) = (ρ₀ : AdelicGroupPoints F G) *
    ((Quotient.out (Quotient.mk (QuotientGroup.rightRel (parabolicRationalSubgroup F p)) ρ₀) :
      rationalSubgroup F G) : AdelicGroupPoints F G)⁻¹ at hx
  have hmul : (ρ₀ : AdelicGroupPoints F G) * g = map F P G p (rational F P x) *
      (((Quotient.out (Quotient.mk (QuotientGroup.rightRel (parabolicRationalSubgroup F p)) ρ₀) :
        rationalSubgroup F G) : AdelicGroupPoints F G) * g) := by
    rw [hx]; group
  rw [hmul, hK.parameterTwist_map_rational_mul hφ hl hU]
  rfl

end Rational

section RationalCoset

variable (F : Type u) [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} {S : SubgroupFunctor G}

/-- For a rational point `w` of `G` and a rational point `δ` of a subgroup functor `S` of `G`,
the product `w⁻¹ δ` is a rational point of `G`. -/
theorem inv_innerAdelicPoint_mul_mem_rationalSubgroup
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (δ : AdelicSubgroupPoints.rationalSubgroup F G S) :
    (innerAdelicPoint F G w)⁻¹ *
        ((δ : AdelicSubgroupPoints.adelicPoints F G S) : AdelicGroupPoints F G) ∈
      AdelicGroupPoints.rationalSubgroup F G := by
  obtain ⟨δ, ⟨y, rfl⟩⟩ := δ
  exact mul_mem (inv_mem ⟨_, (innerAdelicPoint_eq_rational F G w).symm⟩) ⟨y.val, rfl⟩

variable [IsAffine G.X.left] [IsAffine P.X.left] (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]

/-- The coset `P(F) w⁻¹ δ ∈ P(F) \ G(F)` of a rational point `δ` of a subgroup functor `S`
of `G`, for a rational point `w` of `G`. For `S` the image of `V` this is the map
`δ ↦ P(F) w⁻¹ δ` of Mœglin–Waldspurger II.1.6 (i), whose fibres are cosets of
`V(F) ∩ wU(𝔸)w⁻¹`. -/
def intertwiningRationalCoset (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (δ : AdelicSubgroupPoints.rationalSubgroup F G S) : ParabolicRationalCosets F p :=
  Quotient.mk _ ⟨_, inv_innerAdelicPoint_mul_mem_rationalSubgroup F w δ⟩

end RationalCoset

section Intertwining

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- If `δ, δ' ∈ V(F)` and `(w⁻¹ δ') (w⁻¹ δ)⁻¹ ∈ P(𝔸)`, then `δ' δ⁻¹ ∈ V(F) ∩ wU(𝔸)w⁻¹`. -/
theorem mul_inv_mem_intertwiningRationalSubgroup
    {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (r : ParabolicRootPresentation p l a) {q : Q ⟶ G} {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) {c : M' ⟶ M}
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hmul : IsIso (subgroupMultiplication l' iV)) (hw : IsWeylConjugation p l q l' w c)
    {δ δ' : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))}
    (hδ : δ ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)))
    (hδ' : δ' ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)))
    (h : ((innerAdelicPoint F G w)⁻¹ * (δ' : AdelicGroupPoints F G)) *
        ((innerAdelicPoint F G w)⁻¹ * (δ : AdelicGroupPoints F G))⁻¹ ∈
      (map F P G p).toMonoidHom.range) :
    δ' * δ⁻¹ ∈ intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w) := by
  rw [mem_intertwiningRationalSubgroup_iff]
  refine ⟨mul_mem hδ' (inv_mem hδ), ?_⟩
  have e : (innerAdelicPoint F G w)⁻¹ * ((δ' * δ⁻¹ :
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) :
        AdelicGroupPoints F G) * innerAdelicPoint F G w =
      ((innerAdelicPoint F G w)⁻¹ * (δ' : AdelicGroupPoints F G)) *
        ((innerAdelicPoint F G w)⁻¹ * (δ : AdelicGroupPoints F G))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  exact conj_mem_parabolicUnipotentImage r w hG hU hq hV hmul hw (δ' * δ⁻¹).2 (e ▸ h)

end Intertwining

end AdelicGroupPoints

namespace AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F]
  {G V : GroupScheme (Spec (CommRingCat.of F))}

/-- For a smooth connected unipotent `V` and `j : V → G`, a compact subset `Ω` of the image of
`V(𝔸)` in `G(𝔸)` meets every coset of the image of `V(F)`. -/
theorem exists_isCompact_rational_mul_mem_range [IsAffine V.X.left] (j : V ⟶ G)
    (hs : Smooth V.X.hom) (hc : ConnectedSpace V.X.left) (hu : IsUnipotent V) :
    ∃ Ω : Set (adelicPoints F G (SubgroupFunctor.range j)), IsCompact Ω ∧
      ∀ v, ∃ ρ₀ ∈ rationalSubgroup F G (SubgroupFunctor.range j), ρ₀ * v ∈ Ω := by
  obtain ⟨C, hC, hcov⟩ := AdelicGroupPoints.exists_isCompact_rational_mul_mem_of_split
    perfectFieldUnipotentSplit splitUnipotentAffineTorsorStatement F V hs hc hu
  refine ⟨adelicRangeMap F j '' C, hC.image (continuous_adelicRangeMap F j), fun v => ?_⟩
  obtain ⟨x, rfl⟩ := adelicRangeMap_surjective F j v
  obtain ⟨y, ⟨y₀, rfl⟩, hy⟩ := hcov x
  refine ⟨adelicRangeMap F j (AdelicGroupPoints.rational F V y₀), ?_, ⟨_, hy, map_mul _ _ _⟩⟩
  rw [adelicRangeMap_rational]
  exact ⟨_, rfl⟩

end AdelicSubgroupPoints

open AdelicGroupPoints

/-- **Reduction of MW II.1.6 (i) to MW II.1.5.** Absolute convergence of adelic Eisenstein
series, in the form of a summable majorant of its terms uniform on compact sets of `g` and `λ`,
implies the integrable domination of the intertwining integrand. The same `R` works. -/
theorem intertwiningAbsoluteConvergence_of_eisenstein
    (hE : EisensteinAbsoluteConvergenceStatement.{u}) :
    IntertwiningAbsoluteConvergenceStatement.{u} := by
  intro F _ _ G P M U Q M' V A _ _ _ _ _ p _ iU l a r _ _ _ hA hT q iV l' _ w c hG hU hq hV _
    hmul hw K hK N d rho hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨R, hR⟩ := hE F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ
  refine ⟨R, fun C hC n e Λ hΛ hreg => ?_⟩
  have hclosed : IsClosed (AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (iV ≫ q)) : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)
  have : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (iV ≫ q))) := hclosed.locallyCompactSpace
  obtain ⟨Ω, hΩ, hcov⟩ := AdelicSubgroupPoints.exists_isCompact_rational_mul_mem_range F
    (iV ≫ q) hV.1.smooth hV.1.connectedSpace hV.1.isUnipotent
  obtain ⟨bE, hbE, hbound⟩ := hR
    ((fun x : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) ×
      AdelicGroupPoints F G => (x.1 : AdelicGroupPoints F G) * x.2) '' (Ω ×ˢ C))
    ((hΩ.prod hC).image (by fun_prop)) n e Λ hΛ hreg
  have hcls : ∀ δ δ' : AdelicSubgroupPoints.rationalSubgroup F G
      (SubgroupFunctor.range (iV ≫ q)),
      intertwiningRationalCoset F p w δ = intertwiningRationalCoset F p w δ' →
      (δ' : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) *
        (δ : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)))⁻¹ ∈
        intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w) := by
    intro δ δ' h
    have hrel := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    rw [parabolicRationalSubgroup, Subgroup.mem_subgroupOf] at hrel
    obtain ⟨z, -, hz⟩ := hrel
    exact mul_inv_mem_intertwiningRationalSubgroup r w hG hU hq hV hmul hw δ.2 δ'.2 ⟨z, hz⟩
  have : Countable (AdelicGroupPoints.rationalSubgroup F G) :=
    LeftCosetSpace.countable_of_isDiscrete _ (AdelicGroupPoints.isDiscrete_rationalSubgroup F G)
  have : (AdelicSubgroupPoints.normalizedHaarMeasure F G
      (SubgroupFunctor.range (iV ≫ q))).IsMulLeftInvariant := by
    unfold AdelicSubgroupPoints.normalizedHaarMeasure
    infer_instance
  have hΩν : AdelicSubgroupPoints.normalizedHaarMeasure F G
      (SubgroupFunctor.range (iV ≫ q)) Ω ≠ ∞ := by
    rw [AdelicSubgroupPoints.normalizedHaarMeasure, Measure.smul_apply, smul_eq_mul]
    refine ENNReal.mul_ne_top ?_ hΩ.measure_lt_top.ne
    rw [AdelicSubgroupPoints.quotientMassNormalizer, ne_eq, ENNReal.inv_eq_top]
    exact Measure.measure_univ_ne_zero.mpr
      (AdelicSubgroupPoints.rationalQuotientHaarMeasure_ne_zero F G _)
  obtain ⟨b, hb, hbβ⟩ := LeftCosetSpace.exists_integrable_majorant_of_cover
    (AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)))
    (intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w))
    (isDiscrete_intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w))
    (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV ≫ q)))
    hΩ hΩν (intertwiningRationalCoset F p w) hcls hbE
  refine ⟨b, hb, fun x g hg s hs => ?_⟩
  obtain ⟨ρ₀, hρ₀, hρ₀v⟩ := hcov (Quotient.out x)
  have hx : LeftCosetSpace.mk _ (((⟨ρ₀⁻¹, inv_mem hρ₀⟩ : AdelicSubgroupPoints.rationalSubgroup F G
      (SubgroupFunctor.range (iV ≫ q))) : AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (iV ≫ q))) * (ρ₀ * Quotient.out x)) = x := by
    rw [← mul_assoc]
    simp only [inv_mul_cancel, one_mul]
    exact LeftCosetSpace.mk_out _ x
  have hbx := hbβ ⟨ρ₀⁻¹, inv_mem hρ₀⟩ _ hρ₀v
  rw [hx] at hbx
  refine le_trans (le_of_eq ?_) ((hbound _ _ ⟨(ρ₀ * Quotient.out x, g), ⟨hρ₀v, hg⟩, rfl⟩ s hs).trans
    hbx)
  rw [intertwiningRationalCoset,
    IsIwasawaCompact.eisensteinTerm_mk hK hφ.1 r.isCompatible.levi hU]
  change ‖hK.parameterTwist φ (e s) ((innerAdelicPoint F G w)⁻¹ *
      ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * g)‖ = _
  congr 2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

end Langlands.Global

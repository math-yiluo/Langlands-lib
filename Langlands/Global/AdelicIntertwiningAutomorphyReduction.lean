import Langlands.Global.AdelicIntertwiningAutomorphyReductionStatement
import Langlands.Global.AdelicIntertwiningModerateGrowthProof
import Langlands.Global.AdelicIntertwiningCompactEquivariance
import Langlands.Global.AdelicIntertwiningLeftInvariance
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.AdelicIntertwiningIntegrability
import Langlands.Global.AdelicIntertwiningHaarOffset
import Langlands.Global.AdelicEisensteinFiniteCompactChangeProof
import Langlands.Global.EisensteinConstantTerm.QuotientUnfolding
import Langlands.Global.DiscreteLeftCosetMeasureTransport

/-! # Uniform automorphy of intertwining integrals from its two remaining analytic parts

`intertwiningUniformAutomorphy_of_analytic` proves `IntertwiningUniformAutomorphyStatement` from
`IntertwiningSmoothSlicesStatement` and `IntertwiningUniformCenterIdealStatement`, and
`intertwiningUniformAutomorphyReduction` restates this as
`IntertwiningUniformAutomorphyReductionStatement`. The other
conditions of an automorphic form on `V(𝔸)M'(F) \ G(𝔸)` are proved here: left invariance under
`V(𝔸)` (right invariance of the quotient measure) and under `M'(F)` (conjugation by a rational
Levi point), continuity (dominated convergence), finiteness under the infinite part of `K` and a
finite level (compact equivariance), and moderate growth (`intertwiningModerateGrowth`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology Filter
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section Invariance

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- Invariance under two subgroups gives invariance under the subgroup they generate. -/
theorem isLeftInvariantUnder_sup [IsAffine G.X.left] {Γ₁ Γ₂ : Subgroup (AdelicGroupPoints F G)}
    {f : AdelicGroupPoints F G → ℂ} (h₁ : IsLeftInvariantUnder F G Γ₁ f)
    (h₂ : IsLeftInvariantUnder F G Γ₂ f) : IsLeftInvariantUnder F G (Γ₁ ⊔ Γ₂) f := by
  let S : Subgroup (AdelicGroupPoints F G) :=
    { carrier := {x | ∀ g, f (x * g) = f g}
      mul_mem' := fun {x y} hx hy g => by
        change f (x * y * g) = f g
        rw [mul_assoc, hx, hy]
      one_mem' := fun g => by
        change f (1 * g) = f g
        rw [one_mul]
      inv_mem' := fun {x} hx g => by
        rw [← hx (x⁻¹ * g), mul_inv_cancel_left] }
  have hle : Γ₁ ⊔ Γ₂ ≤ S := sup_le (fun x hx => h₁ x hx) (fun x hx => h₂ x hx)
  exact fun x hx => hle hx

/-- The adelic-point map of a rational point is the rational point of its image. -/
theorem map_rational_eq_rational {H H' : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ H')
    (y : RationalGroupPoints F H) :
    map F H H' f (rational F H y) =
      rational F H' (H.affinePointsTarget f (CommAlgCat.of F F) y) :=
  (DFunLike.congr_fun (rational_naturality F H f) y).symm

end Invariance

namespace AdelicGroupPoints

section Integral

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [IsAffine V.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

local notation "Vₐ" j => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)

/-- Left multiplication of the external argument by a point of the target radical `V(𝔸)` leaves
the intertwining integral invariant: `I_λ(y g) = I_λ(g)`. The proof uses right translation by `y`
on the integration variable in `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)`, which preserves the quotient
measure since `V(𝔸)` is unimodular. -/
theorem IsIwasawaCompact.intertwiningIntegral_radical_mul (hK : IsIwasawaCompact p K)
    (iU : U ⟶ P) (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (hVs : Smooth V.X.hom) (hVc : ConnectedSpace V.X.left) (hVu : IsUnipotent V)
    (hU : IsUnipotent U) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)
    (lam : ComplexCharacterParameter F P) (y : Vₐ j) (g : AdelicGroupPoints F G) :
    hK.intertwiningIntegral iU j w φ lam ((y : AdelicGroupPoints F G) * g) =
      hK.intertwiningIntegral iU j w φ lam g := by
  let wA := innerAdelicPoint F G w
  let Γ := intertwiningRationalSubgroup F p iU j wA
  have hΓ := isDiscrete_intertwiningRationalSubgroup F p iU j wA
  let hClosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : IsClosed ((Vₐ j) : Set (AdelicGroupPoints F G)) := hClosed
  let : LocallyCompactSpace (Vₐ j) := hClosed.locallyCompactSpace
  let : PolishSpace (Vₐ j) := hClosed.polishSpace
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j)) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hVs hVc hVu
  let ν := AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)
  let : (Measure.haar : Measure (Vₐ j)).IsMulRightInvariant :=
    AdelicSubgroupPoints.haar_isMulRightInvariant_of_compactRationalQuotient F G
      (SubgroupFunctor.range j)
  let : ν.IsMulLeftInvariant := by
    dsimp only [ν, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  let : ν.IsMulRightInvariant := by
    dsimp only [ν, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  let : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ hΓ
  have hmp : MeasurePreserving (LeftCosetSpace.rightTranslate Γ y)
      (intertwiningMeasure F p iU j wA) (intertwiningMeasure F p iU j wA) :=
    LeftCosetSpace.measurePreserving_rightTranslate_discrete Γ hΓ ν y
  have hemb : MeasurableEmbedding (LeftCosetSpace.rightTranslate Γ y) :=
    (LeftCosetSpace.rightTranslateHomeomorph Γ y).measurableEmbedding
  have hcomp (x : LeftCosetSpace Γ) :
      hK.intertwiningIntegrand iU j w φ lam g (LeftCosetSpace.rightTranslate Γ y x) =
        hK.intertwiningIntegrand iU j w φ lam ((y : AdelicGroupPoints F G) * g) x := by
    induction x using Quotient.inductionOn with
    | _ v =>
      change hK.intertwiningIntegrand iU j w φ lam g
          (LeftCosetSpace.rightTranslate Γ y (LeftCosetSpace.mk Γ v)) =
        hK.intertwiningIntegrand iU j w φ lam ((y : AdelicGroupPoints F G) * g)
          (LeftCosetSpace.mk Γ v)
      rw [LeftCosetSpace.rightTranslate_mk, hK.intertwiningIntegrand_mk iU j w hU hφ,
        hK.intertwiningIntegrand_mk iU j w hU hφ]
      congr 1
      simp only [Subgroup.coe_mul, mul_assoc]
  unfold IsIwasawaCompact.intertwiningIntegral
  simp_rw [← hcomp]
  exact hmp.integral_comp hemb _

/-- Left translation of the external argument by a rational point of the target Levi `M'` does
not change the intertwining integral. Conjugation by the point preserves `V(𝔸)`, its
normalized Haar measure and the rational stabilizer `V(F) ∩ wU(𝔸)w⁻¹`, and moves the argument
of `φ_λ` by the rational point `w⁻¹ m' w` of the source parabolic, under which `φ_λ` is left
invariant. -/
theorem IsIwasawaCompact.intertwiningIntegral_levi_rational_mul (hK : IsIwasawaCompact p K)
    {iU : U ⟶ P} {l : M ⟶ P} {q : Q ⟶ G} {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
    (hw : IsWeylConjugation p l q l' w c)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hl : IsRationalLeviSubgroup l)
    (hV : LeviSubgroup.IsGeometricUnipotentRadical iV) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (lam : ComplexCharacterParameter F P) (m₀ : RationalGroupPoints F M')
    (g : AdelicGroupPoints F G) :
    hK.intertwiningIntegral iU (iV ≫ q) w φ lam
        (map F M' G (l' ≫ q) (rational F M' m₀) * g) =
      hK.intertwiningIntegral iU (iV ≫ q) w φ lam g := by
  let wA := innerAdelicPoint F G w
  let Γ := intertwiningRationalSubgroup F p iU (iV ≫ q) wA
  have hΓ := isDiscrete_intertwiningRationalSubgroup F p iU (iV ≫ q) wA
  have hN : (SubgroupFunctor.range iV).IsNormal := hV.1.isNormal
  have hφU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx g => hφ x (Subgroup.mem_sup_left hx) g
  have hx₀ : rational F Q (M'.affinePointsTarget l' (CommAlgCat.of F F) m₀) =
      map F M' Q l' (rational F M' m₀) := (map_rational_eq_rational l' m₀).symm
  have hxq : map F Q G q (rational F Q (M'.affinePointsTarget l' (CommAlgCat.of F F) m₀)) =
      map F M' G (l' ≫ q) (rational F M' m₀) := by
    rw [hx₀, map_comp_apply_of_hom]
  have hxP : map F P G p (rational F P (M'.affinePointsTarget (c ≫ l) (CommAlgCat.of F F) m₀)) =
      wA⁻¹ * map F M' G (l' ≫ q) (rational F M' m₀) * wA := by
    rw [← map_rational_eq_rational (c ≫ l) m₀, map_comp_apply_of_hom (p := l) c,
      map_comp_apply_of_hom (p := q) l']
    exact hw.adelic_comp_eq (rational F M' m₀)
  let α := EisensteinConstantTerm.conjAdelic q iV hN
    (rational F Q (M'.affinePointsTarget l' (CommAlgCat.of F F) m₀))
  let hClosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)
  let : IsClosed ((Vₐ (iV ≫ q)) : Set (AdelicGroupPoints F G)) := hClosed
  let : LocallyCompactSpace (Vₐ (iV ≫ q)) := hClosed.locallyCompactSpace
  let : PolishSpace (Vₐ (iV ≫ q)) := hClosed.polishSpace
  let : CompactSpace
      (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range (iV ≫ q))) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (iV ≫ q) hV.1.smooth
      hV.1.connectedSpace hV.1.isUnipotent
  let ΓV := AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q))
  have hΓV := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q))
  have : Countable ΓV := EisensteinConstantTerm.countable_rationalSubgroup _
  let ν := AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV ≫ q))
  let : ν.IsMulLeftInvariant := by
    dsimp only [ν, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  have hαV : ∀ v, α v ∈ ΓV ↔ v ∈ ΓV :=
    EisensteinConstantTerm.conjAdelic_mem_rationalSubgroup_iff q iV hN _
  have hmpV : MeasurePreserving α ν ν :=
    EisensteinConstantTerm.measurePreserving_of_preserves ΓV
      (LeftCosetSpace.measurableSet_fundamentalDomain ΓV hΓV)
      (LeftCosetSpace.fundamentalDomain_unique ΓV hΓV) α hαV Measure.haar
      (EisensteinConstantTerm.haar_fundamentalDomain_ne_zero _)
      (EisensteinConstantTerm.haar_fundamentalDomain_ne_top _) _
  have hstab : ∀ v, α v ∈ Γ ↔ v ∈ Γ := by
    intro v
    have hH := conjAdelic_mem_intertwiningAdelicStabilizer_iff iU iV hw hU.1.isNormal hN
      (rational F M' m₀) v
    rw [← hx₀] at hH
    change α v ∈ intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w) ↔
      v ∈ intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w)
    rw [intertwiningRationalSubgroup_eq_rational_inf_stabilizer, Subgroup.mem_inf,
      Subgroup.mem_inf, hαV v, hH]
  let E := LeftCosetSpace.measurableEquivOfMulEquiv α Γ Γ hstab
  have hE : MeasurePreserving E (intertwiningMeasure F p iU (iV ≫ q) wA)
      (intertwiningMeasure F p iU (iV ≫ q) wA) :=
    LeftCosetSpace.measurePreserving_discreteQuotientMeasure α Γ Γ hstab hΓ hΓ ν ν hmpV
  have hcomp (y : LeftCosetSpace Γ) :
      hK.intertwiningIntegrand iU (iV ≫ q) w φ lam
          (map F M' G (l' ≫ q) (rational F M' m₀) * g) (E y) =
        hK.intertwiningIntegrand iU (iV ≫ q) w φ lam g y := by
    induction y using Quotient.inductionOn with
    | _ v =>
      change hK.intertwiningIntegrand iU (iV ≫ q) w φ lam _ (E (LeftCosetSpace.mk Γ v)) =
        hK.intertwiningIntegrand iU (iV ≫ q) w φ lam g (LeftCosetSpace.mk Γ v)
      rw [LeftCosetSpace.measurableEquivOfMulEquiv_mk,
        hK.intertwiningIntegrand_mk iU (iV ≫ q) w hU.1.isUnipotent hφU,
        hK.intertwiningIntegrand_mk iU (iV ≫ q) w hU.1.isUnipotent hφU,
        EisensteinConstantTerm.conjAdelic_coe, hxq]
      have hrearr : wA⁻¹ * (map F M' G (l' ≫ q) (rational F M' m₀) * (v : AdelicGroupPoints F G) *
            (map F M' G (l' ≫ q) (rational F M' m₀))⁻¹) *
            (map F M' G (l' ≫ q) (rational F M' m₀) * g) =
          map F P G p (rational F P (M'.affinePointsTarget (c ≫ l) (CommAlgCat.of F F) m₀)) *
            (wA⁻¹ * (v : AdelicGroupPoints F G) * g) := by
        rw [hxP]
        group
      rw [hrearr, hK.parameterTwist_map_rational_mul hφ hl hU]
  unfold IsIwasawaCompact.intertwiningIntegral
  calc ∫ x, hK.intertwiningIntegrand iU (iV ≫ q) w φ lam
          (map F M' G (l' ≫ q) (rational F M' m₀) * g) x
          ∂intertwiningMeasure F p iU (iV ≫ q) wA
      = ∫ y, hK.intertwiningIntegrand iU (iV ≫ q) w φ lam
          (map F M' G (l' ≫ q) (rational F M' m₀) * g) (E y)
          ∂intertwiningMeasure F p iU (iV ≫ q) wA :=
        (hE.integral_comp E.measurableEmbedding _).symm
    _ = _ := by
      simp_rw [hcomp]
      rfl

/-- Integrable majorants that are uniform for the external argument in compact sets make the
intertwining integral continuous (dominated convergence). -/
theorem IsIwasawaCompact.continuous_intertwiningIntegral (hK : IsIwasawaCompact p K)
    (iU : U ⟶ P) (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (hU : IsUnipotent U)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ) (hφc : Continuous φ)
    (lam : ComplexCharacterParameter F P)
    (hmaj : ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∃ b : LeftCosetSpace (intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)) → ℝ,
        Integrable b (intertwiningMeasure F p iU j (innerAdelicPoint F G w)) ∧
        ∀ x, ∀ g ∈ C, ‖hK.intertwiningIntegrand iU j w φ lam g x‖ ≤ b x) :
    Continuous (hK.intertwiningIntegral iU j w φ lam) := by
  let Γ := intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)
  have hΓ := isDiscrete_intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)
  let hClosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : LocallyCompactSpace (Vₐ j) := hClosed.locallyCompactSpace
  let : PolishSpace (Vₐ j) := hClosed.polishSpace
  let : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ hΓ
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨C, hC, hCn⟩ := exists_compact_mem_nhds g₀
  obtain ⟨b, hb, hbound⟩ := hmaj C hC
  show ContinuousAt (fun g => ∫ x, hK.intertwiningIntegrand iU j w φ lam g x
    ∂intertwiningMeasure F p iU j (innerAdelicPoint F G w)) g₀
  refine continuousAt_of_dominated (bound := b) ?_ ?_ hb ?_
  · exact Filter.Eventually.of_forall fun g =>
      (hK.continuous_intertwiningIntegrand iU j w hU hφ hφc lam g).aestronglyMeasurable
  · filter_upwards [hCn] with g hg
    exact Filter.Eventually.of_forall fun x => hbound x g hg
  · refine Filter.Eventually.of_forall fun x => ?_
    show ContinuousAt (fun g => hK.parameterTwist φ lam ((innerAdelicPoint F G w)⁻¹ *
      ((Quotient.out x : Vₐ j) : AdelicGroupPoints F G) * g)) g₀
    exact ((hK.continuous_parameterTwist hφc lam).comp
      (continuous_const.mul continuous_id)).continuousAt

end Integral

section FiniteLevel

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- The finite projection of a maximal compact subgroup of `G(𝔸)` consists of finite points
whose inclusion in `G(𝔸)` lies in the compact. -/
theorem IsMaximalCompactSubgroup.map_finite_le_comap_ofFinite
    (hKmax : IsMaximalCompactSubgroup F G K) :
    K.map (finite F G).toMonoidHom ≤ K.comap (ofFinite F G).toMonoidHom := by
  rintro _ ⟨k, hk, rfl⟩
  change ofFinite F G (finite F G k) ∈ K
  rw [IsMaximalCompactSubgroup.eq_comap_prod F G K hKmax, Subgroup.mem_comap,
    Subgroup.mem_prod]
  refine ⟨?_, ?_⟩
  · change infinite F G (ofFinite F G (finite F G k)) ∈ K.map (infinite F G).toMonoidHom
    rw [infinite_ofFinite]
    exact Subgroup.one_mem _
  · change finite F G (ofFinite F G (finite F G k)) ∈ K.map (finite F G).toMonoidHom
    rw [finite_ofFinite]
    exact ⟨k, hk, rfl⟩

end FiniteLevel

end AdelicGroupPoints

/-- **Uniform automorphy of intertwining integrals from its two remaining analytic parts.**
`IntertwiningSmoothSlicesStatement` and `IntertwiningUniformCenterIdealStatement` imply
`IntertwiningUniformAutomorphyStatement`. The threshold is the largest of those of the two
premises, of `intertwiningModerateGrowth`, of `intertwiningAbsoluteConvergence` and of
`intertwiningIntegrability`; the ideal is the one of the center-ideal premise. -/
theorem intertwiningUniformAutomorphy_of_analytic
    (hS : IntertwiningSmoothSlicesStatement.{u})
    (hZ : IntertwiningUniformCenterIdealStatement.{u}) :
    IntertwiningUniformAutomorphyStatement.{u} := by
  intro F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _ π' w c
    hG hU hq hV hl' hmul hπ hw K hK hK' N d rho hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨R₁, hR₁⟩ := hS F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c hG hU hq hV hl'
    hmul hπ hw K hK hK' rho hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨R₂, J, hJ, hR₂⟩ := hZ F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c hG hU hq hV
    hl' hmul hπ hw K hK hK' rho hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨R₃, hR₃⟩ := intertwiningModerateGrowth F G P M U Q M' V A p iU l a r hA hT q iV l' π'
    w c hG hU hq hV hl' hmul hπ hw K hK hK' rho hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨R₄, hR₄⟩ := intertwiningAbsoluteConvergence F G P M U Q M' V A p iU l a r hA hT q iV
    l' w c hG hU hq hV hl' hmul hw K hK rho hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨R₅, hR₅⟩ := intertwiningIntegrability F G P M U Q M' V A p iU l a r hA hT q iV l' w c
    hG hU hq hV hl' hmul hw K hK rho hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨n, ⟨e⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  refine ⟨max (max R₁ R₂) (max (max R₃ R₄) R₅), J, hJ, fun lam hlam => ?_⟩
  have hreg (R : ℝ) (hR : R ≤ max (max R₁ R₂) (max (max R₃ R₄) R₅)) :
      r.IsRegularParameter hA hT R lam :=
    fun α hα => hR.trans_lt (hlam α hα)
  have h₁ := hreg R₁ ((le_max_left _ _).trans (le_max_left _ _))
  have h₂ := hreg R₂ ((le_max_right _ _).trans (le_max_left _ _))
  have h₃ := hreg R₃ (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _))
  have h₄ := hreg R₄ (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _))
  have h₅ := hreg R₅ ((le_max_right _ _).trans (le_max_right _ _))
  have hφU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx g => hφ.1 x (Subgroup.mem_sup_left hx) g
  have hcenter := hR₂ lam h₂
  -- Left invariance under `V(𝔸)` and `M'(F)`.
  have hleft : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F q iV l')
      (hK.intertwiningOperator hK' iU l iV c π' w φ lam) := by
    apply isLeftInvariantUnder_sup
    · rintro _ ⟨v, rfl⟩ g
      have hmem : map F V G (iV ≫ q) v ∈
          AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) := by
        change _ ∈ parabolicUnipotentImage F q iV
        exact ⟨v, rfl⟩
      change hK.intertwiningOperator hK' iU l iV c π' w φ lam (map F V G (iV ≫ q) v * g) =
        hK.intertwiningOperator hK' iU l iV c π' w φ lam g
      unfold IsIwasawaCompact.intertwiningOperator
      rw [hK'.heightPower_unipotent_mul hV.1.isUnipotent iV]
      congr 1
      exact hK.intertwiningIntegral_radical_mul iU (iV ≫ q) w hV.1.smooth hV.1.connectedSpace
        hV.1.isUnipotent hU.1.isUnipotent hφU lam ⟨_, hmem⟩ g
    · rintro _ ⟨m₀, rfl⟩ g
      change hK.intertwiningOperator hK' iU l iV c π' w φ lam
          (map F M' G (l' ≫ q) (rational F M' m₀) * g) =
        hK.intertwiningOperator hK' iU l iV c π' w φ lam g
      have hx : map F M' G (l' ≫ q) (rational F M' m₀) =
          map F Q G q (rational F Q (M'.affinePointsTarget l' (CommAlgCat.of F F) m₀)) := by
        rw [map_comp_apply_of_hom, map_rational_eq_rational]
      unfold IsIwasawaCompact.intertwiningOperator
      rw [hK.intertwiningIntegral_levi_rational_mul hw hU r.isCompatible.levi hV hφ.1 lam m₀ g,
        hx, hK'.heightPower_rational_mul]
  -- Continuity.
  have hcontI : Continuous (hK.intertwiningIntegral iU (iV ≫ q) w φ lam) := by
    refine hK.continuous_intertwiningIntegral iU (iV ≫ q) w hU.1.isUnipotent hφU hφ.2.1.1 lam
      (fun C hC => ?_)
    have hsingle : ∀ s ∈ ({e.symm lam} : Set (Fin n → ℂ)),
        r.IsRegularParameter hA hT R₄ (e s) := by
      intro s hs
      rw [Set.mem_singleton_iff.mp hs, e.apply_symm_apply]
      exact h₄
    obtain ⟨b, hb, hbound⟩ := hR₄ C hC n e {e.symm lam} isCompact_singleton hsingle
    exact ⟨b, hb, fun x g hg => by
      simpa only [e.apply_symm_apply] using hbound x g hg (e.symm lam) (Set.mem_singleton _)⟩
  have hcont : Continuous (hK.intertwiningOperator hK' iU l iV c π' w φ lam) :=
    (hK'.continuous_heightPower _).mul hcontI
  -- A finite level.
  obtain ⟨L, hLo, hL⟩ := hφ.2.1.2.2
  have hL'o : IsOpen ((L ⊓ K.map (finite F G).toMonoidHom : Subgroup _) :
      Set (FiniteAdelicGroupPoints F G)) :=
    hLo.inter (IsMaximalCompactSubgroup.isOpen_finite F G K hKmax)
  have hle : L ⊓ K.map (finite F G).toMonoidHom ≤ K.comap (ofFinite F G).toMonoidHom :=
    fun b hb => IsMaximalCompactSubgroup.map_finite_le_comap_ofFinite hKmax hb.2
  have hlevel := hK.intertwiningOperator_fixedByFiniteLevel hK' iU l iV c π' w lam
    (L ⊓ K.map (finite F G).toMonoidHom) hle (fun b hb g => hL b hb.1 g)
  -- Finiteness under the infinite part of `K`.
  have hfin := hK.intertwiningOperator_isInfiniteSubgroupFinite hK' iU l iV c π' w lam φ
    (hR₅ lam h₅) hφ.2.2.1
  exact ⟨⟨hleft, ⟨hcont, hR₁ lam h₁, _, hL'o, hlevel⟩, hfin, ⟨J, hJ, hcenter⟩, hR₃ lam h₃⟩,
    hcenter⟩

/-- Proof of `IntertwiningUniformAutomorphyReductionStatement`. -/
theorem intertwiningUniformAutomorphyReduction :
    IntertwiningUniformAutomorphyReductionStatement.{u} :=
  fun hS hZ => intertwiningUniformAutomorphy_of_analytic hS hZ


/-- Plot-smooth infinite slices and one common annihilating center ideal imply the
uniform automorphy proposition for regular intertwining integrals. -/
def IntertwiningAutomorphyReductionStatement : Prop :=
  IntertwiningUniformAutomorphyReductionStatement.{u}

set_option maxHeartbeats 600000 in
/-- Combine the analytic inputs with left invariance, continuity, moderate growth and
compact equivariance on the actual radical quotient. -/
theorem intertwiningUniformAutomorphy_of_smoothSlices_of_centerIdeal :
    IntertwiningAutomorphyReductionStatement.{u} := by
  classical
  intro hSmooth hCenter F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _
    π' w c hG hU hq hV hl' hMul hπ hw K hK hK' N d rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨Rs, hs⟩ := hSmooth F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c hG hU hq hV
    hl' hMul hπ hw K hK hK' rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨Rz, J, hJ, hz⟩ := hCenter F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c hG hU hq hV
    hl' hMul hπ hw K hK hK' rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨Rm, hm⟩ := intertwiningModerateGrowth F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c
    hG hU hq hV hl' hMul hπ hw K hK hK' rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨Rc, hc⟩ := intertwiningAbsoluteConvergence F G P M U Q M' V A p iU l a r hA hT q iV l' w c
    hG hU hq hV hl' hMul hw K hK rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨n, ⟨e⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  let R := max (max Rs Rz) (max Rm Rc)
  have hsR : Rs ≤ R := (le_max_left Rs Rz).trans (le_max_left _ _)
  have hzR : Rz ≤ R := (le_max_right Rs Rz).trans (le_max_left _ _)
  have hmR : Rm ≤ R := (le_max_left Rm Rc).trans (le_max_right _ _)
  have hcR : Rc ≤ R := (le_max_right Rm Rc).trans (le_max_right _ _)
  let j := iV ≫ q
  let Γ := intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)
  let measure := intertwiningMeasure F p iU j (innerAdelicPoint F G w)
  have hclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
    hclosed.locallyCompactSpace
  let : PolishSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) := hclosed.polishSpace
  let : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ
    (isDiscrete_intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w))
  let Kf := K.comap (ofFinite F G).toMonoidHom
  have hKf : IsOpen (Kf : Set (FiniteAdelicGroupPoints F G)) := by
    have heq : Kf = K.map (finite F G).toMonoidHom := by
      ext b
      constructor
      · intro hb
        exact ⟨ofFinite F G b, hb, by simp⟩
      · rintro ⟨g, hg, rfl⟩
        exact ((hmax.mem_iff g).mp hg).2
    rw [heq]
    exact hmax.isOpen_finite
  obtain ⟨L, hL, hfix⟩ := hφ.2.1.2.2
  have hinv : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx => hφ.1 x (Subgroup.mem_sup_left hx)
  refine ⟨R, J, hJ, fun lam hlam => ?_⟩
  have hreg : r.IsRegularParameter hA hT Rc lam := fun α hα => hcR.trans_lt (hlam α hα)
  have hspec : ∀ s ∈ ({e.symm lam} : Set (Fin n → ℂ)), r.IsRegularParameter hA hT Rc (e s) := by
    intro s hs
    rwa [Set.mem_singleton_iff.mp hs, e.apply_symm_apply]
  let integrand g := hK.intertwiningIntegrand iU j w φ lam g
  have hmeas (g : AdelicGroupPoints F G) : AEStronglyMeasurable (integrand g) measure :=
    (hK.continuous_intertwiningIntegrand iU j w hU.1.isUnipotent hinv hφ.2.1.1 lam g).aestronglyMeasurable
  have hdom (C : Set (AdelicGroupPoints F G)) (hC : IsCompact C) :
      ∃ B : LeftCosetSpace Γ → ℝ, Integrable B measure ∧
        ∀ x g, g ∈ C → ‖integrand g x‖ ≤ B x := by
    obtain ⟨B, hB, hb⟩ := hc C hC n e {e.symm lam} isCompact_singleton hspec
    exact ⟨B, hB, fun x g hg => by
      simpa only [integrand, e.apply_symm_apply] using hb x g hg (e.symm lam) (Set.mem_singleton _)⟩
  have hint (g : AdelicGroupPoints F G) : Integrable (integrand g) measure := by
    obtain ⟨B, hB, hb⟩ := hdom {g} isCompact_singleton
    exact hB.mono' (hmeas g) (Eventually.of_forall fun x => hb x g (Set.mem_singleton g))
  have hcont : Continuous (hK.intertwiningIntegral iU j w φ lam) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    obtain ⟨C, hC, hCg⟩ := exists_compact_mem_nhds g
    obtain ⟨B, hB, hb⟩ := hdom C hC
    change ContinuousAt (fun y => ∫ x, integrand y x ∂measure) g
    have hbd : ∀ᶠ y in 𝓝 g, ∀ᵐ x ∂measure, ‖integrand y x‖ ≤ B x :=
      (show ∀ᶠ y in 𝓝 g, y ∈ C from hCg).mono (fun y hy => Eventually.of_forall fun x => hb x y hy)
    apply continuousAt_of_dominated (Eventually.of_forall hmeas) hbd hB
    exact Eventually.of_forall fun x =>
      ((hK.continuous_parameterTwist hφ.2.1.1 lam).comp (continuous_const.mul continuous_id)).continuousAt
  let out := hK.intertwiningOperator hK' iU l iV c π' w φ lam
  have hOut : Continuous out := (hK'.continuous_heightPower _).mul hcont
  have hZ := hz lam (fun α hα => hzR.trans_lt (hlam α hα))
  refine ⟨?_, hZ⟩
  refine ⟨hK.intertwiningOperator_leftInvariant iU iV π' hK' hU hV hφ.1 lam hw r.isCompatible.levi,
    ⟨hOut, hs lam (fun α hα => hsR.trans_lt (hlam α hα)), ?_⟩,
    hK.intertwiningOperator_isInfiniteSubgroupFinite hK' iU l iV c π' w lam φ hint hφ.2.2.1,
    ⟨J, hJ, hZ⟩, hm lam (fun α hα => hmR.trans_lt (hlam α hα))⟩
  exact ⟨L ⊓ Kf, hL.inter hKf, hK.intertwiningOperator_fixedByFiniteLevel hK' iU l iV c π'
    w lam (L ⊓ Kf) inf_le_right (fun b hb => hfix b hb.1)⟩

end Langlands.Global

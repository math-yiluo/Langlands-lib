import Langlands.Global.AdelicSubgroupQuotientTransport
import Langlands.Global.EisensteinConstantTerm.Points
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.GroupScheme.Dynamic.SubgroupMaximality
import Langlands.GroupScheme.RelativeLevi.SplitFaceCoordinateConjugacy
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Constant terms on the rational parabolic quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Opposite
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicSubgroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "Points" => AdelicGroupPoints F G

private def inducingConstantTermIntegrand (V : SubgroupFunctor G) (φ : Points → ℂ)
    (g : Points) (v : AdelicSubgroupPoints.RationalQuotient F G V) : ℂ :=
  φ ((v.out : adelicPoints F G V).val * g)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem inducingConstantTermIntegrand_mk (V : SubgroupFunctor G) (φ : Points → ℂ)
    (hφ : ∀ a : AdelicSubgroupPoints.rationalSubgroup F G V, ∀ g : Points,
      φ (a.val.val * g) = φ g) (g : Points) (v : adelicPoints F G V) :
    inducingConstantTermIntegrand V φ g (LeftCosetSpace.mk _ v) = φ (v.val * g) := by
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G V
  let z := (LeftCosetSpace.mk Γ v).out
  have hz : z * v⁻¹ ∈ Γ :=
    (LeftCosetSpace.mk_eq_mk_iff Γ v z).mp (Quotient.out_eq (LeftCosetSpace.mk Γ v)).symm
  unfold inducingConstantTermIntegrand
  exact (by simpa only [z, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left]
    using hφ ⟨z * v⁻¹, hz⟩ (v.val * g))

private theorem inducingConstantTermIntegrand_conj (V U : SubgroupFunctor G)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (hU : U = V.comap (G.innerIso x).hom)
    [IsClosed (adelicPoints F G V : Set Points)]
    [IsClosed (adelicPoints F G U : Set Points)]
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G V)]
    (φ : Points → ℂ)
    (hφV : ∀ a : AdelicSubgroupPoints.rationalSubgroup F G V, ∀ g : Points,
      φ (a.val.val * g) = φ g)
    (hφU : ∀ a : AdelicSubgroupPoints.rationalSubgroup F G U, ∀ g : Points,
      φ (a.val.val * g) = φ g)
    (hφx : ∀ g, φ (innerAdelicPoint F G x * g) = φ g) (g : Points) :
    (∫ v, inducingConstantTermIntegrand V φ (innerAdelicPoint F G x * g) v
      ∂normalizedRationalQuotientHaarMeasure F G V) =
    ∫ v, inducingConstantTermIntegrand U φ g v
      ∂normalizedRationalQuotientHaarMeasure F G U := by
  subst U
  rw [← integral_comp_rationalQuotientIso F (G.innerIso x) V]
  congr 1
  funext v
  induction v using Quotient.inductionOn with
  | _ v =>
    change inducingConstantTermIntegrand V φ (innerAdelicPoint F G x * g)
        (rationalQuotientIso F (G.innerIso x) V (LeftCosetSpace.mk _ v)) =
      inducingConstantTermIntegrand _ φ g (LeftCosetSpace.mk _ v)
    rw [rationalQuotientIso_mk, inducingConstantTermIntegrand_mk V φ hφV,
      inducingConstantTermIntegrand_mk _ φ hφU]
    change φ (G.affinePointsTarget (G.innerIso x).hom _ v.val *
      (innerAdelicPoint F G x * g)) = φ (v.val * g)
    rw [affinePointsTarget_innerIso_hom]
    simpa only [mul_assoc, inv_mul_cancel_left] using hφx (v.val * g)

variable {P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine U.X.left] (p : P ⟶ G) (iU : U ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left]

local notation "j" => (iU ≫ p)
local notation "V" => SubgroupFunctor.range j
local notation "Vₐ" => adelicPoints F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "Quot" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "μ" => normalizedRationalQuotientHaarMeasure F G V

/-- A compact radical average of a continuous function on the rational
parabolic quotient is continuous and invariant under both the rational
parabolic and the full adelic radical. -/
def InducingConstantTermCovarianceStatement : Prop :=
  LeviSubgroup.IsGeometricUnipotentRadical iU →
  ∀ φ : Points → ℂ, Continuous φ →
    IsLeftInvariantUnder F G (rationalImage F p) φ →
    Continuous (subgroupConstantTerm F j φ) ∧
    IsLeftInvariantUnder F G (rationalImage F p) (subgroupConstantTerm F j φ) ∧
    IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) (subgroupConstantTerm F j φ)

set_option maxHeartbeats 1100000 in
theorem inducingConstantTermCovariance : InducingConstantTermCovarianceStatement p iU := by
  intro hU φ hφc hφ
  have hnormal := Dynamic.range_comp_isNormalizedBy_of_isNormal iU p hU.1.isNormal
  let : IsClosed (Vₐ : Set Points) := isClosed_adelicPoints_range F G j
  let : CompactSpace Quot := compactSpace_rationalQuotient_range_unipotent F j
    hU.1.smooth hU.1.connectedSpace hU.1.isUnipotent
  let : BorelSpace Quot := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let : IsProbabilityMeasure μ := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  have hΓ (a : Γ) (g : Points) : φ (a.val.val * g) = φ g :=
    hφ _ (rationalImage_comp_le iU p ((mem_rationalSubgroup_range_iff j a.val).mp a.2)) g
  change Continuous (fun g => ∫ v, inducingConstantTermIntegrand V φ g v ∂μ) ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · have hcont : Continuous (fun x : Points × Quot =>
        inducingConstantTermIntegrand V φ x.1 x.2) := by
      rw [← (IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)).continuous_comp_iff]
      change Continuous (fun x : Points × Vₐ =>
        inducingConstantTermIntegrand V φ x.1 (LeftCosetSpace.mk Γ x.2))
      simp_rw [inducingConstantTermIntegrand_mk V φ hΓ]
      exact hφc.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
    simpa only [Measure.restrict_univ] using continuous_parametric_integral_of_continuous hcont
      (isCompact_univ (X := Quot))
  · rintro _ ⟨x, rfl⟩ g
    let X := (Over.mk (𝟙 (Spec (CommRingCat.of F))))
    let e : X ≅ (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)) :=
      Gm.affineTestIso _ _ (by exact (Spec.map_id (CommRingCat.of F)).symm)
    let x₀ : X ⟶ P.X := e.hom ≫ x
    let y := x₀ ≫ p.hom.hom
    have hy : innerAdelicPoint F G y = map F P G p (rational F P x) := by
      rw [innerAdelicPoint_eq_rational, map_rational]
      congr 1
      change G.constantPoint y _ = x ≫ p.hom.hom
      let T := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))
      have ht : (Over.homMk T.hom : T ⟶ X) = e.inv := by
        apply Over.OverMorphism.ext
        change T.hom = e.inv.left
        simpa only [show X.hom = 𝟙 _ from rfl, Category.comp_id] using (Over.w e.inv).symm
      change (Over.homMk T.hom : T ⟶ X) ≫ (e.hom ≫ x) ≫ p.hom.hom = _
      simp only [ht, Category.assoc, e.inv_hom_id_assoc]
    have he : V = SubgroupFunctor.comap (G.innerIso y).hom V :=
      (SubgroupFunctor.comap_innerIso_eq_of_isNormalizedBy hnormal (show y ∈
        (SubgroupFunctor.range p).carrier X from ⟨x₀, rfl⟩)).symm
    have hxy (g' : Points) : φ (innerAdelicPoint F G y * g') = φ g' := by
      rw [hy]
      exact hφ _ ⟨x, rfl⟩ g'
    change subgroupConstantTerm F j φ (map F P G p (rational F P x) * g) = _
    rw [← hy]
    exact inducingConstantTermIntegrand_conj V V y he φ hΓ hΓ hxy g
  · intro a ha g
    let t : Vₐ := ⟨a, ha⟩
    let τ := LeftCosetSpace.rightTranslateHomeomorph Γ t
    have hτ : MeasurePreserving τ μ μ :=
      measurePreserving_rightTranslate_of_compactRationalQuotient F G V t
    change (∫ v, inducingConstantTermIntegrand V φ (a * g) v ∂μ) =
      ∫ v, inducingConstantTermIntegrand V φ g v ∂μ
    rw [← hτ.integral_comp τ.measurableEmbedding (inducingConstantTermIntegrand V φ g)]
    congr 1
    funext v
    induction v using Quotient.inductionOn with
    | _ v =>
      change inducingConstantTermIntegrand V φ (a * g) (LeftCosetSpace.mk Γ v) =
        inducingConstantTermIntegrand V φ g (LeftCosetSpace.mk Γ (v * t))
      rw [inducingConstantTermIntegrand_mk V φ hΓ, inducingConstantTermIntegrand_mk V φ hΓ]
      exact congrArg φ (mul_assoc v.val a g).symm

end Langlands.Global.AdelicGroupPoints

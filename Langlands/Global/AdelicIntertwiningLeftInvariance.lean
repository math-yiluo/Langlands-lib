import Langlands.Global.AdelicIntertwiningHaarOffset
import Langlands.Global.AdelicIntertwiningIntegrability
import Langlands.Global.AdelicIntertwiningConvergenceReduction
import Langlands.Global.AdelicSubgroupNormalizedHaarTransport
import Langlands.Automorphic.UnitaryCharacterPairing

/-! # Left invariance of the actual adelic intertwining operator -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Automorphic.UnitaryCharacterPairing (leftStabilizer)

private theorem measurePreserving_normalizedHaar_of_rational {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (S : SubgroupFunctor G)
    [hS : IsClosed (AdelicSubgroupPoints.adelicPoints F G S : Set (AdelicGroupPoints F G))]
    (a : AdelicSubgroupPoints.adelicPoints F G S ≃ₜ* AdelicSubgroupPoints.adelicPoints F G S)
    (ha : ∀ x, a x ∈ AdelicSubgroupPoints.rationalSubgroup F G S ↔
      x ∈ AdelicSubgroupPoints.rationalSubgroup F G S) :
    MeasurePreserving a (AdelicSubgroupPoints.normalizedHaarMeasure F G S)
      (AdelicSubgroupPoints.normalizedHaarMeasure F G S) := by
  let V := AdelicSubgroupPoints.adelicPoints F G S
  let : LocallyCompactSpace V := hS.locallyCompactSpace
  let : PolishSpace V := hS.polishSpace
  let Δ := AdelicSubgroupPoints.rationalSubgroup F G S
  let hΔ := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G S
  let initial : Measure V := Measure.haar
  let pushed : Measure V := Measure.map a initial
  let : pushed.IsHaarMeasure := a.isHaarMeasure_map initial
  have hp : MeasurePreserving a initial pushed := ⟨a.continuous.measurable, rfl⟩
  have hQ := LeftCosetSpace.measurePreserving_discreteQuotientMeasure a Δ Δ ha hΔ hΔ initial pushed hp
  have hMass : pushed (LeftCosetSpace.fundamentalDomain Δ hΔ) =
      initial (LeftCosetSpace.fundamentalDomain Δ hΔ) := by
    have h := congrArg (fun m : Measure (LeftCosetSpace Δ) => m Set.univ) hQ.map_eq
    rw [Measure.map_apply hQ.measurable MeasurableSet.univ, Set.preimage_univ,
      LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.discreteQuotientMeasure,
      LeftCosetSpace.quotientMeasure_univ, LeftCosetSpace.quotientMeasure_univ] at h
    exact h.symm
  refine ⟨hp.measurable, ?_⟩
  rw [← AdelicSubgroupPoints.normalizedHaarMeasureFrom_eq F G S initial]
  conv_rhs => rw [AdelicSubgroupPoints.normalizedHaarMeasureFrom_eq F G S initial,
    ← AdelicSubgroupPoints.normalizedHaarMeasureFrom_eq F G S pushed]
  change Measure.map a ((initial (LeftCosetSpace.fundamentalDomain Δ hΔ))⁻¹ • initial) =
    (pushed (LeftCosetSpace.fundamentalDomain Δ hΔ))⁻¹ • pushed
  rw [hMass, Measure.map_smul _ hp.measurable.aemeasurable]

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [IsAffine Q.X.left] [IsAffine V.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : M ⟶ P} (iU : U ⟶ P)
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {l' : M' ⟶ Q} (iV : V ⟶ Q)
  [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {c : M' ⟶ M} (π' : Q ⟶ M') {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) (hK' : IsIwasawaCompact q K)
  (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
  {φ : AdelicGroupPoints F G → ℂ} (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
  (lam : ComplexCharacterParameter F P)

local notation "j" => iV ≫ q
local notation "S" => SubgroupFunctor.range j
local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G S
local notation "wA" => innerAdelicPoint F G w
local notation "Γ" => intertwiningRationalSubgroup F p iU j wA
local notation "measure" => intertwiningMeasure F p iU j wA
local notation "T" => hK.intertwiningOperator hK' iU l iV c π' w φ lam

include hU hV hφ in
private theorem intertwiningOperator_unipotent_mul (u : AdelicGroupPoints F V) (g : AdelicGroupPoints F G) :
    T (map F V G j u * g) = T g := by
  let v : Vₐ := ⟨map F V G j u, ⟨u, rfl⟩⟩
  have hclosed : IsClosed (Vₐ : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : IsClosed (Vₐ : Set (AdelicGroupPoints F G)) := hclosed
  let : LocallyCompactSpace Vₐ := hclosed.locallyCompactSpace
  let : PolishSpace Vₐ := hclosed.polishSpace
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G S) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j
      hV.1.smooth hV.1.connectedSpace hV.1.isUnipotent
  let hΓ := isDiscrete_intertwiningRationalSubgroup F p iU j wA
  let : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ hΓ
  let ν := AdelicSubgroupPoints.normalizedHaarMeasure F G S
  let : (Measure.haar : Measure Vₐ).IsMulRightInvariant :=
    AdelicSubgroupPoints.haar_isMulRightInvariant_of_compactRationalQuotient F G S
  have : ν.IsMulLeftInvariant := by dsimp only [ν, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  have : ν.IsMulRightInvariant := by dsimp only [ν, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  let E := LeftCosetSpace.rightTranslateHomeomorph Γ v
  have hpres : MeasurePreserving E measure measure :=
    LeftCosetSpace.measurePreserving_rightTranslate_discrete Γ hΓ ν v
  have hinv : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx => hφ x (Subgroup.mem_sup_left hx)
  have hI (x : LeftCosetSpace Γ) : hK.intertwiningIntegrand iU j w φ lam g (E x) =
      hK.intertwiningIntegrand iU j w φ lam (map F V G j u * g) x := by
    obtain ⟨z, rfl⟩ := LeftCosetSpace.mk_surjective Γ x
    change hK.intertwiningIntegrand iU j w φ lam g (LeftCosetSpace.mk Γ (z * v)) = _
    rw [hK.intertwiningIntegrand_mk iU j w hU.1.isUnipotent hinv,
      hK.intertwiningIntegrand_mk iU j w hU.1.isUnipotent hinv]
    change hK.parameterTwist φ lam (wA⁻¹ * (z.val * map F V G j u) * g) = _
    simp only [mul_assoc]
  unfold IsIwasawaCompact.intertwiningOperator
  rw [hK'.heightPower_unipotent_mul hV.1.isUnipotent iV]
  congr 1
  unfold IsIwasawaCompact.intertwiningIntegral
  simp_rw [← hI]
  exact hpres.integral_comp E.toMeasurableEquiv.measurableEmbedding _

include hU hV hφ in
private theorem intertwiningOperator_rationalLevi_mul
    (hw : IsWeylConjugation p l q l' w c) (hl : IsRationalLeviSubgroup l)
    (m : RationalGroupPoints F M') (g : AdelicGroupPoints F G) :
    T (map F M' G (l' ≫ q) (rational F M' m) * g) = T g := by
  let mA := rational F M' m
  let y := M'.affinePointsTarget l' _ m
  let z := M.affinePointsTarget l _ (M'.affinePointsTarget c _ m)
  let a := map F Q G q (rational F Q y)
  have hy : map F M' Q l' mA = rational F Q y := map_rational l' m
  have hz : map F M P l (map F M' M c mA) = rational F P z := by
    rw [map_rational c m, map_rational]
  have hwz : map F P G p (rational F P z) = wA⁻¹ * a * wA := by
    simpa only [hy, hz, a] using hw.adelic_comp_eq mA
  let α := EisensteinConstantTerm.conjAdelic q iV hV.1.isNormal (rational F Q y)
  have hr := EisensteinConstantTerm.conjAdelic_mem_rationalSubgroup_iff q iV hV.1.isNormal y
  have hH (v : Vₐ) : α v ∈ intertwiningAdelicStabilizer p iU j w ↔
      v ∈ intertwiningAdelicStabilizer p iU j w := by
    simpa only [α, hy] using
      conjAdelic_mem_intertwiningAdelicStabilizer_iff iU iV hw hU.1.isNormal hV.1.isNormal mA v
  have hα (v : Vₐ) : α v ∈ Γ ↔ v ∈ Γ := by
    rw [intertwiningRationalSubgroup_eq_rational_inf_stabilizer, Subgroup.mem_inf, Subgroup.mem_inf,
      hr, hH]
  have hclosed : IsClosed (Vₐ : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : IsClosed (Vₐ : Set (AdelicGroupPoints F G)) := hclosed
  let : PolishSpace Vₐ := hclosed.polishSpace
  let ν := AdelicSubgroupPoints.normalizedHaarMeasure F G S
  have : ν.IsMulLeftInvariant := by dsimp only [ν, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  let hΓ := isDiscrete_intertwiningRationalSubgroup F p iU j wA
  let E := LeftCosetSpace.measurableEquivOfMulEquiv α Γ Γ hα
  have hpres : MeasurePreserving E measure measure :=
    LeftCosetSpace.measurePreserving_discreteQuotientMeasure α Γ Γ hα hΓ hΓ ν ν
      (measurePreserving_normalizedHaar_of_rational S α hr)
  have hinv : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx => hφ x (Subgroup.mem_sup_left hx)
  have hI (x : LeftCosetSpace Γ) : hK.intertwiningIntegrand iU j w φ lam (a * g) (E x) =
      hK.intertwiningIntegrand iU j w φ lam g x := by
    obtain ⟨v, rfl⟩ := LeftCosetSpace.mk_surjective Γ x
    change hK.intertwiningIntegrand iU j w φ lam (a * g) (LeftCosetSpace.mk Γ (α v)) = _
    rw [hK.intertwiningIntegrand_mk iU j w hU.1.isUnipotent hinv,
      hK.intertwiningIntegrand_mk iU j w hU.1.isUnipotent hinv]
    change hK.parameterTwist φ lam (wA⁻¹ * (a * v.val * a⁻¹) * (a * g)) = _
    rw [show wA⁻¹ * (a * v.val * a⁻¹) * (a * g) =
      (wA⁻¹ * a * wA) * (wA⁻¹ * v.val * g) by group, ← hwz]
    exact hK.parameterTwist_map_rational_mul hφ hl hU lam z _
  have ha : map F M' G (l' ≫ q) mA = a := by rw [map_comp_apply_of_hom, hy]
  rw [show rational F M' m = mA from rfl, ha]
  unfold IsIwasawaCompact.intertwiningOperator IsIwasawaCompact.heightPower
  rw [hK'.height_rational_mul y]
  congr 1
  unfold IsIwasawaCompact.intertwiningIntegral
  rw [← hpres.integral_comp E.measurableEmbedding]
  simp_rw [hI]

include hU hV hφ in
/-- Target radical translations and the principal target Levi preserve the actual
intertwining integral after untwisting. -/
theorem IsIwasawaCompact.intertwiningOperator_leftInvariant
    (hw : IsWeylConjugation p l q l' w c) (hl : IsRationalLeviSubgroup l) :
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F q iV l') T := by
  show parabolicUnipotentImage F q iV ⊔ parabolicLeviRationalImage F q l' ≤ leftStabilizer T
  apply sup_le
  · rintro _ ⟨u, rfl⟩ g
    exact intertwiningOperator_unipotent_mul iU iV π' hK hK' hU hV hφ lam u g
  · rintro _ ⟨m, rfl⟩ g
    exact intertwiningOperator_rationalLevi_mul iU iV π' hK hK' hU hV hφ lam hw hl m g

end Langlands.Global.AdelicGroupPoints

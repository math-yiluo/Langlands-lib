import Langlands.Global.AdelicEisensteinParameterDecay
import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.Global.RepresentedAdelicSubgroupQuotient

/-! # The identity element in the actual global intertwining integral -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G} (iU : U ⟶ P)

private theorem innerAdelicPoint_one_eq :
    innerAdelicPoint F G (1 : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) = 1 := by
  unfold innerAdelicPoint GroupScheme.constantPoint
  rw [MonObj.comp_one]

private theorem intertwiningRationalSubgroup_one_self :
    intertwiningRationalSubgroup F p iU (iU ≫ p) 1 =
      AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iU ≫ p)) := by
  ext v
  rw [mem_intertwiningRationalSubgroup_iff, inv_one, one_mul, mul_one]
  exact and_iff_left v.2

section Integral

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [IsAffine U.X.left]
  [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion (iU ≫ p).hom.hom.left]

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- The identity representative gives the mass-one quotient of the full
unipotent radical used on both sides of the operator. -/
theorem intertwiningMeasure_one_isProbabilityMeasure (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) :
    IsProbabilityMeasure (intertwiningMeasure F p iU (iU ≫ p) 1) := by
  let V := SubgroupFunctor.range (iU ≫ p)
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G V
  let hclosed : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ p)
  let : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G V) :=
    hclosed.locallyCompactSpace
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G V) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (iU ≫ p)
      hU.1.smooth hU.1.connectedSpace hU.1.isUnipotent
  let : IsProbabilityMeasure (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V) :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  have hd (S T : Subgroup (AdelicSubgroupPoints.adelicPoints F G V))
      (hS : _root_.IsDiscrete (S : Set (AdelicSubgroupPoints.adelicPoints F G V)))
      (hT : _root_.IsDiscrete (T : Set (AdelicSubgroupPoints.adelicPoints F G V))) (h : S = T) :
      LeftCosetSpace.fundamentalDomain S hS = LeftCosetSpace.fundamentalDomain T hT := by
    subst T
    rfl
  constructor
  unfold intertwiningMeasure LeftCosetSpace.discreteQuotientMeasure
  rw [LeftCosetSpace.quotientMeasure_univ,
    hd _ _ _ (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G V)
      (intertwiningRationalSubgroup_one_self iU),
    AdelicSubgroupPoints.normalizedHaarMeasure, Measure.smul_apply]
  have hm : AdelicSubgroupPoints.rationalQuotientHaarMeasure F G V Set.univ =
      Measure.haar (LeftCosetSpace.fundamentalDomain Γ
        (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G V)) := by
    unfold AdelicSubgroupPoints.rationalQuotientHaarMeasure LeftCosetSpace.haarQuotientMeasure
      LeftCosetSpace.discreteQuotientMeasure
    rw [LeftCosetSpace.quotientMeasure_univ]
  rw [← hm]
  have hp : AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V Set.univ = 1 :=
    measure_univ
  exact (Measure.smul_apply _ _ _).symm.trans hp

/-- The identity intertwining integral is the original twist, for every
function invariant under the adelic unipotent radical. -/
theorem IsIwasawaCompact.intertwiningIntegral_one_self {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact p K) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (phi : AdelicGroupPoints F G → ℂ)
    (hphi : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) phi)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.intertwiningIntegral iU (iU ≫ p) 1 phi lam g = hK.parameterTwist phi lam g := by
  unfold IsIwasawaCompact.intertwiningIntegral
  have hI : ∀ x, hK.intertwiningIntegrand iU (iU ≫ p) 1 phi lam g x = hK.parameterTwist phi lam g := by
    intro x
    let v := (Quotient.out x :
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p)))
    obtain ⟨y, hy⟩ := v.2
    let y' : AdelicGroupPoints F U := y
    have hy' : map F U G (iU ≫ p) y' = (v : AdelicGroupPoints F G) := hy
    have hm : map F U G (iU ≫ p) y' ∈ parabolicUnipotentImage F p iU := ⟨y', rfl⟩
    change hK.parameterTwist phi lam ((innerAdelicPoint F G 1)⁻¹ * (v : AdelicGroupPoints F G) * g) = _
    rw [innerAdelicPoint_one_eq (F := F) (G := G), inv_one, one_mul]
    rw [← hy']
    unfold IsIwasawaCompact.parameterTwist
    rw [hphi _ hm g, hK.heightPower_unipotent_mul hU.1.isUnipotent]
  have hmass : intertwiningMeasure F p iU (iU ≫ p) (innerAdelicPoint F G 1) Set.univ = 1 := by
    rw [innerAdelicPoint_one_eq (F := F) (G := G)]
    let : IsProbabilityMeasure (intertwiningMeasure F p iU (iU ≫ p) 1) :=
      intertwiningMeasure_one_isProbabilityMeasure iU hU
    exact measure_univ
  simp only [hI, integral_const, Measure.real_def, hmass, ENNReal.toReal_one, one_smul]

end Integral

variable [IsAffineHom G.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {l : M ⟶ P} {a : A.toGrp ⟶ M}

omit [NumberField F] in
/-- The identity Weyl parameter is the identity linear map. -/
theorem weylParameter_one_self (r : ParabolicRootPresentation p l a) (proj : P ⟶ M)
    (hproj : l ≫ proj = 𝟙 M) :
    weylParameter (F := F) l (𝟙 M) proj = LinearMap.id := by
  have hinj : Function.Injective (characterRestrict l) := fun x y heq =>
    characterRestrict_splitComponent_injective r (by
      simp only [characterRestrict_comp, AddMonoidHom.comp_apply, heq])
  apply AlgebraTensorModule.ext
  intro s χ
  rw [weylParameter_tmul, LinearMap.id_apply, Category.id_comp]
  congr 1
  apply hinj
  change ((characterRestrict l).comp (characterRestrict (proj ≫ l))) χ = _
  rw [← characterRestrict_comp, ← Category.assoc, hproj, Category.id_comp]

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [IsAffine U.X.left]
  [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion (iU ≫ p).hom.hom.left]

/-- The normalized identity intertwiner acts as the identity on the inducing
function, with the same radical and compact on source and target. -/
theorem IsIwasawaCompact.intertwiningOperator_one_self {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact p K) (r : ParabolicRootPresentation p l a)
    (proj : P ⟶ M) (hproj : l ≫ proj = 𝟙 M)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (phi : AdelicGroupPoints F G → ℂ)
    (hphi : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) phi)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.intertwiningOperator hK iU l iU (𝟙 M) proj 1 phi lam g = phi g := by
  unfold IsIwasawaCompact.intertwiningOperator
  rw [weylParameter_one_self r proj hproj, LinearMap.id_apply, hK.intertwiningIntegral_one_self iU hU phi hphi]
  unfold IsIwasawaCompact.parameterTwist
  have hCancel : hK.heightPower (-lam) g * hK.heightPower lam g = 1 := by
    simp only [IsIwasawaCompact.heightPower, map_neg, LinearMap.neg_apply, ← Complex.exp_add,
      neg_add_cancel, Complex.exp_zero]
  calc
    _ = (hK.heightPower (-lam) g * hK.heightPower lam g) * phi g := by ring
    _ = _ := by rw [hCancel, one_mul]

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The identity term for the actual normalized adelic intertwining operator
with the same source and target data. -/
def IntertwiningIdentityStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F]
    {G P M U : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    [IsAffine P.X.left] [IsAffine U.X.left]
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
    (iU : U ⟶ P) [IsClosedImmersion (iU ≫ p).hom.hom.left]
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (proj : P ⟶ M), ParabolicRootPresentation p l a → l ≫ proj = 𝟙 M →
    LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (phi : AdelicGroupPoints F G → ℂ),
      IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) phi →
      ∀ (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G),
        hK.intertwiningOperator hK iU l iU (𝟙 M) proj 1 phi lam g = phi g

theorem intertwiningIdentity : IntertwiningIdentityStatement.{u} := by
  intro F _ _ G P M U _ _ _ _ _ p _ iU _ A l a K hK proj r hproj hU phi hphi lam g
  exact hK.intertwiningOperator_one_self iU r proj hproj hU phi hphi lam g

end Langlands.Global

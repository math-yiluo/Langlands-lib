import Langlands.Global.ArthurTruncation
import Langlands.Global.AdelicSubgroupNormOne
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.UnipotentConnected

/-! # Arthur truncation on the norm-one adelic group

Arthur 2005, (13.1), evaluated on functions on `G(𝔸)^1`. Restrict the published
full-adelic formula using a zero extension. The formula at a norm-one argument
depends only on the original norm-one function: both the rational translates
and the unipotent translates appearing in the formula stay in `G(𝔸)^1`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}

/-- Extend a function on `G(𝔸)^1` by zero to the full adelic group. -/
def normOneExtend (f : normOneSubgroup F G → ℂ) (x : AdelicGroupPoints F G) : ℂ :=
  if hx : x ∈ normOneSubgroup F G then f ⟨x, hx⟩ else 0

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem normOneExtend_coe (f : normOneSubgroup F G → ℂ) (x : normOneSubgroup F G) :
    normOneExtend f x = f x := by
  simp [normOneExtend, x.property]

omit [Mono i.hom.hom.left] in
/-- The actual standard unipotent adelic subgroup is inside the norm-one group.
Its rational quotient is compact. Each logarithmic norm of an ambient
rational character vanishes on principal points and hence on this subgroup. -/
theorem unipotentPoints_le_normOne (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (Standard.unipotentHom i ν J)) ≤
      normOneSubgroup F G := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨⟨ζ, hζ⟩, heq⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  let j := Standard.unipotentHom i ν J
  have hU := Standard.isRepresentedBy_unipotentHom i ν J
  rw [(heq ζ hζ).2.2] at hU
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) :
      Set (AdelicGroupPoints F G)) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j)) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j
      ((dynamicSmooth F G (CommGroupScheme.groupHom ζ ≫ i) _ j).2.2 hU)
      (DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G _ hU)
      (Dynamic.isUnipotent_unipotentRepresentative _ hU)
  exact AdelicSubgroupPoints.adelicPoints_le_normOneSubgroup F G (SubgroupFunctor.range j)

section Truncation

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

/-- Formula (13.1) on `G(𝔸)^1`, using the existing heights, rational cosets and constant terms. -/
def normOneTruncation (Tp : V T) (f : normOneSubgroup F G → ℂ) (x : normOneSubgroup F G) : ℂ :=
  truncation hG hi D hK hρ Tp (normOneExtend f) x

/-- At a norm-one argument, the full-adelic formula gives the same value for
any two inputs agreeing on `G(𝔸)^1`. -/
theorem truncation_congr_on_normOne (hν : IsGenericCocharacter i ν) (Tp : V T)
    {f g : AdelicGroupPoints F G → ℂ} (hfg : Set.EqOn f g (normOneSubgroup F G))
    (x : normOneSubgroup F G) :
    truncation hG hi D hK hρ Tp f x = truncation hG hi D hK hρ Tp g x := by
  unfold truncation
  refine Finset.sum_congr rfl fun S hS => congrArg (_ * ·) ?_
  refine tsum_congr fun δ => congrArg (· * _) ?_
  have hS' : (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    fun _ hb => by simpa only [mem_simpleFinset] using Finset.mem_powerset.mp hS hb
  have hδ := (normOneSubgroup F G).mul_mem
    (rationalSubgroup_le_normOneSubgroup F G (Quotient.out δ : rationalSubgroup F G).property)
    x.property
  unfold constantTerm subgroupConstantTerm
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun n => hfg ((normOneSubgroup F G).mul_mem ?_ hδ)
  exact unipotentPoints_le_normOne hG hi hν hS' (Quotient.out n).property

/-- Zero extension can be replaced by any extension, in particular by the
original full-adelic function when considering its restriction. -/
theorem normOneTruncation_restrict (hν : IsGenericCocharacter i ν) (Tp : V T)
    (f : AdelicGroupPoints F G → ℂ) (x : normOneSubgroup F G) :
    normOneTruncation hG hi D hK hρ Tp (fun y => f y) x = truncation hG hi D hK hρ Tp f x := by
  apply truncation_congr_on_normOne hG hi D hK hρ hν Tp _ x
  intro y hy
  exact normOneExtend_coe (fun z => f z) ⟨y, hy⟩

end Truncation

end Langlands.Global.ArthurTruncation

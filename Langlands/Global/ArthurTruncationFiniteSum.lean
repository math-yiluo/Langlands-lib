import Langlands.Global.ArthurNormOneTruncation
import Langlands.Global.ArthurTruncationFinitenessProof
import Langlands.Global.AdelicParabolicConstantTermAutomorphy
import Langlands.Representation.LanglandsClassification.StandardParabolicDatum

/-! # Finite sums and Arthur truncation -/

noncomputable section

set_option autoImplicit false

universe u v

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open GroupScheme RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces
  EisensteinConstantTerm Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}

private theorem subgroupConstantTerm_finsetSum
    {U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left]
    (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (hs : Smooth U.X.hom) (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    {I : Type v} (s : Finset I) (f : I → AdelicGroupPoints F G → ℂ)
    (hf : ∀ a ∈ s, Continuous (f a))
    (hi : ∀ a ∈ s, IsLeftInvariantUnder F G (rationalSubgroup F G) (f a))
    (g : AdelicGroupPoints F G) :
    subgroupConstantTerm F j (fun x => ∑ a ∈ s, f a x) g =
      ∑ a ∈ s, subgroupConstantTerm F j (f a) g := by
  unfold subgroupConstantTerm
  apply integral_finsetSum
  intro a ha
  exact integrable_subgroupConstantTermIntegrand j hs hc hu (hf a ha)
    (fun r hr x => hi a ha r (rationalImage_le_rationalSubgroup j hr) x) g

/-- Arthur truncation commutes with pointwise finite sums of continuous functions on
`G(𝔸)` invariant under left multiplication by `G(F)`. -/
def TruncationFiniteSumStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (_hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) (Tp : V T)
    {I : Type v} (s : Finset I) (f : I → AdelicGroupPoints F G → ℂ),
    (∀ a ∈ s, Continuous (f a)) →
    (∀ a ∈ s, IsLeftInvariantUnder F G (rationalSubgroup F G) (f a)) →
    ∀ g : AdelicGroupPoints F G,
      truncation hG hi D hK hρ Tp (fun x => ∑ a ∈ s, f a x) g =
        ∑ a ∈ s, truncation hG hi D hK hρ Tp (f a) g

/-- First use additivity of the integrals on the unipotent quotients, then commute
finite sums using the same cutoff support for each member of the family. -/
theorem truncation_finsetSum : TruncationFiniteSumStatement.{u, v} := by
  classical
  intro F _ _ G _ _ T i _ ν hG hi hν D K hK hρ Tp I s f hf hfi g
  let roots := simpleFinset ν hG hi
  let Q (S : Finset (characterLattice T)) :=
    ParabolicRationalCosets F (Standard.parabolicHom i ν (S : Set (characterLattice T)))
  let x (S : Finset (characterLattice T)) (c : Q S) : AdelicGroupPoints F G :=
    (c.out : rationalSubgroup F G).val * g
  let w (S : Finset (characterLattice T)) (c : Q S) :=
    ArthurRelative.tauHat hG hi ν D (S : Set (characterLattice T)) (simpleRelativeRoots i ν)
      (height hi hK hρ (x S c) - Tp)
  let series (S : Finset (characterLattice T)) (φ : AdelicGroupPoints F G → ℂ) :=
    ∑' c : Q S, constantTerm F i ν (S : Set (characterLattice T)) φ (x S c) * (w S c : ℂ)
  let sign (S : Finset (characterLattice T)) : ℂ := (-1) ^ (roots.card - S.card)
  change (∑ S ∈ roots.powerset, sign S * series S (fun x => ∑ a ∈ s, f a x)) =
    ∑ a ∈ s, ∑ S ∈ roots.powerset, sign S * series S (f a)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hS' : (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    fun _ ha => (mem_simpleFinset hG hi).mp (Finset.mem_powerset.mp hS ha)
  have hU := (Standard.parabolicStructure i ν hG hi hν _ hS').2.2.1.1
  have hfin : {c : Q S | w S c ≠ 0}.Finite :=
    truncationFiniteness F G T i ν hG hi hν D K hK hρ S hS Tp g
  have hseries (φ : AdelicGroupPoints F G → ℂ) :
      series S φ = ∑ c ∈ hfin.toFinset,
        constantTerm F i ν (S : Set (characterLattice T)) φ (x S c) * (w S c : ℂ) := by
    apply tsum_eq_sum
    intro c hc
    have hw : w S c = 0 := by
      simpa only [hfin.mem_toFinset, Set.mem_ofPred_eq, ne_eq, not_not] using hc
    rw [hw, Int.cast_zero, mul_zero]
  rw [← Finset.mul_sum]
  congr 1
  simp only [hseries]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_mul]
  exact congrArg (· * (w S c : ℂ))
    (subgroupConstantTerm_finsetSum (Standard.unipotentHom i ν S)
      hU.smooth hU.connectedSpace hU.isUnipotent s f hf hfi (x S c))

/-- The same finite-sum identity for restrictions of full adelic functions to
`G(𝔸)¹`. -/
theorem normOneTruncation_finsetSum
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) (Tp : V T)
    {I : Type v} (s : Finset I) (f : I → AdelicGroupPoints F G → ℂ)
    (hf : ∀ a ∈ s, Continuous (f a))
    (hfi : ∀ a ∈ s, IsLeftInvariantUnder F G (rationalSubgroup F G) (f a))
    (g : normOneSubgroup F G) :
    normOneTruncation hG hi D hK hρ Tp (fun x => ∑ a ∈ s, f a x) g =
      ∑ a ∈ s, normOneTruncation hG hi D hK hρ Tp (fun x => f a x) g := by
  rw [normOneTruncation_restrict hG hi D hK hρ hν Tp (fun x => ∑ a ∈ s, f a x)]
  simp only [normOneTruncation_restrict hG hi D hK hρ hν]
  exact truncation_finsetSum hG hi hν D hK hρ Tp s f hf hfi g

end Langlands.Global.ArthurTruncation

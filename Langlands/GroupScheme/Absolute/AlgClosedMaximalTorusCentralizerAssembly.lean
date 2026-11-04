import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerReduction
import Langlands.GroupScheme.Absolute.RegularCocharacterSolvable
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientStatement
import Langlands.GroupScheme.Absolute.UnipotentPointsSolvable
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.FieldCentralizerRepresentabilityProof
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.RootSubgroupVectorTransport
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.Torus.CentralMaximalQuotientProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.NoTorusBaseChangeReduction
import Langlands.GroupScheme.Torus.NoTorusUnipotentStatement
import Langlands.GroupScheme.Torus.SplitReflection

/-! # Maximal tori over an algebraically closed field are self-centralizing, from structural
inputs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Central

variable {k : Type u} [Field k]

/-- An extension of a group of points with solvable quotient by a commutative kernel is
solvable: if `q : M ⟶ Q` is an fppf quotient whose kernel is the range of `s : T ⟶ M` with `T`
commutative, and the points of `Q` over `U` form a solvable group, so do the points of `M`. -/
theorem isSolvable_points_of_isFppfQuotient {M Q : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {s : T.toGrp ⟶ M} {q : M ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range s) q)
    (U : Over (Spec (CommRingCat.of k))) [Group.IsSolvable (U ⟶ Q.X)] :
    Group.IsSolvable (U ⟶ M.X) := by
  have : Group.IsSolvable ((yonedaGrp.obj T.toGrp).obj (op U)) :=
    Group.isSolvable_of_comm fun a b => mul_comm (G := U ⟶ T.X) a b
  have : Group.IsSolvable ((yonedaGrp.obj Q).obj (op U)) := ‹Group.IsSolvable (U ⟶ Q.X)›
  refine Group.isSolvable_of_ker_le_range ((yonedaGrp.map s).app (op U)).hom
    ((yonedaGrp.map q).app (op U)).hom fun x hx => ?_
  have hx : x ≫ q.hom.hom = 1 := hx
  change x ∈ (SubgroupFunctor.range s).carrier U
  rw [← hq.2.2.2, mem_range_kernelι_iff]
  exact hx

variable [IsAlgClosed k]

/-- **A connected reductive group with a central maximal torus is that torus.** Over an
algebraically closed field, let `s : T ⟶ M` be a central maximal torus of a connected reductive
group `M`. Assuming Milne 17.81 (`NoTorusUnipotentStatement`) and Milne 16.33(a),(c)
(`SolvableTorusQuotientStatement`), `s` is an isomorphism. -/
theorem IsConnectedReductive.isIso_of_isCentral_of_isMaximalTorus
    (hunip : NoTorusUnipotentStatement.{u}) (hsplit : SolvableTorusQuotientStatement.{u})
    {M : GroupScheme (Spec (CommRingCat.of k))} (hM : IsConnectedReductive M)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {s : T.toGrp ⟶ M} (hc : IsCentral s)
    (hs : IsMaximalTorus s) : IsIso s := by
  have := hM.smooth
  have := hM.isAffineHom
  have := hM.connectedSpace
  -- The quotient `Q = M/T` is a smooth connected affine group without tori, hence unipotent.
  obtain ⟨Q, q, hQs, hQa, hq⟩ :=
    normalSubgroupQuotient k M T.toGrp s hs.2.1 hc.range_isNormal
  have : Smooth Q.X.hom := hQs
  have : IsAffineHom Q.X.hom := hQa
  have : Surjective q.hom.hom.left := hq.2.1
  have : ConnectedSpace Q.X.left :=
    Function.Surjective.connectedSpace q.hom.hom.left.surjective q.hom.hom.left.continuous
  have hQ : IsUnipotent Q := hunip k Q (centralMaximalTorusQuotientStatement k M T s hc hs Q q hq)
  -- So `M` is an extension of a unipotent group by a torus, hence solvable.
  have : Group.IsSolvable (algebraicClosurePoint k ⟶ Q.X) :=
    isSolvable_points_of_isUnipotent hQ _
  have hsolv : IsSolvableGroupScheme M :=
    isSolvableGroupScheme_of_isSolvable_points (isSolvable_points_of_isFppfQuotient hq _)
  -- Its unipotent part is a smooth connected unipotent normal subgroup, hence trivial, so `M`
  -- is isomorphic to its split torus quotient.
  obtain ⟨U, D, u, p, hu, hUs, hUc, hUu, hUn, hp, hD⟩ := hsplit k M hsolv
  have hbot : SubgroupFunctor.range u = ⊥ :=
    hM.hasTrivialUnipotentRadical U u hu hUs hUc hUu hUn
  rw [hbot] at hp
  -- A maximal torus of a torus is the whole torus.
  exact hs.isIso_of_torus (hD.of_iso hp.isoOfBot).isTorus

end Central

/-- The algebraically closed case of Milne 17.61(a) from three structural inputs: dynamic
centralizers of cocharacters of connected reductive groups are connected reductive, a smooth
connected group without tori is unipotent (Milne 17.81), and a smooth connected solvable group has
a smooth connected normal unipotent subgroup with split torus quotient (Milne 16.33(a),(c)). -/
def AlgClosedMaximalTorusCentralizerReductionStatement : Prop :=
  DynamicCentralizerReductiveStatement.{u} → NoTorusUnipotentStatement.{u} →
    SolvableTorusQuotientStatement.{u} → AlgClosedMaximalTorusCentralizerStatement.{u}

/-- The centralizer of a maximal torus `T` is the dynamic centralizer of a generic cocharacter of
`T`, hence connected reductive, and `T` is a central maximal torus in it. -/
theorem algClosedMaximalTorusCentralizerReduction :
    AlgClosedMaximalTorusCentralizerReductionStatement.{u} := by
  intro hreductive hunip hsplit k _ _ G hG T j hj
  have := hG.isAffineHom
  have := hG.smooth
  -- Over an algebraically closed field `T` is split, so `C_G(T) = Z(ν)` for a generic `ν`.
  have hTs : IsSplitTorus T.toGrp :=
    hj.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨ν, hν⟩ := hTs.exists_genericCocharacter j
  have hZ := genericCentralizer k G hG T j (hj.isMaximalSplitTorus hTs) ν hν
  obtain ⟨C, c, hc, hcc⟩ :=
    fieldCentralizerRepresentability k T G (hj.2.1.isAffineHom : IsAffineHom T.toGrp.X.hom) j
  have hC : IsConnectedReductive C :=
    hreductive k G hG (CommGroupScheme.groupHom ν ≫ j) C c hcc (by rw [hZ]; exact hc)
  -- The factor `t : T ⟶ C` of `j` is a central maximal torus of `C`.
  set t := torusCentralizerFactor j hc
  have ht : t ≫ c = j := torusCentralizerFactor_comp j hc
  have htm : IsMaximalTorus t := by
    refine ⟨hj.1, isClosedSubgroup_torusCentralizerFactor j hc hcc hj.2.1, ?_⟩
    intro T' i' f hT' hi' hf
    exact hj.2.2 T' (i' ≫ c) f hT' (hi'.comp hcc) (by rw [← Category.assoc, hf, ht])
  have := hC.isIso_of_isCentral_of_isMaximalTorus hunip hsplit
    (isCentral_torusCentralizerFactor j hc) htm
  -- So the centralizer `range c` is `range (t ≫ c) = range j`.
  rw [← hc.2, ← ht]
  exact (SubgroupFunctor.range_iso_comp (asIso t) c).symm

/-- **Milne 17.84 from structural inputs.** Every maximal torus of a connected reductive group
over a field is its own centralizer, given the dynamic-centralizer reductivity statement, Milne
17.81 and Milne 16.33(a),(c). -/
theorem maximalTorusCentralizer_of_structuralInputs
    (hreductive : DynamicCentralizerReductiveStatement.{u})
    (hunip : NoTorusUnipotentStatement.{u})
    (hsplit : SolvableTorusQuotientStatement.{u}) :
    MaximalTorusCentralizerStatement.{u} :=
  maximalTorusCentralizer_of_centralMaximalTorusBaseChange
    (centralMaximalTorusBaseChangeReduction normalSubgroupQuotient
      centralMaximalTorusQuotientStatement (noTorusBaseChangeReduction hunip))
    (algClosedMaximalTorusCentralizerReduction hreductive hunip hsplit)

end Langlands.GroupScheme

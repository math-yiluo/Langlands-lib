import Langlands.GroupScheme.Rational.TorusUnipotentQuotientConjugacy
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed
import Langlands.GroupScheme.Torus.MaximalAmbient

/-! # Maximal tori over a torus quotient with a homomorphic section -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section General

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
    (q : G ⟶ Q) (s : Q ⟶ G) (hs : s ≫ q = 𝟙 Q) (hQ : IsTorus Q)
    (hcompare : ∀ j : T.toGrp ⟶ G,
      i ≫ q = j ≫ q → SubgroupConjugate i j)

include hi hs hQ hcompare in
/-- A homomorphic torus section and equal-map conjugacy force the projection
of every maximal torus to be an isomorphism onto the whole quotient. -/
theorem IsMaximalTorus.isIso_comp_of_torus_section : IsIso (i ≫ q) := by
  have : Mono s.hom.hom :=
    mono_of_mono_fac (congrArg (fun a => a.hom.hom) hs)
  have : IsAffine Q.X.left := SplittingAssembly.isAffine_of_isTorus Q hQ
  have : IsAffineHom Q.X.hom := inferInstance
  have hclosed : IsClosedSubgroup s := hQ.isClosedSubgroup_of_mono s
  have heq : i ≫ q = ((i ≫ q) ≫ s) ≫ q := by
    rw [Category.assoc, hs, Category.comp_id]
  have hmax : IsMaximalTorus ((i ≫ q) ≫ s) :=
    (hcompare ((i ≫ q) ≫ s) heq).isMaximalTorus_iff.mp hi
  let U : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { Q with comm := hQ.isCommMonObj }
  exact hmax.2.2 U s (i ≫ q) hQ hclosed rfl

/-- The actual isomorphism from a maximal torus to its torus quotient. -/
def IsMaximalTorus.torusQuotientIsoOfSection : T.toGrp ≅ Q :=
  letI := hi.isIso_comp_of_torus_section q s hs hQ hcompare
  asIso (i ≫ q)

@[simp]
theorem IsMaximalTorus.torusQuotientIsoOfSection_hom :
    (hi.torusQuotientIsoOfSection q s hs hQ hcompare).hom = i ≫ q :=
  rfl

end General

section SplitUnipotent

variable
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u})
    {k : Type u} [Field k]
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    (hN : IsUnipotent N) (hNsplit : RelativeRoot.IsSplitUnipotent N)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (s : Q ⟶ G) (hs : s ≫ q = 𝟙 Q) (hQ : IsTorus Q)
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')

/-- The maximal torus maps isomorphically onto the torus quotient, using
split-unipotent conjugacy for the equal-quotient-map comparison. -/
def IsMaximalTorus.splitUnipotentTorusQuotientIso : T.toGrp ≅ Q :=
  hi.torusQuotientIsoOfSection q s hs hQ (fun j hj =>
    subgroupConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements
      hstable hlinear splitUnipotentAffineTorsorStatement n hn
      inferInstance inferInstance hN hNsplit q hq i j hj hi.1)

@[simp]
theorem IsMaximalTorus.splitUnipotentTorusQuotientIso_hom :
    (hi.splitUnipotentTorusQuotientIso
      hstable hlinear n hn hN hNsplit q hq s hs hQ).hom = i ≫ q :=
  rfl

/-- An actual source isomorphism of maximal tori, with equal maps into
the original torus quotient. -/
def IsMaximalTorus.isoOverSplitUnipotentTorusQuotient : T.toGrp ≅ T'.toGrp :=
  hi.splitUnipotentTorusQuotientIso hstable hlinear n hn hN hNsplit q hq s hs hQ ≪≫
    (hi'.splitUnipotentTorusQuotientIso
      hstable hlinear n hn hN hNsplit q hq s hs hQ).symm

theorem IsMaximalTorus.isoOverSplitUnipotentTorusQuotient_hom_comp :
    (hi.isoOverSplitUnipotentTorusQuotient
      hstable hlinear n hn hN hNsplit q hq s hs hQ hi').hom ≫ (i' ≫ q) = i ≫ q := by
  change
    (hi.splitUnipotentTorusQuotientIso
      hstable hlinear n hn hN hNsplit q hq s hs hQ ≪≫
      (hi'.splitUnipotentTorusQuotientIso
        hstable hlinear n hn hN hNsplit q hq s hs hQ).symm).hom ≫
      (hi'.splitUnipotentTorusQuotientIso
        hstable hlinear n hn hN hNsplit q hq s hs hQ).hom =
    (hi.splitUnipotentTorusQuotientIso
      hstable hlinear n hn hN hNsplit q hq s hs hQ).hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Actual conjugacy data with a rational point of the specified kernel,
rather than merely an ambient rational conjugating point. -/
structure SplitUnipotentTorusQuotientConjugacyData
    {k : Type u} [Field k]
    {N G H H' : GroupScheme (Spec (CommRingCat.of k))}
    (n : N ⟶ G) (i : H ⟶ G) (i' : H' ⟶ G) where
  sourceIso : H ≅ H'
  kernelPoint : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X
  conjugates : i ≫ (G.innerIso (kernelPoint ≫ n.hom.hom)).hom = sourceIso.hom ≫ i'

/-- Construct a rational kernel conjugator and the exact source isomorphism
for maximal tori over a supplied split-unipotent torus quotient section. -/
def IsMaximalTorus.splitUnipotentTorusQuotientConjugacy :
    SplitUnipotentTorusQuotientConjugacyData n i i' := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom := HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  let e := hi.isoOverSplitUnipotentTorusQuotient
    hstable hlinear n hn hN hNsplit q hq s hs hQ hi'
  have he : i ≫ q = (e.hom ≫ i') ≫ q := by
    rw [Category.assoc]
    exact (hi.isoOverSplitUnipotentTorusQuotient_hom_comp
      hstable hlinear n hn hN hNsplit q hq s hs hQ hi').symm
  exact ⟨e,
    QuotientHomCocycle.splitUnipotentTorusConjugator
      hstable hlinear splitUnipotentAffineTorsorStatement
      n q hq.2.2.2.symm hN hNsplit i (e.hom ≫ i') he hi.1,
    QuotientHomCocycle.splitUnipotentTorusConjugator_conjugates
      hstable hlinear splitUnipotentAffineTorsorStatement
      n q hq.2.2.2.symm hN hNsplit i (e.hom ≫ i') he hi.1⟩

include hstable hlinear hn hN hNsplit hq hs hQ in
/-- A split-unipotent extension of a torus with a homomorphic section has
rationally conjugate maximal tori, conditional on stable vectors and
torus-action linearization alone. -/
theorem maximalToriAreConjugate_of_splitUnipotent_torus_section :
    MaximalToriAreConjugate G := by
  intro T T' i i' hi hi'
  let D := hi.splitUnipotentTorusQuotientConjugacy
    hstable hlinear n hn hN hNsplit q hq s hs hQ hi'
  exact ⟨D.kernelPoint ≫ n.hom.hom, D.sourceIso, D.conjugates⟩

end SplitUnipotent

end Langlands.GroupScheme

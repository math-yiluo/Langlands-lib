import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly
import Langlands.GroupScheme.Absolute.NoCocharacterUnipotent

/-! # Algebraically closed maximal-torus centralizers from two structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Central

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, only the solvable torus quotient
statement is needed to identify a central maximal torus in a reductive group. -/
theorem IsConnectedReductive.isIso_of_central_maximalTorus_of_solvableQuotient
    (hsplit : SolvableTorusQuotientStatement.{u})
    {M : GroupScheme (Spec (CommRingCat.of k))} (hM : IsConnectedReductive M)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {s : T.toGrp ⟶ M}
    (hc : IsCentral s) (hs : IsMaximalTorus s) : IsIso s := by
  have := hM.smooth
  have := hM.isAffineHom
  have := hM.connectedSpace
  obtain ⟨Q, q, hQs, hQa, hq⟩ :=
    normalSubgroupQuotient k M T.toGrp s hs.2.1 hc.range_isNormal
  have : Smooth Q.X.hom := hQs
  have : IsAffineHom Q.X.hom := hQa
  have : Surjective q.hom.hom.left := hq.2.1
  have : ConnectedSpace Q.X.left :=
    Function.Surjective.connectedSpace q.hom.hom.left.surjective q.hom.hom.left.continuous
  have hQ : IsUnipotent Q :=
    (HasNoNontrivialClosedTorus.of_forall_hom
      (centralMaximalTorusQuotientStatement k M T s hc hs Q q hq)).isUnipotent
  have : Group.IsSolvable (algebraicClosurePoint k ⟶ Q.X) :=
    isSolvable_points_of_isUnipotent hQ _
  have hsolv : IsSolvableGroupScheme M :=
    isSolvableGroupScheme_of_isSolvable_points (isSolvable_points_of_isFppfQuotient hq _)
  obtain ⟨U, D, i, p, hi, hUs, hUc, hUu, hUn, hp, hD⟩ := hsplit k M hsolv
  have hbot : SubgroupFunctor.range i = ⊥ :=
    hM.hasTrivialUnipotentRadical U i hi hUs hUc hUu hUn
  rw [hbot] at hp
  exact hs.isIso_of_torus (hD.of_iso hp.isoOfBot).isTorus

/-- The original inclusion of a central maximal torus is an actual isomorphism,
retaining the solvable quotient statement as its structural premise. -/
def centralMaximalTorusIsoOfSolvableQuotient
    (hsplit : SolvableTorusQuotientStatement.{u})
    {M : GroupScheme (Spec (CommRingCat.of k))} (hM : IsConnectedReductive M)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (s : T.toGrp ⟶ M)
    (hc : IsCentral s) (hs : IsMaximalTorus s) : T.toGrp ≅ M := by
  let : IsIso s :=
    hM.isIso_of_central_maximalTorus_of_solvableQuotient hsplit hc hs
  exact asIso s

/-- The isomorphism's forward map is the given central maximal torus inclusion. -/
theorem centralMaximalTorusIsoOfSolvableQuotient_hom
    (hsplit : SolvableTorusQuotientStatement.{u})
    {M : GroupScheme (Spec (CommRingCat.of k))} (hM : IsConnectedReductive M)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (s : T.toGrp ⟶ M)
    (hc : IsCentral s) (hs : IsMaximalTorus s) :
    (centralMaximalTorusIsoOfSolvableQuotient hsplit hM s hc hs).hom = s := rfl

end Central

/-- Dynamic centralizer reductivity and solvable torus quotients imply the
exact algebraically closed maximal-torus self-centralization statement. -/
def AlgClosedMaximalTorusCentralizerFromQuotientStatement : Prop :=
  DynamicCentralizerReductiveStatement.{u} →
    SolvableTorusQuotientStatement.{u} →
      AlgClosedMaximalTorusCentralizerStatement.{u}

/-- The no-torus unipotence needed by the centralizer assembly is already a
theorem over algebraically closed fields, so no arbitrary-field input is needed. -/
theorem algClosedMaximalTorusCentralizer_fromQuotient :
    AlgClosedMaximalTorusCentralizerFromQuotientStatement.{u} := by
  intro hreductive hsplit k _ _ G hG T j hj
  have := hG.isAffineHom
  have := hG.smooth
  have hTs : IsSplitTorus T.toGrp :=
    hj.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨ν, hν⟩ := hTs.exists_genericCocharacter j
  have hZ := genericCentralizer k G hG T j (hj.isMaximalSplitTorus hTs) ν hν
  obtain ⟨C, c, hc, hcc⟩ :=
    fieldCentralizerRepresentability k T G (hj.2.1.isAffineHom : IsAffineHom T.toGrp.X.hom) j
  have hC : IsConnectedReductive C :=
    hreductive k G hG (CommGroupScheme.groupHom ν ≫ j) C c hcc (by rw [hZ]; exact hc)
  set t := torusCentralizerFactor j hc
  have ht : t ≫ c = j := torusCentralizerFactor_comp j hc
  have htm : IsMaximalTorus t := by
    refine ⟨hj.1, isClosedSubgroup_torusCentralizerFactor j hc hcc hj.2.1, ?_⟩
    intro T' i' f hT' hi' hf
    exact hj.2.2 T' (i' ≫ c) f hT' (hi'.comp hcc) (by rw [← Category.assoc, hf, ht])
  have := hC.isIso_of_central_maximalTorus_of_solvableQuotient hsplit
    (isCentral_torusCentralizerFactor j hc) htm
  rw [← hc.2, ← ht]
  exact (SubgroupFunctor.range_iso_comp (asIso t) c).symm

end Langlands.GroupScheme

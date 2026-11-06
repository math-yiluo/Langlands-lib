import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedCorootComparisonStatement
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerSubgroupTori
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCorootFace
import Langlands.GroupScheme.Rational.DerivedRootDatumComparison
import Langlands.GroupScheme.Rational.DerivedTorusCentralComplement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement

/-! # Assembly of the actual derived-centralizer coroot comparison -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w z

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A base and simple-root support realizing the image of an actual integral
coroot span under a supplied torus map. -/
structure DerivedCorootComparison
    {k : Type u} [Field k]
    {T S : CommGroupScheme (Spec (CommRingCat.of k))}
    {J : Type v} {K : Type w}
    (P : RootDatum J (characterLattice S) (cocharacterLattice S))
    (Q : RootDatum K (characterLattice T) (cocharacterLattice T))
    (e : T ⟶ S) where
  base : P.Base
  support : Set J
  support_subset : support ⊆ (base.support : Set J)
  span_eq : (Q.corootSpan ℤ).map (RealTorusSpace.cocharacterMapInt e) =
    Submodule.span ℤ (P.coroot '' support)

namespace SplitTorusCentralizerSubgroupTorusModel

variable {k : Type u} [Field k]
    {G M D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ G} {j : M ⟶ G} {d : D ⟶ M}
    (C : SplitTorusCentralizerSubgroupTorusModel a j d)
    {J : Type v} {L : Type w} {K : Type z}
    {P : RootDatum J (characterLattice C.rootModel.torus)
      (cocharacterLattice C.rootModel.torus)}
    {R : RootDatum L (characterLattice C.rootModel.torus)
      (cocharacterLattice C.rootModel.torus)}
    {Q : RootDatum K (characterLattice C.subgroupTorus)
      (cocharacterLattice C.subgroupTorus)}

/-- Supplied actual root data and centralizer reductivity suffice for the
integral comparison; the central torus complement is constructed internally. -/
theorem exists_corootComparison [Finite J] [P.IsReduced]
    (hA : IsSplitTorus A.toGrp) (hj : (torusCentralizer a).IsRepresentedBy j)
    (hM : IsConnectedReductive M) (hd : IsDerivedSubgroup d)
    (hP : IsRootDatumOf C.rootModel.ambient P)
    (hR : IsRootDatumOf C.rootModel.centralizer R)
    (hQ : IsRootDatumOf C.subgroup Q) :
    ∃ (b : P.Base) (s : Set J), s ⊆ (b.support : Set J) ∧
      (Q.corootSpan ℤ).map (RealTorusSpace.cocharacterMapInt C.inclusion) =
        Submodule.span ℤ (P.coroot '' s) := by
  have : Smooth M.X.hom := hM.smooth
  have : Mono C.rootModel.centralizer.hom.hom.left :=
    C.rootModel.centralizer_maximal.2.1.mono
  have : Finite (weylImage C.rootModel.centralizer) :=
    splitTorusWeylImageFinite k M C.rootModel.torus C.rootModel.isSplit
      C.rootModel.centralizer C.rootModel.centralizer_maximal.2.1
  let Z := derivedTorusCentralComplement C.inclusion C.subgroup
    C.rootModel.centralizer d hM hd
    (C.rootModel.centralizer_maximal.isMaximalSplitTorus C.rootModel.isSplit)
    (C.isMaximal.isMaximalSplitTorus C.isSplit) C.inclusion_comp.symm hR
  have := Z.flat
  have := Z.surjective
  let F := C.rootModel.corootFace hA hj hP hR
  refine ⟨F.base, F.support, F.support_subset, ?_⟩
  exact (hR.map_corootSpan_derived C.inclusion Z.map C.subgroup
    C.rootModel.centralizer d C.inclusion_comp.symm C.isSplit Z.isSplit
    Z.isCentral hd C.rootModel.isSplit hQ).trans F.span_eq

/-- Construct the base and support for the actual derived-centralizer integral
coroot comparison from supplied root data and centralizer reductivity. -/
def corootComparison [Finite J] [P.IsReduced]
    (hA : IsSplitTorus A.toGrp) (hj : (torusCentralizer a).IsRepresentedBy j)
    (hM : IsConnectedReductive M) (hd : IsDerivedSubgroup d)
    (hP : IsRootDatumOf C.rootModel.ambient P)
    (hR : IsRootDatumOf C.rootModel.centralizer R)
    (hQ : IsRootDatumOf C.subgroup Q) :
    DerivedCorootComparison P Q C.inclusion :=
  Classical.choice (by
    obtain ⟨b, s, hs, heq⟩ := C.exists_corootComparison hA hj hM hd hP hR hQ
    exact ⟨⟨b, s, hs, heq⟩⟩)

end SplitTorusCentralizerSubgroupTorusModel

/-- The exact target follows from the two outstanding structural statements.
All compatible tori, central complements and integral comparisons are constructed. -/
theorem splitTorusCentralizerDerivedCorootComparison_of_rootDatumExistence
    (hroot : RootDatumExistenceStatement.{u})
    (hcentralizer : DynamicCentralizerReductiveStatement.{u}) :
    SplitTorusCentralizerDerivedCorootComparisonStatement.{u} := by
  intro k _ _ G hG A a ha M j hj D d hd hD
  have := hG.isAffineHom
  have := hG.smooth
  have := hD.isConnectedReductive.isAffineHom
  have := hD.isConnectedReductive.smooth
  have hjclosed : IsClosedSubgroup j := ha.1.isClosedSubgroup_torusCentralizer a hj
  have := hjclosed.isAffineHom
  have := hjclosed.locallyOfFiniteType
  have hcentralizer' : (Dynamic.centralizer
      (CommGroupScheme.groupHom (centralizingCocharacter ha.1 a) ≫ a)).IsRepresentedBy j := by
    rwa [centralizingCocharacter_spec ha.1 a]
  have hM : IsConnectedReductive M :=
    hcentralizer k G hG _ M j hjclosed hcentralizer'
  let C := splitTorusCentralizerSubgroupTorusModel a ha j hj d hd.1
  obtain ⟨J, hJ, P, hP, hPred⟩ := hroot k G hG C.rootModel.torus
    C.rootModel.isSplit C.rootModel.ambient C.rootModel.ambient_maximal
  obtain ⟨L, _, R, hR, _⟩ := hroot k M hM C.rootModel.torus
    C.rootModel.isSplit C.rootModel.centralizer C.rootModel.centralizer_maximal
  obtain ⟨K, hK, Q, hQ, hQred⟩ := hroot k D hD.isConnectedReductive C.subgroupTorus
    C.isSplit C.subgroup C.isMaximal
  let : Finite J := hJ
  let : P.IsReduced := hPred
  let F := C.corootComparison ha.1 hj hM hd hP hR hQ
  exact ⟨C.rootModel.torus, C.subgroupTorus, C.rootModel.ambient, C.subgroup, C.inclusion,
    C.rootModel.isSplit, C.rootModel.ambient_maximal, C.isSplit, C.isMaximal,
    C.inclusion_closed, C.inclusion_ambient_comp, J, K, hJ, hK, P, Q,
    hP, hPred, hQ, hQred, F.base, F.support, F.support_subset, F.span_eq⟩

end Langlands.GroupScheme

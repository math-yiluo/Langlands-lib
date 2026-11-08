import Langlands.Geometry.Building.RootFieldCoordinatesOfTorus
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerReduction
import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Rational.Statement
import Langlands.GroupScheme.Rational.RelativeRootMultiples
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedGeometricReduction
import Langlands.GroupScheme.Rational.TorusSplitPartTransfer
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Type R1 root field coordinates from the structural statements -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

open Langlands.GroupScheme

/-- Given torus-centralizer existence for one maximal split torus and maximal
split torus conjugacy, every representative of the centralizer of a maximal
split torus of a quasi-split group is a torus. -/
theorem isTorus_of_quasiSplit_torusCentralizer
    (hex : QuasiSplitTorusCentralizerExistenceStatement.{u})
    (hconj : MaximalSplitTorusConjugacyStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsQuasiSplit G)
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i)
    {Z : GroupScheme (Spec (CommRingCat.of k))} {j : Z ⟶ G}
    (hj : (torusCentralizer i).IsRepresentedBy j) :
    IsTorus Z := by
  obtain ⟨A₀, a₀, C, j₀, ha₀, hj₀, -, hC⟩ := hex k G hG
  obtain ⟨g, e, he⟩ := (hconj k G hG.isConnectedReductive).1 A₀ S a₀ i ha₀ hi
  have hj' := hj₀.torusCentralizer_of_iso_square e (G.innerIso g) he
  exact IsTorus.of_iso (SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hj hj') hC

/-- **Type R1 root field coordinates, conditionally.** The published R1 statement
follows from torus-centralizer existence, maximal split torus conjugacy, root datum
existence and the relative root system statement. -/
theorem quasiSplitR1RootFieldCoordinates_of_structuralStatements
    (hex : QuasiSplitTorusCentralizerExistenceStatement.{u})
    (hconj : MaximalSplitTorusConjugacyStatement.{u})
    (hdatum : RootDatumExistenceStatement.{u})
    (hrel : RelativeRootSystemStatement.{u}) :
    QuasiSplitR1RootFieldCoordinatesStatement.{u} := by
  intro k _ G _ hG S i hi Z j hj s hs a ha h2
  subst hs
  have hZ : IsTorus Z := isTorus_of_quasiSplit_torusCentralizer hex hconj hG hi hj
  have hGr := hG.isConnectedReductive
  let : Smooth G.X.hom := hGr.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  have hjc : IsClosedSubgroup j := IsSplitTorus.isClosedSubgroup_torusCentralizer hi.1.1 _ hj
  let T : CommGroupScheme (Spec (CommRingCat.of k)) := { Z with comm := hZ.isCommMonObj }
  let jT : T.toGrp ⟶ G := j
  let f : S ⟶ T := Additive.ofMul s
  let : IsAffineHom T.toGrp.X.hom := hjc.isAffineHom
  let : LocallyOfFiniteType T.toGrp.X.hom := hjc.locallyOfFiniteType
  have hself : torusCentralizer jT = SubgroupFunctor.range jT :=
    le_antisymm ((torusCentralizer_le_of_factor jT (s ≫ j) s rfl).trans hj.2.symm.le)
      (range_le_torusCentralizer jT)
  have hjm : IsMaximalTorus jT := isMaximalTorus_of_torusCentralizer_eq hZ hjc hself
  obtain ⟨K, _, _, _, _, hK⟩ := torusFiniteGaloisSplitting k Z hZ
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  obtain ⟨J, _, P, hP, -⟩ := hdatum K
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)
    (hGr.baseChange_of_algebraicExtension (K := K))
    ((CommGroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T) hK
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map jT)
    (isMaximalTorus_baseChange_of_torusCentralizer_eq K hZ hjc hself)
  let : Mono (s ≫ j).hom.hom.left := hi.isSplitSubtorus.mono
  have hR := hrel k G hGr S (s ≫ j) hi
  have ha' : a ∈ relativeRoots (s ≫ j) := ha.1
  have hhigh : RelativeRoot.HasNoHigherRoots (s ≫ j) a := fun n hn hna => by
    have := hR.eq_one_of_nsmul_mem_of_two_not_mem ha' h2 hna
    omega
  exact ⟨rootFieldCoordinatesOfTorus k K f jT hGr hjm hjc hi hj hK hP ha' hhigh⟩

/-- Chosen root field coordinates for a type R1 root of a quasi-split group, under the
four structural statements. -/
def rootFieldCoordinatesOfStructuralStatements
    (hex : QuasiSplitTorusCentralizerExistenceStatement.{u})
    (hconj : MaximalSplitTorusConjugacyStatement.{u})
    (hdatum : RootDatumExistenceStatement.{u})
    (hrel : RelativeRootSystemStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsQuasiSplit G) {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {Z : GroupScheme (Spec (CommRingCat.of k))} {j : Z ⟶ G}
    (hj : (torusCentralizer i).IsRepresentedBy j) {s : S.toGrp ⟶ Z} (hs : s ≫ j = i)
    {a : characterLattice S} (ha : a ∈ RelativeRoot.indivisibleRoots i)
    (h2 : 2 • a ∉ relativeRoots i) :
    RootFieldCoordinates i j s a :=
  Classical.choice (quasiSplitR1RootFieldCoordinates_of_structuralStatements hex hconj hdatum
    hrel k G hG S i hi Z j hj s hs a ha h2)

end Langlands.Geometry.Building

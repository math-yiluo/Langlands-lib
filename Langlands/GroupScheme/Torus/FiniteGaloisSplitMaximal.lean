import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingStatement
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement
import Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement

/-! # Split maximal tori after a finite Galois extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A group scheme `G` over a field `k` has a split maximal torus: some maximal torus
`i : T ⟶ G` has split source `T`. For a reductive group this is Milne's notion of a splittable
reductive group (*Algebraic Groups*, Definition 19.22). -/
def HasSplitMaximalTorus {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) :
    Prop :=
  ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
    IsSplitTorus T.toGrp ∧ IsMaximalTorus i

/-- Every smooth affine group scheme `G` over a field `k` has a split maximal torus after base
change to some finite Galois extension `K / k`. Finite Galois splitting of tori and invariance of
maximality under field extension are explicit hypotheses. -/
theorem exists_finiteGalois_hasSplitMaximalTorus
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    (hbase : MaximalTorusBaseChangeStatement.{u})
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧ IsGalois k K ∧
      HasSplitMaximalTorus ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) := by
  obtain ⟨T, i, hi⟩ := maximalTorusExistence k G
  obtain ⟨K, _, _, hfin, hgal, hT⟩ := hsplit k T.toGrp hi.1
  exact ⟨K, inferInstance, inferInstance, hfin, hgal,
    (CommGroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T,
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i,
    hT, (hbase k K G T i hi.1 hi.2.1).mp hi⟩

/-- Every semisimple group `G` over a field `k` becomes, after base change to some finite Galois
extension `K / k`, a semisimple group with a split maximal torus. Finite Galois splitting of tori,
invariance of maximality and preservation of semisimplicity under field extension are explicit
hypotheses. -/
theorem exists_finiteGalois_hasSplitMaximalTorus_of_isSemisimple
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    (hbase : MaximalTorusBaseChangeStatement.{u})
    (hss : IsSemisimpleFieldExtensionStatement.{u})
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsSemisimple G) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧ IsGalois k K ∧
      IsSemisimple ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) ∧
      HasSplitMaximalTorus ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) := by
  have : Smooth G.X.hom := hG.isConnectedReductive.smooth
  have : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  obtain ⟨K, _, _, hfin, hgal, hT⟩ := exists_finiteGalois_hasSplitMaximalTorus hsplit hbase G
  exact ⟨K, inferInstance, inferInstance, hfin, hgal, hss k K G hG, hT⟩

end Langlands.GroupScheme

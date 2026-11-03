import Langlands.GroupScheme.Chevalley.UnipotentQuotientDescent
import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionStatement
import Langlands.GroupScheme.UnipotentClosedSubgroupStatement
import Langlands.GroupScheme.Rational.CentralVectorQuotientStatement
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The central smooth quotient from explicit structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Chevalley

/-- An actual affine homogeneous quotient by a smooth closed subgroup, using
the closed-orbit, field-extension and closed-subgroup unipotence statements. -/
def unipotentAffineQuotientOfStructuralStatements
    (hclosed : UnipotentAffineOrbitClosedStatement.{u})
    (hbase : UnipotentFieldExtensionStatement.{u})
    (hsub : UnipotentClosedSubgroupStatement.{u})
    (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] (hG : IsUnipotent G)
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)
    (hi : IsClosedSubgroup i) (hsm : Smooth H.X.hom) :
    HomogeneousQuotientFromEmbedding.AffineHomogeneousQuotient i := by
  let : Smooth H.X.hom := hsm
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  exact unipotentAffineQuotientOfFieldExtension hclosed k (AlgebraicClosure k)
    G H i hi hsm
    (hbase k (AlgebraicClosure k) G inferInstance inferInstance hG)
    (hbase k (AlgebraicClosure k) H inferInstance inferInstance (hsub k G H i hi hG))

end Chevalley

namespace RelativeRoot

/-- The exact published central smooth quotient target follows from the three
explicit structural propositions, over every field at every universe. -/
theorem centralSmoothQuotient_of_structuralStatements
    (hclosed : UnipotentAffineOrbitClosedStatement.{u})
    (hbase : UnipotentFieldExtensionStatement.{u})
    (hsub : UnipotentClosedSubgroupStatement.{u}) :
    CentralSmoothQuotientStatement.{u} := by
  intro k _ G Z z hsm ha hc hG hz hsmZ _hcZ hcentral S _hS b bZ heq d n hd hn hpos
  let : Smooth G.X.hom := hsm
  let : IsAffineHom G.X.hom := ha
  let : ConnectedSpace G.X.left := hc
  let : IsClosedImmersion z.hom.hom.left := hz
  let : Mono z.hom.hom := Over.mono_of_mono_left _
  let D := Chevalley.unipotentAffineQuotientOfStructuralStatements
    hclosed hbase hsub k G hG Z z hz hsmZ
  have hstable : b.IsStable (SubgroupFunctor.range z) :=
    AutomorphicAction.IsEquivariant.isStable_range
      (show bZ.IsEquivariant b z from fun {T} s v => heq T s v)
  exact D.quotient.exists_action_relativeDimension D.affine
    hcentral.range_isNormal hG b hstable hd hn hpos

end RelativeRoot

end Langlands.GroupScheme

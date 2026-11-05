import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Rational.SplitTorusDominationReduction

/-! # Affine commutative quotient data for an actual derived subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G D : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- Choose the smooth affine commutative fppf quotient by a supplied actual
derived subgroup of a smooth affine group over any field. -/
def IsDerivedSubgroup.commutativeQuotientData
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) :
    Σ (Q : CommGroupScheme (Spec (CommRingCat.of k))),
      {q : G ⟶ Q.toGrp //
        Smooth Q.X.hom ∧ IsAffineHom Q.X.hom ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q} := by
  let h := normalSubgroupQuotient k G D d hd.1 hd.isNormal
  let Q := Classical.choose h
  let q := Classical.choose (Classical.choose_spec h)
  have hp := Classical.choose_spec (Classical.choose_spec h)
  have hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q := hp.2.2
  let : IsAffineHom Q.X.hom := hp.2.1
  let : IsAffineHom (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : IsAffineHom q.hom.hom.left := IsAffineHom.of_comp q.hom.hom.left Q.X.hom
  let : QuasiCompact q.hom.hom.left := inferInstance
  let Qc : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { Q with comm := hq.isCommMonObj_of_containsCommutators hd.containsCommutators }
  exact ⟨Qc, q, hp.1, hp.2.1, hq⟩

end Langlands.GroupScheme

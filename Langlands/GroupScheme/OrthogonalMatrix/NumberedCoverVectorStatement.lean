import Langlands.GroupScheme.OrthogonalMatrix.Smooth
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.MultiplicativePointTopology
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # Vector weights of a numbered simply connected split orthogonal cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.OrthogonalMatrix

/-- A simply connected central cover of the split even orthogonal group has a
numbered vector-weight basis, when the fundamental weight at vertex zero kills
its actual torus kernel on every relative test scheme.

The eigenvector identity uses the inverse-right row action and holds over every
commutative coefficient algebra. This is an unproved prerequisite statement. -/
def NumberedCoverVectorStatement : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 4 ≤ n →
    letI := OrthogonalMatrix.smooth_groupScheme (Fin n) (CommRingCat.of k)
    letI := OrthogonalMatrix.isAffineHom_groupScheme (Fin n) (CommRingCat.of k)
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
      (p : SplitPinning G),
      IsSimplyConnected G →
      ∀ (pi : G ⟶ identityComponent
          (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of k))),
        IsCentralIsogeny pi →
        ∀ e : p.base.support ≃ Fin n,
          (∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.D n (e a) (e b)) →
          (∀ v : p.base.support, (e v).val = 0 →
            ∀ chi : characterLattice p.torus,
              latticePairing _ chi (p.rootDatum.coroot v.val) = 1 →
              (∀ w : p.base.support, w ≠ v →
                latticePairing _ chi (p.rootDatum.coroot w.val) = 0) →
              ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ p.torus.X),
                t ≫ (p.inclusion ≫ pi).hom.hom = 1 →
                  t ≫ (CommGroupScheme.groupHom chi).hom.hom = 1) →
          ∃ eps : Fin n → characterLattice p.torus,
            (∀ (a : p.base.support) (h : (e a).val + 1 < n),
              p.rootDatum.root a.val = eps (e a) - eps ⟨(e a).val + 1, h⟩) ∧
            (∀ (a : p.base.support) (h : (e a).val + 1 = n),
              p.rootDatum.root a.val =
                eps ⟨n - 2, by omega⟩ + eps ⟨n - 1, by omega⟩) ∧
            (∀ i j : Fin n, i ≠ j → ∀ s t : ℤˣ, ∃ a : p.rootIndex,
              p.rootDatum.root a = (s : ℤ) • eps i + (t : ℤ) • eps j) ∧
            ∃ b : Basis (Fin n × ℤˣ) k ((Fin n ⊕ Fin n) → k),
              ∀ (R : CommAlgCat.{u} (CommRingCat.of k))
                (t : GroupScheme.affinePoints p.torus.toGrp R) (a : Fin n × ℤˣ),
                Matrix.vecMul (fun j => algebraMap k R (b a j))
                    ((MatrixRepresentation.affineMatrix
                      (pi ≫ identityComponentι
                          (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of k)) ≫
                        inclusion (Fin n) (CommRingCat.of k))
                      R (t ≫ p.inclusion.hom.hom))⁻¹ :
                      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) =
                  fun j =>
                    ((Gm.affineUnitsEquiv (CommRingCat.of k) R
                      (t ≫ (CommGroupScheme.groupHom
                        ((a.2 : ℤ) • eps a.1)).hom.hom) : Rˣ) : R) *
                      algebraMap k R (b a j)

end Langlands.GroupScheme.OrthogonalMatrix

import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.CentralSimpleNormOne
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Actual norm-one presentations of simply connected groups of inner type A

Inner type A is expressed by the actual Cartan pairings and the full
absolute Galois star action of the published Tits-index data. This module
states the classical identification with a central-simple norm-one group;
it supplies no proof of that identification.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Positive absolute rank `n`, an actual numbering of every simple vertex
with the full type-A Cartan matrix, and triviality of the full Galois star
action. There is no algebra or group-classification field. -/
def TitsIndexData.HasInnerTypeA (d : TitsIndexData G) (n : ℕ) : Prop :=
  0 < n ∧
    (∃ e : d.Vertex ≃ Fin n,
      ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) ∧
    ∀ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      d.star σ a = a

/-- A simply connected absolutely almost-simple group of inner type `A_n`
is the actual reduced-norm-one group of a central simple algebra of degree
`n + 1`, over an arbitrary field and in every characteristic. This is an
unproved prerequisite statement, not a supplied presentation premise. -/
def InnerTypeANormOneStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G → d.HasInnerTypeA n →
      ∃ (A : Type u) (_ : Ring A) (_ : Algebra K A)
        (_ : FiniteDimensional K A) (_ : Algebra.IsCentral K A) (_ : IsSimpleRing A),
        Langlands.CentralSimple.reducedDegree K A = n + 1 ∧
          Nonempty (G ≅ CentralSimpleUnits.normOne K A)

end Langlands.GroupScheme

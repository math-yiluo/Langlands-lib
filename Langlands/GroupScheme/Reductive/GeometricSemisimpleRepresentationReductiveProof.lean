import Langlands.GroupScheme.Reductive.GeometricSemisimpleRepresentationReductiveStatement
import Langlands.GroupScheme.Reductive.SemisimpleRepresentationUnipotentProof
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # A geometrically semisimple faithful representation forces reductivity (proof) -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne's Corollary 19.18 follows from Proposition 19.17 (the second conjunct of
`SemisimpleRepresentationUnipotentStatement`) applied over the algebraic closure: the base change
`G_{k^a}` is a connected group variety and `ρ_{k^a}` is a faithful semisimple representation of
it. -/
theorem geometricallySemisimpleRepresentationReductive_of_semisimpleRepresentationUnipotent
    (h : SemisimpleRepresentationUnipotentStatement.{u}) :
    GeometricallySemisimpleRepresentationReductiveStatement.{u} := by
  intro k _ G _ hsm hconn IsSemisimpleRep n ρ hρ _ hρK
  refine ⟨hsm, inferInstance, hconn, ?_⟩
  let b := toAlgebraicClosure k
  have : Smooth G.X.hom := hsm
  have : ConnectedSpace G.X.left := hconn
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have hc : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  have hcl : IsClosedSubgroup (ρ.baseChange b) :=
    (IsClosedSubgroup.baseChange b hρ).comp_iso _
  exact (h (AlgebraicClosure k) ((GroupScheme.baseChange b).obj G)).2 inferInstance hc n
    (ρ.baseChange b) hcl hρK

/-- **A connected group variety with a faithful representation that stays semisimple over an
algebraic closure is reductive** (Milne, *Algebraic Groups* (2017), Corollary 19.18). -/
theorem geometricallySemisimpleRepresentationReductive :
    GeometricallySemisimpleRepresentationReductiveStatement.{u} :=
  geometricallySemisimpleRepresentationReductive_of_semisimpleRepresentationUnipotent
    semisimpleRepresentationUnipotent

end Langlands.GroupScheme

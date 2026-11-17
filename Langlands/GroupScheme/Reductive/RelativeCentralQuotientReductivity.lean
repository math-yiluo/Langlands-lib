import Langlands.GroupScheme.Reductive.CentralQuotientReductiveProof
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Torus.RelativeQuotient

/-! # Reductivity of supplied affine central quotients over arbitrary bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over any scheme, an affine actual fppf quotient of a reductive group
by a subgroup functor contained in its centre is reductive. -/
def AffineCentralQuotientReductivityStatement : Prop :=
  ∀ (S : Scheme.{u}) (G Q : GroupScheme S) (N : SubgroupFunctor G) (q : G ⟶ Q),
    RelativeRoot.IsFppfQuotient N q → IsReductive G → N ≤ center G →
    IsAffineHom Q.X.hom → IsReductive Q

namespace RelativeRoot.IsFppfQuotient

/-- An affine fppf quotient of a reductive group by any central subgroup
functor is reductive over an arbitrary base scheme. -/
theorem isReductive_target_of_central
    {S : Scheme.{u}} {G Q : GroupScheme S} {N : SubgroupFunctor G} {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient N q) (hG : IsReductive G)
    (hN : N ≤ center G) [IsAffineHom Q.X.hom] : IsReductive Q := by
  let : Smooth G.X.hom := hG.smooth
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  let : Smooth Q.X.hom := smooth_target_of_surjective_flat_hom_overBase q
  refine ⟨inferInstance, inferInstance, fun s => ?_⟩
  let b := geometricPoint S s
  have : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom := by
    change IsAffineHom (pullback.snd Q.X.hom b)
    infer_instance
  have : LocallyOfFiniteType ((GroupScheme.baseChange b).obj Q).X.hom := by
    change LocallyOfFiniteType (pullback.snd Q.X.hom b)
    infer_instance
  exact (centralQuotientReductive _ ((GroupScheme.baseChange b).obj G)
    ((GroupScheme.baseChange b).obj Q) ((GroupScheme.baseChange b).map q)
    (N.baseChange b) (hG.isConnectedReductive_baseChange b)
    inferInstance inferInstance (SubgroupFunctor.baseChange_le_center b hN)
    (hq.baseChange b)).isPseudoReductive

end RelativeRoot.IsFppfQuotient

/-- The affine central quotient reductivity proposition follows from
smoothness descent and reductivity on geometric fibres. -/
theorem affineCentralQuotientReductivity : AffineCentralQuotientReductivityStatement.{u} := by
  intro S G Q N q hq hG hN hQ
  exact hq.isReductive_target_of_central hG hN

end Langlands.GroupScheme

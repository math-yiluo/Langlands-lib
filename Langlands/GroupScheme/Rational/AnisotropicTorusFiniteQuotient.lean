import Langlands.GroupScheme.Rational.FiniteQuotientCompactness
import Langlands.GroupScheme.Rational.AnisotropicCompactnessStatement
import Langlands.GroupScheme.Torus.ConnectedReductive

/-! # Anisotropic torus extensions by finite group schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A purely algebraic finite extension of an actual anisotropic torus.
The finite target and its represented fppf quotient are retained as schemes. -/
def HasAnisotropicTorusFiniteQuotient
    (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (T : GroupScheme (Spec (CommRingCat.of k))) (j : T ⟶ G),
    IsTorus T ∧ IsAnisotropic T ∧ IsClosedSubgroup j ∧
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
      IsFinite Q.X.hom ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q

/-- The specified algebraic extension is locally of finite type over the field. -/
theorem HasAnisotropicTorusFiniteQuotient.locallyOfFiniteType
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : HasAnisotropicTorusFiniteQuotient G) : LocallyOfFiniteType G.X.hom := by
  obtain ⟨T, j, hT, ha, hj, Q, q, hQ, hq⟩ := hG
  let : IsFinite Q.X.hom := hQ
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  rw [← Over.w q.hom.hom]
  infer_instance

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

/-- Conditional on the published anisotropic compactness target, an affine
finite extension of an anisotropic torus has compact canonical rational points.
The algebraic hypothesis itself contains no compactness premise. -/
theorem HasAnisotropicTorusFiniteQuotient.compactSpace
    (hcompact : AnisotropicCompactnessStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    (hG : HasAnisotropicTorusFiniteQuotient G) :
    let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    CompactSpace (rationalPoints G) := by
  let : LocallyOfFiniteType G.X.hom := hG.locallyOfFiniteType
  obtain ⟨T, j, hT, ha, hj, Q, q, hQ, hq⟩ := hG
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left j.hom.hom
  let hred := hT.isConnectedReductive_of_fieldSplitting
  let : IsAffineHom T.X.hom := hred.isAffineHom
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
  let : TopologicalSpace (rationalPoints T) := rationalPointTopology F T.X
  let : IsFinite Q.X.hom := hQ
  have hTcompact : CompactSpace (rationalPoints T) :=
    isCompact_univ_iff.mp ((hcompact F T hred).mpr ha)
  exact compactSpace_rationalPoints_of_finite_fppf_quotient
    (SubgroupFunctor.range j) j ⟨inferInstance, rfl⟩ q hq hTcompact

end LocalField

end Langlands.GroupScheme

import Langlands.GroupScheme.Rational.AnisotropicTorusFiniteQuotient
import Langlands.GroupScheme.Rational.AnisotropicTorusCompactness
import Langlands.GroupScheme.Torus.MaximalAmbient

/-! # Compactness of finite extensions of anisotropic tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

/-- An affine finite extension of an anisotropic torus has compact canonical
rational points, using the proved torus norm-kernel compactness theorem. -/
theorem HasAnisotropicTorusFiniteQuotient.isCompact_univ
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    (hG : HasAnisotropicTorusFiniteQuotient G) :
    let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact (Set.univ : Set (rationalPoints G)) := by
  let : LocallyOfFiniteType G.X.hom := hG.locallyOfFiniteType
  obtain ⟨T, j, hT, ha, hj, Q, q, hQ, hq⟩ := hG
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left j.hom.hom
  let hred := hT.isConnectedReductive_of_fieldSplitting
  let : IsAffineHom T.X.hom := hred.isAffineHom
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
  let : Smooth T.X.hom := hred.smooth
  let Tc : CommGroupScheme (Spec (CommRingCat.of F)) :=
    { T with comm := hT.isCommMonObj }
  let : TopologicalSpace (rationalPoints T) := rationalPointTopology F T.X
  let : IsFinite Q.X.hom := hQ
  have hTcompact : CompactSpace (rationalPoints T) :=
    isCompact_univ_iff.mp (ha.isCompact_univ_of_isTorus (T := Tc) hT)
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : CompactSpace (rationalPoints G) :=
    compactSpace_rationalPoints_of_finite_fppf_quotient
      (k := F) (H := T) (G := G) (Q := Q)
      (SubgroupFunctor.range j) j ⟨inferInstance, rfl⟩ q hq hTcompact
  exact _root_.isCompact_univ (X := rationalPoints G)

/-- Affine groups with an actual anisotropic torus and finite schematic
quotient have compact points in the canonical rational-point topology. -/
def AnisotropicTorusFiniteQuotientCompactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left],
    HasAnisotropicTorusFiniteQuotient G →
      let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (Set.univ : Set (rationalPoints G))

/-- Apply torus compactness and the finite attained-image compactness theorem. -/
theorem anisotropicTorusFiniteQuotientCompactness :
    AnisotropicTorusFiniteQuotientCompactnessStatement.{u} := by
  intro F _ _ _ _ G _ hG
  exact hG.isCompact_univ

end Langlands.GroupScheme

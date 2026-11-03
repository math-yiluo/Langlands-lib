import Langlands.GroupScheme.Chevalley.UnipotentOrbit
import Langlands.GroupScheme.AffineClosedOrbit

/-! # Affine homogeneous quotients from unipotent vector orbits -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace HomogeneousQuotientFromEmbedding

/-- A smooth homogeneous quotient together with affineness of its actual scheme. -/
structure AffineHomogeneousQuotient {S : Scheme.{u}} {G H : GroupScheme S}
    (i : H ⟶ G) where
  quotient : HomogeneousQuotient i
  affine : IsAffine quotient.scheme.left

end HomogeneousQuotientFromEmbedding

namespace Chevalley

/-- Kostant–Rosenlicht, as an explicit input, gives an actual affine homogeneous
quotient by any smooth closed unipotent subgroup of a smooth affine unipotent
group over an algebraically closed field. -/
def unipotentAffineQuotient
    (hclosed : UnipotentAffineOrbitClosedStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] (hG : IsUnipotent G)
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)
    (hi : IsClosedSubgroup i) (hsm : Smooth H.X.hom) (hH : IsUnipotent H) :
    HomogeneousQuotientFromEmbedding.AffineHomogeneousQuotient i :=
  Classical.choice (by
    obtain ⟨n, j, ρ, hc, hfib⟩ :=
      exists_closed_affine_vector_orbit hclosed k G hG H i hi hH
    let V := (VectorGroup.groupScheme (CommRingCat.of k) (n + 1)).X
    let a := VectorOrbit.schemeAction ρ
    let x := VectorOrbit.coordinatePoint (CommRingCat.of k) (n + 1) j
      (𝟙_ (Over (Spec (CommRingCat.of k))))
    let : IsAffine V.left := by
      change IsAffine (Spec (CommRingCat.of
        (MvPolynomial (Fin (n + 1)) (CommRingCat.of k))))
      infer_instance
    let : LocallyOfFiniteType V.hom := by
      apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      exact RingHom.finiteType_algebraMap.mpr
        (inferInstance : Algebra.FiniteType (CommRingCat.of k)
          (MvPolynomial (Fin (n + 1)) (CommRingCat.of k)))
    let D := a.quotientOfClosedAffineOrbit x i hi hsm hfib hc
    exact ⟨⟨D, a.quotientOfClosedAffineOrbit_affine x i hi hsm hfib hc⟩⟩)

end Chevalley

end Langlands.GroupScheme

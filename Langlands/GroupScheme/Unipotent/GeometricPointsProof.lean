import Langlands.GroupScheme.Unipotent.GeometricPointsStatement
import Langlands.GroupScheme.Unipotent.RationalPointsProof
import Langlands.GroupScheme.Unipotent.FieldReflectionProof
import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionProof
import Langlands.GroupScheme.Derived.CentralIntersection.Unipotence
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Unipotence of smooth groups through geometric points -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- On a reduced affine group scheme locally of finite type over an algebraically closed field,
the rational points are schematically dense: a closed immersion through which every rational
point factors is an isomorphism. -/
theorem isIso_of_forall_rationalPoint_factors {K : Type u} [Field K] [IsAlgClosed K]
    (H : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] [IsReduced H.X.left]
    (Z : Scheme.{u}) (z : Z ⟶ H.X.left) (hz : IsClosedImmersion z)
    (h : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
      ∃ s : Spec (CommRingCat.of K) ⟶ Z, s ≫ z = g.left) :
    IsIso z := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  apply IsClosedImmersion.isIso_of_injective_of_isAffine
  intro a b hab
  rw [← sub_eq_zero]
  apply CentralIntersection.eq_zero_of_forall_evalPoint_eq_zero
  intro g
  obtain ⟨s, hs⟩ := h g
  have h0 : z.appTop (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  rw [CentralIntersection.evalPoint_apply, ← hs, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    h0, map_zero, map_zero]

/-- Milne 2017, Corollary 14.12: a smooth affine group scheme over a field `k` is unipotent if
and only if every `kᵃ`-point acts by a unipotent matrix in every matrix representation of the
base change to `kᵃ = AlgebraicClosure k`. -/
theorem smoothUnipotentGeometricPoints : SmoothUnipotentGeometricPointsStatement.{u} := by
  intro k _ G _ _
  let K := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let GK := (GroupScheme.baseChange b).obj G
  have : IsAffineHom GK.X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFiniteType GK.X.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd G.X.hom b)
    infer_instance
  have : Smooth GK.X.hom := by
    change Smooth (Limits.pullback.snd G.X.hom b)
    infer_instance
  have : IsReduced GK.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      K GK.X.left GK.X.hom
  have h1410 := perfectFieldUnipotentRationalPoints K GK
  constructor
  · intro hG
    exact h1410.1 (unipotentFieldExtensionStatement k K G inferInstance inferInstance hG)
  · intro hpoints
    apply unipotentFieldReflection k K G
    exact h1410.2 (fun Z z hz hZ => isIso_of_forall_rationalPoint_factors GK Z z hz hZ) hpoints

end Langlands.GroupScheme

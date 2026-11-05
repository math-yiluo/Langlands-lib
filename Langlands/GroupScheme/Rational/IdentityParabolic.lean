import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Reductive.TrivialUnipotentRadical
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Absolute.BorelExistence

/-! # The identity parabolic and its canonical trivial radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The identity of a connected reductive group is an actual parabolic. -/
theorem IsConnectedReductive.isParabolicSubgroup_id (hG : IsConnectedReductive G) :
    IsParabolicSubgroup (𝟙 G) := by
  have := hG.smooth
  have := hG.isAffineHom
  refine ⟨inferInstanceAs (IsClosedImmersion (𝟙 G.X.left)), hG.smooth, ?_⟩
  have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have : LocallyOfFiniteType
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  obtain ⟨B, j, hj⟩ := BorelExistence.exists_isBorelSubgroup
    ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)
  exact ⟨B, j, j, hj, by rw [CategoryTheory.Functor.map_id, Category.comp_id]⟩

/-- The unit subgroup is the geometric unipotent radical of a connected
reductive group, with both ground and algebraic-closure radical conditions. -/
theorem IsConnectedReductive.isGeometricUnipotentRadical_kernelUnit
    (hG : IsConnectedReductive G) :
    LeviSubgroup.IsGeometricUnipotentRadical (kernelUnit G) := by
  have := hG.isAffineHom
  have h₀ := isUnipotentRadical_kernelUnit G hG.hasTrivialUnipotentRadical
  refine ⟨h₀, ?_⟩
  let U := Grp.trivial (Over (Spec (CommRingCat.of k)))
  have : Smooth U.X.hom := h₀.smooth
  have : ConnectedSpace U.X.left := h₀.connectedSpace
  have : IsAffineHom U.X.hom := by
    change IsAffineHom (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  refine ⟨h₀.isClosedSubgroup.baseChange _, ?_,
    connectedSpace_baseChange_of_smooth_affine U (toAlgebraicClosure k),
    h₀.isUnipotent.baseChange, ?_, ?_⟩
  · change Smooth (Limits.pullback.snd U.X.hom (toAlgebraicClosure k))
    infer_instance
  · rw [SubgroupFunctor.range_baseChangeHom]
    exact h₀.isNormal.baseChange _
  · intro H j hj hs hc hu hn
    rw [hG.hasTrivialGeometricUnipotentRadical H j hj hs hc hu hn]
    intro T
    exact bot_le

/-- Multiplication with the canonical identity subgroup is the right unitor. -/
theorem subgroupMultiplication_id_kernelUnit :
    subgroupMultiplication (𝟙 G) (kernelUnit G) = (ρ_ G.X).hom := by
  unfold subgroupMultiplication
  rw [Grp.id_hom_hom, Category.comp_id]
  let U := Grp.trivial (Over (Spec (CommRingCat.of k)))
  have hunit : snd G.X U.X ≫
      (kernelUnit G).hom.hom = 1 := by
    rw [toUnit_unique (snd G.X U.X) (toUnit _)]
    rfl
  rw [hunit, mul_one]
  rfl

/-- The actual multiplication is an isomorphism for the identity Levi. -/
theorem isIso_subgroupMultiplication_id_kernelUnit :
    IsIso (subgroupMultiplication (𝟙 G) (kernelUnit G)) := by
  rw [subgroupMultiplication_id_kernelUnit]
  exact (ρ_ G.X).isIso_hom

/-- The identity is a rational Levi with a matching geometric radical. -/
theorem IsConnectedReductive.isRationalLeviSubgroup_id (hG : IsConnectedReductive G) :
    IsRationalLeviSubgroup (𝟙 G) :=
  ⟨hG.isAffineHom, inferInstanceAs (IsClosedImmersion (𝟙 G.X.left)), hG,
    Grp.trivial _, kernelUnit G, hG.isGeometricUnipotentRadical_kernelUnit,
      isIso_subgroupMultiplication_id_kernelUnit⟩

/-- The canonical identity-parabolic data used by actual Jacquet restriction. -/
structure IdentityParabolicData (G : GroupScheme (Spec (CommRingCat.of k))) : Type u where
  isParabolic : IsParabolicSubgroup (𝟙 G)
  isLevi : IsRationalLeviSubgroup (𝟙 G)
  isRadical : LeviSubgroup.IsGeometricUnipotentRadical (kernelUnit G)
  multiplication_isIso : IsIso (subgroupMultiplication (𝟙 G) (kernelUnit G))

/-- Every connected reductive group has canonical identity-parabolic data. -/
def identityParabolicData (hG : IsConnectedReductive G) : IdentityParabolicData G :=
  ⟨hG.isParabolicSubgroup_id, hG.isRationalLeviSubgroup_id,
    hG.isGeometricUnipotentRadical_kernelUnit, isIso_subgroupMultiplication_id_kernelUnit⟩

end Langlands.GroupScheme

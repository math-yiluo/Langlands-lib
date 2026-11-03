import Langlands.GroupScheme.Reductive.Basic
import Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent

/-! # Geometric connectedness of connected group schemes over a field -/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private def relativePointsEquiv {R : Type u} [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t G.X.hom ≃ (Over.mk t ⟶ G.X) :=
  schemeHomOverEquivOverHom t G.X.hom

/-- The actual pointwise group law, expressed in the relative group-law interface. -/
def relativeGroupLaw {R : Type u} [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) :
    GoodReductionJacobian.RelativeGroupLaw R G.X.hom where
  mul t x y := (relativePointsEquiv G t).symm
    (relativePointsEquiv G t x * relativePointsEquiv G t y)
  one t := (relativePointsEquiv G t).symm 1
  inv t x := (relativePointsEquiv G t).symm (relativePointsEquiv G t x)⁻¹
  mul_assoc t x y z := by
    apply (relativePointsEquiv G t).injective
    simp only [Equiv.apply_symm_apply, mul_assoc]
  one_mul t x := by
    apply (relativePointsEquiv G t).injective
    simp only [Equiv.apply_symm_apply, one_mul]
  mul_one t x := by
    apply (relativePointsEquiv G t).injective
    simp only [Equiv.apply_symm_apply, mul_one]
  inv_mul_cancel t x := by
    apply (relativePointsEquiv G t).injective
    simp only [Equiv.apply_symm_apply, inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply (relativePointsEquiv G t').injective
    change (Over.homMk ψ hψ : Over.mk t' ⟶ Over.mk t) ≫
        (relativePointsEquiv G t x * relativePointsEquiv G t y) =
      ((Over.homMk ψ hψ : Over.mk t' ⟶ Over.mk t) ≫ relativePointsEquiv G t x) *
        ((Over.homMk ψ hψ : Over.mk t' ⟶ Over.mk t) ≫ relativePointsEquiv G t y)
    exact MonObj.comp_mul _ _ _

variable {k : Type u} [Field k]

/-- A connected group scheme of finite type over a field is geometrically connected. -/
theorem geometricallyConnected_of_connected
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left] :
    GeometricallyConnected G.X.hom := by
  obtain ⟨G₀, i, L₀, hi, _, _, _, hgc, hrange, _⟩ :=
    G.relativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent k
  have : IsOpenImmersion i := hi
  have hiRange : i.opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    change Set.range i = Set.univ
    simpa only [PreconnectedSpace.connectedComponent_eq_univ] using hrange
  have : IsIso i := isIso_of_isOpenImmersion_of_opensRange_eq_top i hiRange
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@GeometricallyConnected : MorphismProperty Scheme.{u}) i G.X.hom).mp hgc

/-- Connectedness persists after every field extension of a finite type group scheme. -/
theorem connectedSpace_baseChange_of_connected
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    {K : Type u} [Field K] (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left := by
  have : GeometricallyConnected G.X.hom := G.geometricallyConnected_of_connected
  exact pullback_of_geometrically
    (GeometricallyConnected.geometrically_connectedSpace (f := G.X.hom)) K b

/-- A smooth connected affine group scheme remains connected under every field extension. -/
theorem connectedSpace_baseChange_of_smooth_affine
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {K : Type u} [Field K] (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
  G.connectedSpace_baseChange_of_connected b

/-- The algebraic-closure base change of a connected reductive group is connected. -/
theorem IsConnectedReductive.connectedSpace_toAlgebraicClosure
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G) :
    ConnectedSpace ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.left := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  exact G.connectedSpace_baseChange_of_smooth_affine (toAlgebraicClosure k)

end Langlands.GroupScheme

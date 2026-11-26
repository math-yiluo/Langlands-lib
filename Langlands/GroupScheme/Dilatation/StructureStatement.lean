import Langlands.GroupScheme.Dilatation.CongruenceModel

/-! # Smoothness and geometric connectedness of dilatations and congruence models -/

open AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel

universe u

/-- Dilatation of a smooth affine DVR model along a smooth closed subgroup is smooth.
A geometrically connected centre gives a geometrically connected special fibre, and
geometric connectedness of the supplied generic group then gives it on all fibres. -/
def SmoothDilatationStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) (M : IntegralModel R K G)
    (ϖ : R) (hϖ : Irreducible ϖ)
    (Y : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
    (j : Y ⟶ M.specialFibre) [IsClosedImmersion j.hom.hom.left],
    M.IsSmooth → Smooth Y.X.hom →
    (M.dilatation hϖ j).IsSmooth ∧
    (GeometricallyConnected Y.X.hom →
      (M.dilatation hϖ j).HasGeometricallyConnectedSpecialFibre) ∧
    (GeometricallyConnected G.X.hom → GeometricallyConnected Y.X.hom →
      (M.dilatation hϖ j).HasGeometricallyConnectedFibres)

/-- Every positive congruence model of a smooth affine DVR group model is smooth
with geometrically connected special fibre. If the supplied generic group is
geometrically connected then every fibre of the positive model is geometrically connected. -/
def SmoothCongruenceModelsStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) (M : IntegralModel R K G)
    (ϖ : R) (hϖ : Irreducible ϖ), M.IsSmooth → ∀ n : ℕ+,
    (M.congruenceModel hϖ (n : ℕ)).IsSmooth ∧
    (M.congruenceModel hϖ (n : ℕ)).HasGeometricallyConnectedSpecialFibre ∧
    (GeometricallyConnected G.X.hom →
      (M.congruenceModel hϖ (n : ℕ)).HasGeometricallyConnectedFibres)

/-- Structural properties of the special-fibre dilatation and its congruence applications. -/
def DilatationStructureStatement : Prop :=
  SmoothDilatationStatement.{u} ∧ SmoothCongruenceModelsStatement.{u}

end Langlands.GroupScheme.IntegralModel

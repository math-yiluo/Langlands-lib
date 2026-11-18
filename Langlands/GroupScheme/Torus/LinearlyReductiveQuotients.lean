import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficients
import Langlands.GroupScheme.MatrixRepresentation.StableProjection
import Langlands.GroupScheme.Rational.CoordinateAction
import Langlands.GroupScheme.Rational.DominantPullbackProof
import Langlands.GroupScheme.Torus.NagataReductionStatements

/-! # Linear reductivity along injective affine coordinate pullbacks -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- Restriction along a homomorphism with injective affine coordinate pullback
preserves and reflects stability on all affine tests. -/
theorem MatrixRepresentation.isStableSubspace_restrict_iff_of_injective_pullback
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation H n)
    (f : G ⟶ H) (hf : Function.Injective (CoordinateWeights.pullback f.hom.hom))
    (W : Submodule k (n → k)) :
    (ρ.restrict f).IsStableSubspace W ↔ ρ.IsStableSubspace W := by
  refine ⟨fun h => ?_, fun h => h.restrict f⟩
  apply (AffineCoefficients.isStableSubspace_iff ρ W).mpr
  intro ℓ v hv
  let φ := CoordinateWeights.pullback f.hom.hom
  obtain ⟨r, hr⟩ := φ.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hf)
  have hm : (ρ.restrict f).universalCharacterMatrix = ρ.universalCharacterMatrix.map φ := by
    unfold universalCharacterMatrix
    rw [affineMatrix_restrict]
    exact (AffineCoefficients.universalCharacterMatrix_map ρ _ _).symm
  have hc : AffineCoefficients.coefficientMap (ρ.restrict f) (ℓ.comp r) =
      AffineCoefficients.coefficientMap ρ ℓ := by
    change (ρ.restrict f).universalCharacterMatrix.map (ℓ.comp r) = _
    rw [hm]
    apply Matrix.ext
    intro i j
    change ℓ (r (φ (ρ.universalCharacterMatrix i j))) = ℓ (ρ.universalCharacterMatrix i j)
    exact congrArg ℓ (DFunLike.congr_fun hr _)
  rw [← hc]
  exact (AffineCoefficients.isStableSubspace_iff (ρ.restrict f) W).mp h (ℓ.comp r) v hv

/-- Linear reductivity descends along a homomorphism with injective affine
coordinate pullback. -/
theorem IsLinearlyReductive.of_injective_pullback
    (hG : IsLinearlyReductive G) (f : G ⟶ H)
    (hf : Function.Injective (CoordinateWeights.pullback f.hom.hom)) :
    IsLinearlyReductive H := by
  intro n ρ
  simpa only [MatrixRepresentation.isStableSubspace_restrict_iff_of_injective_pullback
    ρ f hf] using hG n (ρ.restrict f)

/-- A schematically dominant affine morphism has injective coordinate pullback. -/
theorem CoordinateWeights.pullback_injective_of_schemeTheoreticallyDominant
    (f : G.X ⟶ H.X) [IsSchemeTheoreticallyDominant f.left] :
    Function.Injective (CoordinateWeights.pullback f) := by
  let ψ := ((commAlgCatEquivUnder (CommRingCat.of k)).functor.map
    (CommAlgCat.ofHom (PointedCoordinateWeights.pullback f))).right
  have hleft := congrArg CommaMorphism.left
    (PointedCoordinateWeights.algSpec_map_pullback f)
  simp only [Over.comp_left, algSpec_map_left, Quiver.Hom.unop_op] at hleft
  have hψ : Spec.map ψ = (PointedCoordinateWeights.coordinateIso G.X).hom.left ≫
      f.left ≫ (PointedCoordinateWeights.coordinateIso H.X).inv.left := by
    rw [← Category.assoc, ← hleft, Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, Category.comp_id]
  have : IsSchemeTheoreticallyDominant (Spec.map ψ) := by
    rw [hψ]
    infer_instance
  have hi := (Spec.map ψ).app_injective ⊤
  have heq : ψ = (Scheme.ΓSpecIso _).inv ≫ (Spec.map ψ).appTop ≫
      (Scheme.ΓSpecIso _).hom := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hinj : Function.Injective ψ := by
    rw [heq]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).1.comp
      (hi.comp (ConcreteCategory.bijective_of_isIso _).1)
  exact hinj

/-- Linear reductivity descends along schematically dominant affine group
homomorphisms over fields. -/
def LinearlyReductiveSchematicQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] (f : G ⟶ H)
    [IsSchemeTheoreticallyDominant f.hom.hom.left],
    IsLinearlyReductive G → IsLinearlyReductive H

/-- The geometric form of linear reductivity descent. -/
theorem linearlyReductiveSchematicQuotient :
    LinearlyReductiveSchematicQuotientStatement.{u} := by
  intro k _ G H _ _ f _ hG
  exact hG.of_injective_pullback f
    (CoordinateWeights.pullback_injective_of_schemeTheoreticallyDominant f.hom.hom)

end Langlands.GroupScheme

import Langlands.GroupScheme.GeometricComponentCanonicalTower

/-! # The identity law for canonical fixed component extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisPointComparison

private def baseChangeEqIdIso {S : Scheme.{u}} (b : S ⟶ S) (h : b = 𝟙 S)
    (G : GroupScheme S) : (GroupScheme.baseChange b).obj G ≅ G :=
  eqToIso (congrArg (fun f => (GroupScheme.baseChange f).obj G) h) ≪≫
    baseChangeIdIso G

private theorem baseChangeEqIdIso_hom_left {S : Scheme.{u}}
    (b : S ⟶ S) (h : b = 𝟙 S) (G : GroupScheme S) :
    (baseChangeEqIdIso b h G).hom.hom.hom.left =
      CategoryTheory.Limits.pullback.fst G.X.hom b := by
  subst b
  change (𝟙 _ ≫ (baseChangeIdIso G).hom).hom.hom.left = _
  simpa only [Category.id_comp] using baseChangeIdIso_hom_left G

variable (k : Type u) [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k)))

/-- The actual self-pullback is identified with the original group scheme by
the standard pullback identity comparison. -/
def selfBaseChangeIso : baseChanged k k H ≅ H :=
  baseChangeEqIdIso (baseMap k k) (by simp [baseMap]) H

/-- The self-pullback comparison is the actual first pullback projection. -/
@[simp]
theorem selfBaseChangeIso_hom_left :
    (selfBaseChangeIso k H).hom.hom.hom.left =
      CategoryTheory.Limits.pullback.fst H.X.hom (baseMap k k) :=
  baseChangeEqIdIso_hom_left _ _ _

variable (M : Type u) [Field M] [Algebra k M]

/-- On coefficient points, the self-pullback comparison is the published
coefficient projection equivalence. -/
theorem selfBaseChangeIso_coefficient
    (x : (baseChanged k k H).affinePoints (CommAlgCat.of k M)) :
    (baseChanged k k H).affinePointsTarget (selfBaseChangeIso k H).hom
        (CommAlgCat.of k M) x =
      coefficientBaseChangeEquiv k k M H x := by
  apply Over.OverMorphism.ext
  simp only [affinePointsTarget_apply, Over.comp_left,
    selfBaseChangeIso_hom_left, coefficientBaseChangeEquiv_left]

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

variable (k : Type u) [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

private theorem selfSectionHom
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    rationalPoints.map
        ((GroupScheme.baseChange (baseMap k (AlgebraicClosure k))).map
          (selfBaseChangeIso k H).hom)
        (geometricComponentBaseChangeSectionHom k k H x) = x := by
  apply (baseChangeCoeffEquiv k (AlgebraicClosure k) H).injective
  rw [baseChangeCoeffEquiv_map, selfBaseChangeIso_coefficient,
    geometricComponentBaseChangeSectionHom_coefficient]
  change Lie.affineMap H (AlgHom.id k (AlgebraicClosure k))
      (baseChangeCoeffEquiv k (AlgebraicClosure k) H x) =
    baseChangeCoeffEquiv k (AlgebraicClosure k) H x
  rw [Lie.affineMap_id]

/-- The comparison along the identity embedding of the chosen algebraic
closure becomes the identity after the actual self-pullback projection. -/
theorem geometricComponentBaseChangeEquivOfEmbedding_id
    (c : GeometricComponents k H) :
    geometricComponentMap k (selfBaseChangeIso k H).hom
        (geometricComponentBaseChangeEquivOfEmbedding k k H
          (AlgHom.id k (AlgebraicClosure k)) c) = c := by
  obtain ⟨x, rfl⟩ := geometricComponentOfPoint_surjective k H c
  change geometricComponentMap k (selfBaseChangeIso k H).hom
      (geometricComponentBaseChangeEquiv k k H (geometricComponentOfPoint k H x)) = _
  rw [geometricComponentBaseChangeEquiv_ofPoint, geometricComponentMap_ofPoint,
    selfSectionHom]

/-- The actual self-pullback comparison induces an equivalence on the full
Galois-fixed geometric component groups. -/
def geometricComponentFixedSelfIso :
    geometricComponentFixedSubgroup k (baseChanged k k H) ≃*
      geometricComponentFixedSubgroup k H :=
  geometricComponentFixedIso k (selfBaseChangeIso k H)

@[simp]
theorem geometricComponentFixedSelfIso_val
    (c : geometricComponentFixedSubgroup k (baseChanged k k H)) :
    (geometricComponentFixedSelfIso k H c).val =
      geometricComponentMap k (selfBaseChangeIso k H).hom c.val := rfl

/-- Canonical extension from a field to itself becomes the identity under
the actual self-pullback comparison. -/
theorem geometricComponentCanonicalBaseChange_id
    (c : geometricComponentFixedSubgroup k H) :
    geometricComponentFixedSelfIso k H
        (geometricComponentCanonicalBaseChange k k H c) = c := by
  apply Subtype.ext
  rw [geometricComponentFixedSelfIso_val,
    geometricComponentCanonicalBaseChange_val k k H
      (AlgHom.id k (AlgebraicClosure k))]
  exact geometricComponentBaseChangeEquivOfEmbedding_id k H c.val

/-- The identity law as an equality of homomorphisms on the full fixed group. -/
theorem geometricComponentCanonicalBaseChange_id_hom :
    (geometricComponentFixedSelfIso k H).toMonoidHom.comp
        (geometricComponentCanonicalBaseChange k k H) =
      MonoidHom.id (geometricComponentFixedSubgroup k H) := by
  apply MonoidHom.ext
  intro c
  exact geometricComponentCanonicalBaseChange_id k H c

/-- Self-extension is exactly the inverse homomorphism of the actual
self-pullback equivalence. -/
theorem geometricComponentCanonicalBaseChange_self_eq :
    geometricComponentCanonicalBaseChange k k H =
      (geometricComponentFixedSelfIso k H).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro c
  apply (geometricComponentFixedSelfIso k H).injective
  rw [geometricComponentCanonicalBaseChange_id]
  exact ((geometricComponentFixedSelfIso k H).apply_symm_apply c).symm

/-- Canonical extension to the same field is bijective on the full fixed group. -/
theorem geometricComponentCanonicalBaseChange_self_bijective :
    Function.Bijective (geometricComponentCanonicalBaseChange k k H) := by
  rw [geometricComponentCanonicalBaseChange_self_eq]
  exact (geometricComponentFixedSelfIso k H).symm.bijective

end Langlands.GroupScheme.IdentityComponent

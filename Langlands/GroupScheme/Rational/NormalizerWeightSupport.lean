import Langlands.GroupScheme.Rational.TangentImage
import Langlands.GroupScheme.Rational.RootKernelTorus
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction

/-! # Normalizer permutations of the actual tangent-weight support -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (j : H ⟶ G) {F : SubgroupFunctor G}

/-- Normalization on every test preserves the intrinsic tangent submodule
under the adjoint action of each rational point of the normalizing group. -/
theorem basePointAdjoint_mem_tangentSubmodule
    (hF : (AutomorphicAction.conjugation j).IsStable F)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    {X : Additive (lieKernel G k)} (hX : X ∈ tangentSubmodule F) :
    basePointAdjoint (n ≫ j.hom.hom) X ∈ tangentSubmodule F := by
  have hc : Lie.constant G (A := k) (G.constantPoint (n ≫ j.hom.hom) _) =
      H.constantPoint n _ ≫ j.hom.hom := by
    change Lie.affineMap G (TrivSqZeroExt.inlAlgHom (CommRingCat.of k) k k)
      (G.constantPoint (n ≫ j.hom.hom) _) = G.constantPoint (n ≫ j.hom.hom) _
    exact G.constantPoint_naturality _ _
  have h := hF _ (H.constantPoint n _) X.toMul.val hX
  simpa only [mem_tangentSubmodule, basePointAdjoint, adjoint_val,
    AutomorphicAction.conjugation_act, hc] using h

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (t : T.toGrp ⟶ H) [Mono t.hom.hom.left]

/-- Every rational normalizing point carries each actual subgroup weight
to its Weyl translate. -/
theorem weylAction_mapsTo_actionWeightSupport
    (hF : (AutomorphicAction.conjugation j).IsStable F)
    (n : normalizerPoints t) :
    Set.MapsTo (weylAction t n)
      (actionWeightSupport (AutomorphicAction.conjugation (t ≫ j)) F)
      (actionWeightSupport (AutomorphicAction.conjugation (t ≫ j)) F) := by
  intro χ hχ
  obtain ⟨X, hX0, hXχ, hXF⟩ := hχ
  refine ⟨basePointAdjoint (n.val ≫ j.hom.hom) X, ?_, ?_,
    basePointAdjoint_mem_tangentSubmodule j hF n.val hXF⟩
  · intro h0
    apply hX0
    have h := congrArg (basePointAdjoint (n.val ≫ j.hom.hom)⁻¹) h0
    change (basePointAdjoint (n.val ≫ j.hom.hom)⁻¹ *
      basePointAdjoint (n.val ≫ j.hom.hom)) X = _ at h
    rw [basePointAdjoint_inv_mul, Module.End.one_apply, map_zero] at h
    exact h
  · rw [actionWeightSpace_conjugation] at hXχ ⊢
    rw [weylAction_apply]
    exact ((isNormalizingPoint_normalizingAut t n).comp j).adjoint_mem_weightSpace hXχ

/-- Normalization makes occurrence of an actual tangent weight invariant
under every rational normalizing point. Zero is retained when it occurs. -/
theorem weylAction_mem_actionWeightSupport_iff
    (hF : (AutomorphicAction.conjugation j).IsStable F)
    (n : normalizerPoints t) (χ : characterLattice T) :
    weylAction t n χ ∈ actionWeightSupport (AutomorphicAction.conjugation (t ≫ j)) F ↔
      χ ∈ actionWeightSupport (AutomorphicAction.conjugation (t ≫ j)) F := by
  constructor
  · intro hχ
    have h := weylAction_mapsTo_actionWeightSupport j t hF n⁻¹ hχ
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h
    exact h
  · intro hχ
    exact weylAction_mapsTo_actionWeightSupport j t hF n hχ

/-- The actual Weyl quotient preserves the complete intrinsic subgroup support. -/
theorem relativeWeylCharacterAction_mem_actionWeightSupport_iff
    (hF : (AutomorphicAction.conjugation j).IsStable F)
    (w : relativeWeylGroup t) (χ : characterLattice T) :
    relativeWeylCharacterAction t w χ ∈
      actionWeightSupport (AutomorphicAction.conjugation (t ≫ j)) F ↔
      χ ∈ actionWeightSupport (AutomorphicAction.conjugation (t ≫ j)) F := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  exact weylAction_mem_actionWeightSupport_iff j t hF n χ

/-- The quotient of actual rational normalizers by actual rational
centralizers permutes all weights in the normalized subgroup's tangent image. -/
def normalizedWeightPermutation
    (hF : (AutomorphicAction.conjugation j).IsStable F) :
    relativeWeylGroup t →*
      Equiv.Perm (actionWeightSupport (AutomorphicAction.conjugation (t ≫ j)) F) where
  toFun w :=
    { toFun := fun χ => ⟨relativeWeylCharacterAction t w χ,
        (relativeWeylCharacterAction_mem_actionWeightSupport_iff j t hF w χ).mpr χ.property⟩
      invFun := fun χ => ⟨relativeWeylCharacterAction t w⁻¹ χ,
        (relativeWeylCharacterAction_mem_actionWeightSupport_iff j t hF w⁻¹ χ).mpr χ.property⟩
      left_inv := by
        intro χ
        apply Subtype.ext
        change relativeWeylCharacterAction t w⁻¹ (relativeWeylCharacterAction t w χ) = χ
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := by
        intro χ
        apply Subtype.ext
        change relativeWeylCharacterAction t w (relativeWeylCharacterAction t w⁻¹ χ) = χ
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by
    apply Equiv.ext
    intro χ
    apply Subtype.ext
    change relativeWeylCharacterAction t 1 χ = χ
    rw [map_one]
    rfl
  map_mul' w z := by
    apply Equiv.ext
    intro χ
    apply Subtype.ext
    change relativeWeylCharacterAction t (w * z) χ =
      relativeWeylCharacterAction t w (relativeWeylCharacterAction t z χ)
    rw [map_mul, LinearEquiv.mul_apply]

@[simp] theorem normalizedWeightPermutation_apply
    (hF : (AutomorphicAction.conjugation j).IsStable F)
    (w : relativeWeylGroup t)
    (χ : actionWeightSupport (AutomorphicAction.conjugation (t ≫ j)) F) :
    (normalizedWeightPermutation j t hF w χ : characterLattice T) =
      relativeWeylCharacterAction t w χ := rfl

end Langlands.GroupScheme.RelativeRoot

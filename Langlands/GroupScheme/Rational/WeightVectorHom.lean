import Langlands.GroupScheme.Rational.VectorPointLieEquiv
import Langlands.GroupScheme.Lie.KernelTargetMaps

/-! # Homomorphisms between vector groups of the same torus weight -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

open WeightVectorUniqueness

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction S.toGrp U} {c : AutomorphicAction S.toGrp V}
    {a : characterLattice S} {m n : ℕ}
    {eU : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ U.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))}
    {eV : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))}
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hwU : IsWeightVectorCoordinates b a eU) (hwV : IsWeightVectorCoordinates c a eV)
    (f : U ⟶ V)
    (hf : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ U.X),
      b.act s x ≫ f.hom.hom = c.act s (x ≫ f.hom.hom))

include hS ha hwU hwV hf

/-- Equivariance forces compatibility with the universal scalar, by restriction
along the injective Laurent power map associated to a positive pairing. -/
theorem coordinateSmul_universalScalar_equivariantHom {N : ℕ}
    (v : universalScheme k N ⟶ U.X) :
    coordinateSmul eU _ (universalScalar k N) v ≫ f.hom.hom =
      coordinateSmul eV _ (universalScalar k N) (v ≫ f.hom.hom) := by
  obtain ⟨D, hD, ζ, hζ⟩ := hS.exists_pairing_eq_pos ha
  apply hwV.1.cancel (powerMap D) (powerMap_appTop_injective hD)
  rw [← Category.assoc, hwU.powerMap_coordinateSmul hζ,
    hwV.powerMap_coordinateSmul hζ, hf, Category.assoc]

/-- Every equivariant homomorphism between vector groups of the same nonzero
split-torus weight is scalar linear on all test schemes. -/
theorem coordinateSmul_equivariantHom
    (T : Over (Spec (CommRingCat.of k))) (r : Γ(T.left, ⊤)) (v : T ⟶ U.X) :
    coordinateSmul eU T r v ≫ f.hom.hom =
      coordinateSmul eV T r (v ≫ f.hom.hom) := by
  let g := classifyingMap T r (eU T v).toAdd
  have hgr : g.left.appTop (universalScalar k m) = r :=
    classifyingMap_universalScalar T r _
  have hgv : g ≫ universalPoint eU = v :=
    classifyingMap_universalPoint hwU.1 T r v
  calc
    _ = (g ≫ coordinateSmul eU _ (universalScalar k m) (universalPoint eU)) ≫
        f.hom.hom := by rw [hwU.1.comp_coordinateSmul, hgr, hgv]
    _ = g ≫ coordinateSmul eV _ (universalScalar k m)
        (universalPoint eU ≫ f.hom.hom) := by
      rw [Category.assoc, coordinateSmul_universalScalar_equivariantHom
        hS ha hwU hwV f hf]
    _ = _ := by rw [hwV.1.comp_coordinateSmul, hgr, ← Category.assoc, hgv]

variable [IsAffineHom U.X.hom] [IsAffineHom V.X.hom]

/-- The actual differential of any equivariant homomorphism of a common nonzero
weight intertwines the point-to-Lie comparisons on every coefficient algebra. -/
theorem vectorPointLieEquiv_equivariantHom
    (A : CommAlgCat.{u} (CommRingCat.of k)) (v : Lie.AffinePoints U A) :
    Lie.targetMapLinear f A
        (vectorPointLieEquiv eU hwU.1 A (Additive.ofMul v)) =
      vectorPointLieEquiv eV hwV.1 A (Additive.ofMul (v ≫ f.hom.hom)) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (vectorPointLieEquiv eU hwU.1 A (Additive.ofMul v)).toMul.val ≫
    f.hom.hom = (vectorPointLieEquiv eV hwV.1 A
      (Additive.ofMul (v ≫ f.hom.hom))).toMul.val
  rw [vectorPointLieEquiv_val, vectorPointLieEquiv_val,
    coordinateSmul_equivariantHom hS ha hwU hwV f hf]
  rfl

/-- Express the actual differential in the two natural Lie coordinate systems. -/
def weightVectorHomLinearMap (A : CommAlgCat.{u} (CommRingCat.of k)) :
    (Fin m → A) →ₗ[A] (Fin n → A) :=
  (vectorLieCoordinates eV hwV.1 A).toLinearMap ∘ₗ
    Lie.targetMapLinear f A ∘ₗ (vectorLieCoordinates eU hwU.1 A).symm.toLinearMap

/-- For an equivariant homomorphism of a common nonzero weight, this linear map
also computes the homomorphism on actual points in the two vector coordinates. -/
theorem weightVectorHomLinearMap_coordinates
    (A : CommAlgCat.{u} (CommRingCat.of k)) (v : Lie.AffinePoints U A) :
    weightVectorHomLinearMap hwU hwV f A (vectorAffineCoordinates eU A v).toAdd =
      (vectorAffineCoordinates eV A (v ≫ f.hom.hom)).toAdd := by
  change vectorLieCoordinates eV hwV.1 A
      (Lie.targetMapLinear f A (vectorPointLieEquiv eU hwU.1 A (Additive.ofMul v))) = _
  rw [vectorPointLieEquiv_equivariantHom hS ha hwU hwV f hf,
    vectorLieCoordinates_vectorPointLieEquiv]
  rfl

end Langlands.GroupScheme.RelativeRoot

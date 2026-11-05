import Langlands.GroupScheme.Rational.AdditivePointPowers
import Langlands.GroupScheme.Rational.PointPowerIntegrality

/-! # Spectral integrality from a commuting torus and additive factorization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

section Topology

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {H G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffine H.X.left] [IsAffine G.X.left]

/-- The actual point homomorphism, bundled continuously for the canonical
rational-point topologies. -/
def rationalPointsMapContinuousMap (i : H ⟶ G) :
    letI : TopologicalSpace (rationalPoints H) := rationalPointTopology R H.X
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X
    C(rationalPoints H, rationalPoints G) := by
  let : TopologicalSpace (rationalPoints H) := rationalPointTopology R H.X
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X
  exact ⟨rationalPoints.map i, continuous_rationalPointMap R i.hom.hom⟩

@[simp] theorem rationalPointsMapContinuousMap_apply (i : H ⟶ G)
    (t : rationalPoints H) :
    rationalPointsMapContinuousMap i t = rationalPoints.map i t := rfl

end Topology

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance commutingFactorizationIntegralityLocalInstance1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The image of a point of any closed torus in an anisotropic group has all
nonnegative powers in one compact set of actual rational points. -/
theorem IsAnisotropic.exists_isCompact_powers_map_of_closedTorus
    (hG : IsAnisotropic G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : T.toGrp ⟶ G} (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i)
    (t : rationalPoints T.toGrp) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∃ C : Set (rationalPoints G), IsCompact C ∧
      ∀ k : ℕ, (rationalPoints.map i t) ^ k ∈ C := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom T.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : LocallyOfFiniteType T.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  let : TopologicalSpace (rationalPoints T.toGrp) := rationalPointTopology F T.X
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have hC := (hG.of_isClosedSubgroup hi).isCompact_univ_of_isTorus hT
  refine ⟨Set.range (rationalPoints.map i), ?_, fun k => ?_⟩
  · have hc : Continuous (rationalPoints.map i) :=
      (rationalPointsMapContinuousMap i).continuous
    simpa only [Set.image_univ] using hC.image hc
  · exact ⟨t ^ k, map_pow (rationalPoints.map i) t k⟩

namespace MatrixRepresentation

variable {n : Type} [Fintype n] [DecidableEq n]

/-- A commuting closed-torus/additive factorization of a positive power gives
an integral actual representation matrix in every finite dimension. -/
theorem isIntegral_rationalMatrix_of_pow_eq_torus_mul_additive
    (ρ : MatrixRepresentation G n) (hG : IsAnisotropic G)
    (g : rationalPoints G) {m : ℕ} (hm : 0 < m)
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : T.toGrp ⟶ G) (t : rationalPoints T.toGrp)
    {d : ℕ} (φ : VectorGroup.groupScheme (CommRingCat.of F) d ⟶ G)
    (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hpow : g ^ m = rationalPoints.map i t *
      rationalPoints.map φ
        ((VectorGroup.coordinates (CommRingCat.of F) d (Over.mk (𝟙 _))).symm
          (Multiplicative.ofAdd (fun _ => 1))))
    (hcomm : Commute (rationalPoints.map i t)
      (rationalPoints.map φ
        ((VectorGroup.coordinates (CommRingCat.of F) d (Over.mk (𝟙 _))).symm
          (Multiplicative.ofAdd (fun _ => 1))))) :
    IsIntegral (ValuativeRel.valuation F).integer
      (ρ.rationalMatrix g : Matrix n n F) := by
  obtain ⟨C, hC, ht⟩ := hG.exists_isCompact_powers_map_of_closedTorus hT hi t
  obtain ⟨D, hD, hφ⟩ := VectorGroup.exists_isCompact_powers_map_coordinateOne d F φ
  exact ρ.isIntegral_rationalMatrix_of_pow_eq_mul g _ _ hm hpow hcomm
    C D hC hD ht hφ

/-- Every characteristic coefficient of the original point then belongs to
the canonical valuation ring. -/
theorem charpoly_coeff_vle_one_of_pow_eq_torus_mul_additive
    (ρ : MatrixRepresentation G n) (hG : IsAnisotropic G)
    (g : rationalPoints G) {m : ℕ} (hm : 0 < m)
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : T.toGrp ⟶ G) (t : rationalPoints T.toGrp)
    {d : ℕ} (φ : VectorGroup.groupScheme (CommRingCat.of F) d ⟶ G)
    (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hpow : g ^ m = rationalPoints.map i t *
      rationalPoints.map φ
        ((VectorGroup.coordinates (CommRingCat.of F) d (Over.mk (𝟙 _))).symm
          (Multiplicative.ofAdd (fun _ => 1))))
    (hcomm : Commute (rationalPoints.map i t)
      (rationalPoints.map φ
        ((VectorGroup.coordinates (CommRingCat.of F) d (Over.mk (𝟙 _))).symm
          (Multiplicative.ofAdd (fun _ => 1)))))
    (j : ℕ) :
    (ρ.rationalMatrix g : Matrix n n F).charpoly.coeff j ≤ᵥ (1 : F) :=
  ρ.charpoly_coeff_vle_one_of_isIntegral_rationalMatrix g
    (ρ.isIntegral_rationalMatrix_of_pow_eq_torus_mul_additive hG g hm i t φ
      hT hi hpow hcomm) j

end MatrixRepresentation

end LocalField

end Langlands.GroupScheme

import Langlands.GroupScheme.HomogeneousCharacterCoordinates
import Langlands.GroupScheme.Reductive.CovariantCellFixedLine
import Langlands.GroupScheme.Reductive.SteinbergBigCellReduction
import Langlands.GroupScheme.Reductive.CoordinateNonZeroDivisor
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Covariance of a coordinate from covariance of a power -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace AffineCoordinates

/-- In a domain over an algebraically closed field, two elements with the same
positive power differ by a scalar factor. -/
theorem exists_eq_algebraMap_mul_of_pow_eq {k R : Type*} [Field k] [IsAlgClosed k]
    [CommRing R] [IsDomain R] [Algebra k R] {n : ℕ} (hn : 0 < n) {y z : R}
    (h : y ^ n = z ^ n) : ∃ ζ : k, y = algebraMap k R ζ * z := by
  by_cases hz : z = 0
  · refine ⟨0, ?_⟩
    rw [hz, zero_pow hn.ne'] at h
    rw [pow_eq_zero_iff hn.ne' |>.mp h, hz, mul_zero]
  · let K := FractionRing R
    have hz' : algebraMap R K z ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hz
    let w : K := algebraMap R K y / algebraMap R K z
    have hw : w ^ n = 1 := by
      rw [div_pow, ← map_pow, ← map_pow, h]
      exact div_self (by rw [map_pow]; exact pow_ne_zero n hz')
    have hwi : IsIntegral k w := IsIntegral.of_pow hn (hw ▸ isIntegral_one)
    obtain ⟨ζ, hζ⟩ := minpoly.mem_range_of_degree_eq_one (A := k) (x := w)
      (hx := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hwi))
    refine ⟨ζ, IsFractionRing.injective R K ?_⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply k R K, hζ]
    exact (div_mul_cancel₀ _ hz').symm

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance covariantPowerDescentInst1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance covariantPowerDescentInst2 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- Over an algebraically closed field, a coordinate with counit one is left
covariant for a coordinate `χ` with counit one as soon as its `n`-th power
satisfies the `n`-th power of the covariance equation on every scheme test,
provided the tensor product of the two coordinate algebras is a domain. -/
theorem mem_leftCovariantSubspace_of_pow [IsAlgClosed k]
    [IsDomain (algebra H ⊗[k] algebra G)] (i : H ⟶ G) (χ : algebra H) {f : algebra G}
    {n : ℕ} (hn : 0 < n)
    (hpow : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
      pointAlgebraHom G T ((h ≫ i.hom.hom) * g) f ^ n =
        (pointAlgebraHom H T h χ * pointAlgebraHom G T g f) ^ n)
    (hχ : AffineLinearEmbedding.counit (corepresentation H) χ = 1)
    (hf : AffineLinearEmbedding.counit (corepresentation G) f = 1) :
    f ∈ leftCovariantSubspace i χ := by
  let : Coalgebra k (algebra G) :=
    (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
  let r : algebra G →ₐ[k] algebra H := (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom
  let B : CommAlgCat (CommRingCat.of k) := CommAlgCat.of _ (algebra H ⊗[k] algebra G)
  let ε : algebra H ⊗[k] algebra G →ₐ[k]
      ((algΓ (CommRingCat.of k)).obj ((algSpec (CommRingCat.of k)).obj (op B))).unop :=
    ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)).unop.hom
  let φL : algebra H ⟶ B := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
  let φR : algebra G ⟶ B := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  have e := hpow _ (algPoint H φL) (algPoint G φR)
  rw [pointAlgebraHom_mul, AffineHomImageHopfAdapter.pointAlgebraHom_pullback,
    pointAlgebraHom_algPoint, pointAlgebraHom_algPoint] at e
  have e' : (r.toLinearMap.rTensor (algebra G) (Coalgebra.comul f)) ^ n =
      (χ ⊗ₜ[k] f) ^ n := by
    apply counit_unop_injective B
    rw [map_pow, map_pow]
    change ε (r.toLinearMap.rTensor (algebra G) (Coalgebra.comul f)) ^ n =
      ε (χ ⊗ₜ[k] f) ^ n
    refine (congrArg (· ^ n) ((productMap_comp_include ε _).symm.trans
      (productMap_rTensor' r _ _ _))).trans (e.trans ?_)
    change (ε (χ ⊗ₜ[k] 1) * ε (1 ⊗ₜ[k] f)) ^ n = _
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  obtain ⟨ζ, hζ⟩ := exists_eq_algebraMap_mul_of_pow_eq (k := k) hn e'
  have hmem : f ∈ leftCovariantSubspace i (ζ • χ) := by
    rw [mem_leftCovariantSubspace]
    refine hζ.trans ?_
    rw [Algebra.algebraMap_eq_smul_one (R := k) (A := algebra H ⊗[k] algebra G) ζ, smul_mul_assoc, one_mul, TensorProduct.smul_tmul']
  have hζ1 : ζ = 1 := by
    have := nontrivial_algΓ_identityTest (k := k)
    have he := pointAlgebraHom_leftCovariant i (ζ • χ) hmem
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 1
    rw [MonObj.one_comp, mul_one, pointAlgebraHom_one_apply, pointAlgebraHom_one_apply,
      map_smul, hχ, hf, smul_eq_mul, mul_one, map_one, mul_one] at he
    exact ((algebraMap k _).injective (he.symm.trans (map_one _).symm))
  rw [hζ1, one_smul] at hmem
  exact hmem

variable {U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom]

local instance covariantPowerDescentInst3 : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom

/-- Over an algebraically closed field, a coordinate with counit one is right
invariant under a group-scheme morphism as soon as its `n`-th power is, on every
scheme test, provided the tensor product of the two coordinate algebras is a
domain. -/
theorem mem_rightInvariantSubspace_of_pow [IsAlgClosed k]
    [IsDomain (algebra U ⊗[k] algebra G)] (j : U ⟶ G) {f : algebra G} {n : ℕ} (hn : 0 < n)
    (hpow : ∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ U.X) (g : T ⟶ G.X),
      pointAlgebraHom G T (g * (u ≫ j.hom.hom)) f ^ n = pointAlgebraHom G T g f ^ n)
    (hf : AffineLinearEmbedding.counit (corepresentation G) f = 1) :
    f ∈ rightInvariantSubspace j := by
  have hS : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      pointAlgebraHom G T g⁻¹ (antipodeCoord G f) = pointAlgebraHom G T g f := by
    intro T g
    rw [pointAlgebraHom_antipode, inv_inv]
  have hf' : AffineLinearEmbedding.counit (corepresentation G) (antipodeCoord G f) = 1 := by
    have := nontrivial_algΓ_identityTest (k := k)
    apply (algebraMap k ((algΓ (CommRingCat.of k)).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop).injective
    rw [← pointAlgebraHom_one_apply, pointAlgebraHom_antipode, inv_one,
      pointAlgebraHom_one_apply, hf]
  have hcov : antipodeCoord G f ∈ leftCovariantSubspace j 1 := by
    refine mem_leftCovariantSubspace_of_pow j 1 hn (fun T u g => ?_) (map_one _) hf'
    rw [map_one, one_mul, pointAlgebraHom_antipode, pointAlgebraHom_antipode, mul_inv_rev,
      ← GrpObj.inv_comp]
    exact hpow T u⁻¹ g⁻¹
  intro T u g
  have h := pointAlgebraHom_leftCovariant j 1 hcov T u⁻¹ g⁻¹
  rw [map_one, one_mul, GrpObj.inv_comp, ← mul_inv_rev, hS, hS] at h
  exact h

end AffineCoordinates

end Langlands.GroupScheme

import Langlands.Geometry.Building.TorusFiltration.CongruenceProof
import Langlands.Geometry.Building.TorusFiltration.FunctorialityProof
import Langlands.GroupScheme.IntegralModel.CongruenceLieStatements
import Langlands.GroupScheme.IntegralModel.LieLatticeReduction

/-! # The Lie filtration of the minimal congruent torus filtration

For a torus `T` over the maximal unramified extension `K = inertiaFixedField F` of a
nonarchimedean local field `F`, `minimalCongruentLie F T hT r` is the Lie lattice
`t(K)_r = Lie(𝒯_r)` of the constructed smooth model `𝒯_r = minimalCongruentModel F T hT r`
(KP Propositions B.6.9 and B.10.16, where `t(k)_r = Lie(T_r)` by definition). The file proves
that it is antitone and a lattice, identifies the congruence subgroups of every smooth model
with integral points `T(K)_r` with deeper terms of the filtration, and derives the Lie
congruence `𝔪^k • t(K)_r = t(K)_{r+k}` from KP Lemma A.5.13(4), which enters as an argument.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "Model" => IntegralModel O K T.toGrp
local notation "𝔪" => IsLocalRing.maximalIdeal (fixedFieldIntegers F)

private local instance minimalCongruentLieIntegersDVR : IsDiscreteValuationRing O :=
  (fixedFieldIntegers_strictHenselian F).1

/-- The Lie lattice `t(K)_r = Lie(𝒯_r)` of the constructed smooth model at depth `r`,
inside the Lie algebra of `T`. -/
def minimalCongruentLie (r : ℝ≥0) : Submodule O (GenericLie O T.toGrp) :=
  (minimalCongruentModel F T hT r).val.lieLattice

omit [IsAffine T.X.left] in
private theorem map_identity_le_of_le' {M N : Model} (h : M.integralPoints ≤ N.integralPoints) :
    M.integralPoints.map (rationalPoints.map (𝟙 T.toGrp)) ≤ N.integralPoints := by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using h hx

/-- A smooth model whose integral points lie in those of another model has the smaller
Lie lattice: the identity extends to a model homomorphism (KP Corollary 2.10.10). -/
theorem lieLattice_le_of_integralPoints_le {M N : Model} (hM : M.IsSmooth)
    (h : M.integralPoints ≤ N.integralPoints) : M.lieLattice ≤ N.lieLattice := by
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F hM rfl
    (map_identity_le_of_le' F T h)
  intro X hX
  have h := φ.map_lieLattice_le (Submodule.mem_map_of_mem (f := GenericLie.map O (𝟙 T.toGrp)) hX)
  rwa [GenericLie.map_id] at h

/-- Every smooth model with integral points `T(K)_r` has Lie lattice `t(K)_r`
(KP Corollary 2.10.11). -/
theorem lieLattice_eq_minimalCongruentLie (r : ℝ≥0) {M : Model} (hM : M.IsSmooth)
    (hp : M.integralPoints = minimalCongruentPoints F T hT r) :
    M.lieLattice = minimalCongruentLie F T hT r := by
  let N := minimalCongruentModel F T hT r
  exact le_antisymm (lieLattice_le_of_integralPoints_le F T hM (hp.trans N.property.2.2.symm).le)
    (lieLattice_le_of_integralPoints_le F T N.property.1 (N.property.2.2.trans hp.symm).le)

/-- The Lie filtration decreases with the depth. -/
theorem minimalCongruentLie_antitone : Antitone (minimalCongruentLie F T hT) := by
  intro r s h
  refine lieLattice_le_of_integralPoints_le F T (minimalCongruentModel F T hT s).property.1 ?_
  rw [(minimalCongruentModel F T hT s).property.2.2, (minimalCongruentModel F T hT r).property.2.2]
  exact minimalCongruentPoints_antitone F T hT h

section Lattice

/- The tower instance of the generic Lie algebra is tried first: the search through the
intermediate-field instances of `inertiaFixedField F` does not terminate in time. -/
attribute [local instance high] GenericLie.instIsScalarTower

/-- Every term of the Lie filtration is a lattice in the Lie algebra of `T`. -/
theorem minimalCongruentLie_isLattice (r : ℝ≥0) :
    Submodule.IsLattice (inertiaFixedField F) (minimalCongruentLie F T hT r) :=
  IntegralModel.lieLattice_isLattice (minimalCongruentModel F T hT r).property.1

end Lattice

omit [IsAffine T.X.left] in
private theorem congruenceModel_isSmooth_pnat (M : Model) (hM : M.IsSmooth) {π : O}
    (hπ : Irreducible π) (k : ℕ+) : (M.congruenceModel hπ (k : ℕ)).IsSmooth :=
  (IntegralModel.dilatationStructure.2 O K T.toGrp M π hπ hM k).1

/-- The level-`k` congruence subgroup of a smooth model with integral points `T(K)_r` is
`T(K)_{r+k}`: the level-one case is the congruence property of the filtration, and the
induction passes through the positive congruence models. -/
theorem congruenceSubgroupAt_eq_minimalCongruentPoints (r : ℝ≥0) (k : ℕ+) {M : Model}
    (hM : M.IsSmooth) (hp : M.integralPoints = minimalCongruentPoints F T hT r) :
    M.congruenceSubgroupAt k = minimalCongruentPoints F T hT (r + (k : ℕ)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  induction k using PNat.recOn with
  | one =>
    rw [M.congruenceSubgroupAt_one, minimalCongruentCongruence F T hT r M hM hp]
    simp
  | succ k ih =>
    let P := M.positiveCongruenceModel hπ k
    have hP : P.IsSmooth := by
      have h := congruenceModel_isSmooth_pnat F T M hM hπ k
      rwa [M.congruenceModel_coe_pnat] at h
    have hPp : P.integralPoints = minimalCongruentPoints F T hT (r + (k : ℕ)) :=
      (M.integralPoints_positiveCongruenceModel hπ k).trans ih
    rw [← M.congruenceSubgroupAt_positiveCongruenceModel hπ k 1, P.congruenceSubgroupAt_one,
      minimalCongruentCongruence F T hT _ P hP hPp]
    simp only [PNat.add_coe, PNat.val_ofNat, Nat.cast_add, Nat.cast_one, add_assoc]

/-- The `k`th maximal-ideal multiple of the Lie lattice of a smooth model with integral
points `T(K)_r` is `t(K)_{r+k}`. The Lie lattice of the level-`k` congruence model is
that multiple (KP Lemma A.5.13(4), the argument `h𝔩`), and that model has integral points
`T(K)_{r+k}`. -/
theorem smul_lieLattice_eq_minimalCongruentLie
    (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u}) (r : ℝ≥0) (k : ℕ) {M : Model}
    (hM : M.IsSmooth) (hp : M.integralPoints = minimalCongruentPoints F T hT r) :
    (𝔪 ^ k : Ideal O) • M.lieLattice = minimalCongruentLie F T hT (r + k) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [← h𝔩 O K T.toGrp M π hπ k]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using lieLattice_eq_minimalCongruentLie F T hT r hM hp
  · let k' : ℕ+ := ⟨k, hk⟩
    change (M.congruenceModel hπ (k' : ℕ)).lieLattice = minimalCongruentLie F T hT (r + (k' : ℕ))
    exact lieLattice_eq_minimalCongruentLie F T hT _ (congruenceModel_isSmooth_pnat F T M hM hπ k')
      ((M.integralPoints_congruenceModel hπ k').trans
        (congruenceSubgroupAt_eq_minimalCongruentPoints F T hT r k' hM hp))

/-- The Lie congruence `𝔪^k • t(K)_r = t(K)_{r+k}`, from KP Lemma A.5.13(4) (the argument
`h𝔩`). -/
theorem smul_minimalCongruentLie (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u})
    (r : ℝ≥0) (k : ℕ) :
    (𝔪 ^ k : Ideal O) • minimalCongruentLie F T hT r = minimalCongruentLie F T hT (r + k) :=
  smul_lieLattice_eq_minimalCongruentLie F T hT h𝔩 r k (minimalCongruentModel F T hT r).property.1
    (minimalCongruentModel F T hT r).property.2.2

/-- The differential of a homomorphism of tori carries `t(K)_r` into `u(K)_r`: by the
functoriality of the filtration and KP Corollary 2.10.10 the homomorphism extends to the
models at depth `r`. -/
theorem map_minimalCongruentLie_le {U : CommGroupScheme (Spec (CommRingCat.of K))}
    [IsAffine U.X.left] (hU : IsTorus U.toGrp) (f : T ⟶ U) (r : ℝ≥0) :
    (minimalCongruentLie F T hT r).map (GenericLie.map O (CommGroupScheme.groupHom f)) ≤
      minimalCongruentLie F U hU r := by
  let M := minimalCongruentModel F T hT r
  let N := minimalCongruentModel F U hU r
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le (M := N.val)
    (n := CommGroupScheme.groupHom f) IntegralModel.smoothHomExtension F M.property.1 rfl (by
      rw [M.property.2.2, N.property.2.2]
      exact minimalCongruentFunctoriality F T U hT hU f r)
  exact φ.map_lieLattice_le

end Langlands.Geometry.Building

import Langlands.Global.AdelicWavePacketSiegelDecayReduction
import Langlands.Global.AdelicSiegelSetupExistenceProof
import Langlands.Global.AdelicPositiveDecompositionReduction
import Langlands.Global.AdelicSplitCentreUnitaryCharacter
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.Global.AdelicSiegelNormOne

/-! # Norm-one Siegel points as torus points times a compact set

For an algebraic Siegel setup `(T, i, ν, T₀, j)` of a connected reductive group `G` over a number
field, a point `x = z · n m a k · w` of the Siegel set `A_G · Ω_N Ω_M A_{T₀}(t) K · Ω` that lies
in the norm-one group `G(𝔸)¹` is `a · y` with `y` in a compact set depending only on the Siegel
data. The module also gives the algebraic Siegel setup attached to any maximal split torus and
generic cocharacter. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

section Setup

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

omit [NumberField F] in
/-- Every maximal split torus `T → G` with a generic cocharacter `ν` is part of an algebraic
Siegel setup `(T, i, ν, T₀, j)`. -/
theorem exists_isSiegelAlgebraicSetup (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν) :
    ∃ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
      IsSiegelAlgebraicSetup F G T i ν T₀ j := by
  obtain ⟨D, d, -, -, hd⟩ := derivedSubgroupRepresentability F G
  obtain ⟨T₀, t₀, e, ht₀, he_closed, he⟩ := derivedMaximalSplitTorus F G D d hG hd T i hi
  obtain ⟨⟨A, a, ha⟩, -⟩ := splitComponentStatement F G hG
  obtain ⟨c, hc, -, -⟩ := ha.exists_commFactor_of_isMaximalSplitTorus hi
  have hiso := derivedCentralSplitTorusProduct F G D d hG hd T T₀ A i t₀ e a c hi ht₀
    he_closed he ha hc
  obtain ⟨-, hRL, hU⟩ := standardMinimalLeviStructure F G T i ν hG hi hν
  refine ⟨T₀, e, hi, hν,
    Standard.isMinimalParabolicSubgroup_parabolicHom_of_genericMinimal i ν genericMinimalParabolic
      hG hi hν,
    hRL, hU, standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν,
    relativeRoots_torusToStandardParabolic F G T i ν hG hi hν,
    ⟨D, d, t₀, hd, ht₀, he⟩, A, c, ?_, ?_⟩
  · rw [hc]
    exact ha
  · rw [subgroupProductMap_eq_prodHom e c]
    exact hiso.surjective

end Setup

section Centre

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The points `z ∈ A_G` with `z w ∈ G(𝔸)¹` for some `w` in a compact set `Ω` form a relatively
compact set: in the decomposition `G(𝔸) = A_G × G(𝔸)¹` the `A_G`-coordinate of `z w` is `z`
times that of `w`. -/
theorem exists_isCompact_canonicalSubgroup_of_mul_mem_normOne (hG : IsConnectedReductive G)
    {Z₀ : CommGroupScheme (Spec (CommRingCat.of F))} (c : Z₀.toGrp ⟶ G)
    (hc : IsSplitComponent c) {Ω : Set (AdelicGroupPoints F G)} (hΩ : IsCompact Ω) :
    ∃ Z : Set (AdelicGroupPoints F G), IsCompact Z ∧
      ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G, ∀ w ∈ Ω,
        z * w ∈ normOneSubgroup F G → z ∈ Z := by
  let E := splitComponentNormOneDecomposition centralSplitTorusCharacter F G hG Z₀ c hc
  let f : AdelicGroupPoints F G → AdelicGroupPoints F G :=
    fun w => (positivePointMap F G Z₀ c (E.symm w).1)⁻¹
  have hf : Continuous f :=
    ((positivePointMap F G Z₀ c).continuous.comp
      (continuous_fst.comp E.symm.continuous)).inv
  refine ⟨f '' Ω, hΩ.image hf, ?_⟩
  intro z hz w hw hzw
  rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup hc] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  let c₀ : intrinsicSubgroup F Z₀ := ⟨z', hz'⟩
  have hzc : pointMap F Z₀.toGrp G (Adeles F) c z' = positivePointMap F G Z₀ c c₀ := rfl
  refine ⟨w, hw, ?_⟩
  set p := E.symm w with hp
  have hw' : w = positivePointMap F G Z₀ c p.1 * (p.2 : AdelicGroupPoints F G) := by
    rw [← splitComponentNormOneDecomposition_apply centralSplitTorusCharacter F G hG Z₀ c hc p]
    exact (E.apply_symm_apply w).symm
  have hE1 : E (c₀ * p.1, p.2) = pointMap F Z₀.toGrp G (Adeles F) c z' * w := by
    rw [splitComponentNormOneDecomposition_apply, map_mul, hzc, hw', mul_assoc]
  have hE2 : E (1, ⟨_, hzw⟩) = pointMap F Z₀.toGrp G (Adeles F) c z' * w := by
    rw [splitComponentNormOneDecomposition_apply, map_one, one_mul]
  have heq := congrArg Prod.fst (E.injective (hE1.trans hE2.symm))
  have hc₀ : c₀ = p.1⁻¹ := eq_inv_of_mul_eq_one_left heq
  change (positivePointMap F G Z₀ c p.1)⁻¹ = pointMap F Z₀.toGrp G (Adeles F) c z'
  rw [hzc, hc₀, map_inv]

end Centre

section SiegelPoints

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  {ν : cocharacterLattice T} {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ T}

/-- **Norm-one Siegel points as torus points times a compact set.** For a closed matrix
embedding `rho`, compact factors `C`, a threshold `t` and a compact `Ω`, there is a compact
`Y ⊆ G(𝔸)` such that every point `x ∈ G(𝔸)¹` of the Siegel set of `(C, t, Ω)` with torus
coordinate `a` is `a · y` with `y ∈ Y`. Write `x = z · n m a k · w`. Then `z w ∈ G(𝔸)¹`, so
`z` lies in a compact set (`exists_isCompact_canonicalSubgroup_of_mul_mem_normOne`); the
conjugates `a⁻¹ n a` lie in a compact set (`exists_isCompact_conj_unipotent`); `m` commutes with
`a` and `z` is central, so `x = a · z (a⁻¹ n a) m k w`. -/
theorem exists_isCompact_siegelPoint_eq_mul (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hrho : IsClosedSubgroup rho)
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t : ℝ≥0ˣ) {Ω : Set (AdelicGroupPoints F G)} (hΩ : IsCompact Ω) :
    ∃ Y : Set (AdelicGroupPoints F G), IsCompact Y ∧
      ∀ (a : intrinsicSubgroup F T₀) (x : AdelicGroupPoints F G),
        IsSiegelPoint F G T i ν T₀ j C t Ω a x → x ∈ normOneSubgroup F G →
          ∃ y ∈ Y, x = positiveMap F G T i T₀ j a * y := by
  have hlevi : standardLevi i ν ∅ = torusCentralizer i := hsetup.2.2.2.2.2.1
  obtain ⟨Z₀, zc, hzc, -⟩ := hsetup.2.2.2.2.2.2.2.2
  obtain ⟨Z, hZ, hZmem⟩ :=
    exists_isCompact_canonicalSubgroup_of_mul_mem_normOne hG
      (CommGroupScheme.groupHom zc ≫ i) hzc hΩ
  obtain ⟨S, hS, hSmem⟩ :=
    exists_isCompact_conj_unipotent hG hsetup rho hrho C.omegaN C.compact_omegaN t
  let ιN := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅)
  let ιM : normOneSubgroup F (Standard.leviScheme i ν ∅) → AdelicGroupPoints F G :=
    fun m => map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m
  have hιM : Continuous ιM :=
    (map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅)).continuous.comp
      continuous_subtype_val
  let Ω' : Set (AdelicGroupPoints F G) :=
    Z * (S * (ιM '' C.omegaM) * (C.compactSubgroup : Set (AdelicGroupPoints F G)) * Ω)
  have hΩ' : IsCompact Ω' :=
    hZ.mul (((hS.mul (C.compact_omegaM.image hιM)).mul C.compact_compactSubgroup).mul hΩ)
  refine ⟨Ω', hΩ', fun a x hx hx1 => ?_⟩
  obtain ⟨z, hz, n', hn', m, hm, ha, k, hk, w, hw, rfl⟩ := hx
  set A := positiveMap F G T i T₀ j a with hA
  have hzc' : z ∈ Subgroup.center (AdelicGroupPoints F G) :=
    RestrictionSplitCentre.canonicalSubgroup_le_center F G hz
  have hcomm : Commute (ιM m) A :=
    commute_of_mem_standardLevi_image F G T i ν T₀ j hlevi (CommAlgCat.of F (Adeles F))
      (ιM m) ⟨m.val, rfl⟩ a.val
  set p := ιN n' * ιM m * A * k with hp
  have hp1 : p ∈ normOneSubgroup F G :=
    IsSiegelAlgebraicSetup.weakSiegelProduct_subset_normOne F G T i ν T₀ j C hsetup t
      ((mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j _ p).mpr ⟨n', hn', m, hm, a, ha, k, hk, rfl⟩)
  have hzw : z * w ∈ normOneSubgroup F G := by
    have he : z * w = p⁻¹ * (z * p * w) := by
      rw [← (Subgroup.mem_center_iff.mp hzc' p)]
      group
    rw [he]
    exact (normOneSubgroup F G).mul_mem ((normOneSubgroup F G).inv_mem hp1) hx1
  have hzZ : z ∈ Z := hZmem z hz w hw hzw
  refine ⟨z * (A⁻¹ * ιN n' * A * ιM m * k * w),
    Set.mul_mem_mul hzZ (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (hSmem n' hn' a ha)
      ⟨m, hm, rfl⟩) hk) hw), ?_⟩
  have hzA : z * A = A * z := (Subgroup.mem_center_iff.mp hzc' A).symm
  calc z * p * w = z * (ιN n' * (ιM m * A) * k) * w := by
        simp only [hp, mul_assoc]
    _ = z * (ιN n' * (A * ιM m) * k) * w := by rw [hcomm.eq]
    _ = z * A * (A⁻¹ * ιN n' * A * ιM m * k * w) := by group
    _ = A * (z * (A⁻¹ * ιN n' * A * ιM m * k * w)) := by rw [hzA, mul_assoc]

end SiegelPoints

end Langlands.Global

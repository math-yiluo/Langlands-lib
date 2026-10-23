import Langlands.Galois.Local.TotallyRamifiedSolvabilityStatement
import Langlands.Galois.Local.UnramifiedCriterionProof
import Langlands.LocalFactor.Ramification.Galois

/-!
# Proof of solvability of totally ramified finite local Galois groups

For a group acting on a local ring, commutators of `G_i` lie in `G_{2i}`. For a discrete
valuation ring whose residue classes have representatives fixed by the whole group, the
action on a uniformizer gives a homomorphism from `G_0` to the commutative residue field,
whose kernel lies in `G_1`, and `G_0` is the whole group. Hence the derived series lies in
the lower filtration, which terminates. Total ramification of `E/F`, expressed by the
canonical absolute ramification indices, makes the relative residue degree one, so
elements of `F` supply the fixed representatives.
-/

noncomputable section

namespace Langlands.Ramification

open IsLocalRing
open scoped commutatorElement

universe u v

section Generic

variable {R : Type u} {G : Type v} [CommRing R] [IsLocalRing R] [Group G]
  [MulSemiringAction G R]

/-- Every group element preserves each power of the maximal ideal. -/
theorem smul_mem_maximalIdeal_pow {n : ℕ} (g : G) {x : R} (hx : x ∈ maximalIdeal R ^ n) :
    g • x ∈ maximalIdeal R ^ n := by
  have hmap : (maximalIdeal R).map (MulSemiringAction.toRingAut G R g).toRingHom =
      maximalIdeal R :=
    map_maximalIdeal_of_surjective _ (MulSemiringAction.toRingAut G R g).surjective
  have := Ideal.mem_map_of_mem (MulSemiringAction.toRingAut G R g).toRingHom hx
  rw [Ideal.map_pow, hmap] at this
  exact this

theorem smul_mem_maximalIdeal (g : G) {x : R} (hx : x ∈ maximalIdeal R) :
    g • x ∈ maximalIdeal R := by
  have h := smul_mem_maximalIdeal_pow (n := 1) g (x := x) (by rw [pow_one]; exact hx)
  rwa [pow_one] at h

/-- An element of `congruenceGroup (i + 1)` moves `m ^ k` into `m ^ (k + i)` for `k ≥ 1`. -/
theorem smul_sub_mem_pow_add {i : ℕ} {g : G} (hg : g ∈ congruenceGroup R G (i + 1)) :
    ∀ {k : ℕ}, 1 ≤ k → ∀ {x : R}, x ∈ maximalIdeal R ^ k →
      g • x - x ∈ maximalIdeal R ^ (k + i) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro x _
    rw [add_comm]
    exact hg x
  | succ k _ ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      have e : g • (a * b) - a * b = (g • a - a) * (g • b) + a * (g • b - b) := by
        rw [smul_mul']
        ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · have h1 : (g • a - a) * (g • b) ∈ maximalIdeal R ^ (k + i) * maximalIdeal R :=
          Ideal.mul_mem_mul (ih ha) (smul_mem_maximalIdeal g hb)
        rwa [← pow_succ, show k + i + 1 = k + 1 + i by omega] at h1
      · have h1 : a * (g • b - b) ∈ maximalIdeal R ^ k * maximalIdeal R ^ (1 + i) :=
          Ideal.mul_mem_mul ha (by rw [add_comm]; exact hg b)
        rwa [← pow_add, show k + (1 + i) = k + 1 + i by omega] at h1
    · intro x y hx hy
      rw [smul_add, add_sub_add_comm]
      exact Ideal.add_mem _ hx hy

/-- Commutators of two elements of `congruenceGroup (i + 1)` lie in
`congruenceGroup (2 * i + 1)`. -/
theorem commutatorElement_mem_congruenceGroup {i : ℕ} {g h : G}
    (hg : g ∈ congruenceGroup R G (i + 1)) (hh : h ∈ congruenceGroup R G (i + 1)) :
    ⁅g, h⁆ ∈ congruenceGroup R G (2 * i + 1) := by
  intro x
  obtain ⟨z, rfl⟩ : ∃ z, x = h • g • z := ⟨g⁻¹ • h⁻¹ • x, by simp⟩
  have e1 : ⁅g, h⁆ • h • g • z = g • h • z := by
    simp only [commutatorElement_def, mul_smul, inv_smul_smul]
  have e2 : g • h • z - h • g • z =
      (g • (h • z - z) - (h • z - z)) - (h • (g • z - z) - (g • z - z)) := by
    simp only [smul_sub]
    abel
  have a1 := smul_sub_mem_pow_add hg (k := i + 1) (by omega) (hh z)
  have a2 := smul_sub_mem_pow_add hh (k := i + 1) (by omega) (hg z)
  rw [e1, e2, show 2 * i + 1 = i + 1 + i by omega]
  exact sub_mem a1 a2

/-- Commutators of `G_i` lie in `G_{2i}`. -/
theorem commutator_lowerGroup_le (i : ℕ) :
    ⁅lowerGroup R G i, lowerGroup R G i⁆ ≤ lowerGroup R G (2 * i) :=
  Subgroup.commutator_le.mpr fun _ hg _ hh => commutatorElement_mem_congruenceGroup hg hh

/-- For `i ≥ 1`, the quotient `G_i / G_{i+1}` is abelian. -/
theorem commutator_lowerGroup_le_succ {i : ℕ} (hi : 1 ≤ i) :
    ⁅lowerGroup R G i, lowerGroup R G i⁆ ≤ lowerGroup R G (i + 1) :=
  (commutator_lowerGroup_le i).trans (lowerGroup_antitone R G (by omega))

section Uniformizer

variable [IsDomain R] {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ})

omit [IsDomain R] in
include hϖ in
theorem exists_smul_uniformizer_eq (g : G) : ∃ u : R, g • ϖ = ϖ * u := by
  have hm : ϖ ∈ maximalIdeal R := by
    rw [hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  have h := smul_mem_maximalIdeal g hm
  rw [hϖ, Ideal.mem_span_singleton'] at h
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by rw [← hu, mul_comm]⟩

/-- The unit factor `u` with `g • ϖ = ϖ * u`. -/
def uniformizerFactor (g : G) : R := (exists_smul_uniformizer_eq hϖ g).choose

omit [IsDomain R] in
theorem smul_uniformizer (g : G) : g • ϖ = ϖ * uniformizerFactor hϖ g :=
  (exists_smul_uniformizer_eq hϖ g).choose_spec

variable (hϖ0 : ϖ ≠ 0)

/-- The action of `G_0` on a uniformizer, read in the residue field. -/
def uniformizerCharacter : lowerGroup R G 0 →* ResidueField R where
  toFun g := residue R (uniformizerFactor hϖ (g : G))
  map_one' := by
    have h := smul_uniformizer hϖ (1 : G)
    rw [one_smul] at h
    have h1 : uniformizerFactor hϖ (1 : G) = 1 :=
      mul_left_cancel₀ hϖ0 (h.symm.trans (mul_one ϖ).symm)
    simp [h1]
  map_mul' g h := by
    have e : uniformizerFactor hϖ ((g : G) * h) =
        uniformizerFactor hϖ (g : G) * ((g : G) • uniformizerFactor hϖ (h : G)) := by
      apply mul_left_cancel₀ hϖ0
      rw [← smul_uniformizer, mul_smul, smul_uniformizer hϖ (h : G), smul_mul',
        smul_uniformizer hϖ (g : G), mul_assoc]
    have hg : (g : G) ∈ congruenceGroup R G (0 + 1) := g.2
    have hres : residue R ((g : G) • uniformizerFactor hϖ (h : G)) =
        residue R (uniformizerFactor hϖ (h : G)) := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      simpa using hg (uniformizerFactor hϖ (h : G))
    simp only [Subgroup.coe_mul, e, map_mul, hres]

/-- On the kernel of the uniformizer character, `ϖ` moves by an element of `m ^ 2`. -/
theorem smul_uniformizer_sub_mem_of_eq_one {g : lowerGroup R G 0}
    (h : uniformizerCharacter hϖ hϖ0 g = 1) :
    (g : G) • ϖ - ϖ ∈ maximalIdeal R ^ 2 := by
  rw [smul_uniformizer hϖ, ← mul_sub_one, pow_two]
  apply Ideal.mul_mem_mul
  · rw [hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  · rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
    exact h

variable (hrep : ∀ x : R, ∃ a : R, (∀ g : G, g • a = a) ∧ x - a ∈ maximalIdeal R)

omit [IsDomain R] in
include hrep in
/-- With fixed residue representatives, `G_0` is the whole group. -/
theorem lowerGroup_zero_eq_top_of_fixed : lowerGroup R G 0 = ⊤ := by
  refine eq_top_iff.mpr fun g _ x => ?_
  obtain ⟨a, ha, hxa⟩ := hrep x
  have e : g • x - x = g • (x - a) - (x - a) := by
    rw [smul_sub, ha g]
    abel
  rw [e, zero_add, pow_one]
  exact sub_mem (smul_mem_maximalIdeal g hxa) hxa

omit [IsDomain R] in
include hϖ hrep in
/-- With fixed residue representatives, an element of `G_0` moving `ϖ` by an element of
`m ^ 2` lies in `G_1`. -/
theorem mem_lowerGroup_one_of_fixed {g : G} (hg : g ∈ lowerGroup R G 0)
    (hgϖ : g • ϖ - ϖ ∈ maximalIdeal R ^ 2) : g ∈ lowerGroup R G 1 := by
  intro x
  obtain ⟨a, ha, hxa⟩ := hrep x
  rw [hϖ, Ideal.mem_span_singleton'] at hxa
  obtain ⟨b, hb⟩ := hxa
  have hx : x = a + b * ϖ := by rw [hb]; ring
  have e : g • x - x = (g • b) * (g • ϖ - ϖ) + (g • b - b) * ϖ := by
    rw [hx, smul_add, ha g, smul_mul']
    ring
  have hg' : g ∈ congruenceGroup R G (0 + 1) := hg
  have hb' : g • b - b ∈ maximalIdeal R := by simpa using hg' b
  have hϖm : ϖ ∈ maximalIdeal R := by
    rw [hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  rw [e, show 1 + 1 = 2 from rfl]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hgϖ) ?_
  rw [pow_two]
  exact Ideal.mul_mem_mul hb' hϖm

include hϖ hϖ0 hrep in
/-- With fixed residue representatives, `G_0 / G_1` is abelian. -/
theorem commutator_lowerGroup_zero_le_of_fixed :
    ⁅lowerGroup R G 0, lowerGroup R G 0⁆ ≤ lowerGroup R G 1 := by
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  let g' : lowerGroup R G 0 := ⟨g, hg⟩
  let h' : lowerGroup R G 0 := ⟨h, hh⟩
  have hθ : uniformizerCharacter hϖ hϖ0 ⁅g', h'⁆ = 1 := by
    have hu : (uniformizerCharacter hϖ hϖ0).toHomUnits ⁅g', h'⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
    have hv := congrArg Units.val hu
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at hv
  exact mem_lowerGroup_one_of_fixed hϖ hrep (⁅g', h'⁆).2
    (smul_uniformizer_sub_mem_of_eq_one hϖ hϖ0 hθ)

include hϖ hϖ0 hrep in
/-- The derived series lies in the lower ramification filtration. -/
theorem derivedSeries_le_lowerGroup_of_fixed (n : ℕ) :
    derivedSeries G n ≤ lowerGroup R G n := by
  induction n with
  | zero => rw [derivedSeries_zero, lowerGroup_zero_eq_top_of_fixed hrep]
  | succ n ih =>
    rw [derivedSeries_succ]
    refine (Subgroup.commutator_mono ih ih).trans ?_
    rcases n with _ | n
    · exact commutator_lowerGroup_zero_le_of_fixed hϖ hϖ0 hrep
    · exact commutator_lowerGroup_le_succ (by omega)

include hϖ hϖ0 hrep in
/-- A terminating lower filtration with fixed residue representatives gives solvability. -/
theorem isSolvable_of_fixed (hbot : ∃ b : ℕ, lowerGroup R G b = ⊥) : Group.IsSolvable G := by
  obtain ⟨b, hb⟩ := hbot
  exact ⟨⟨b, le_bot_iff.mp (hb ▸ derivedSeries_le_lowerGroup_of_fixed hϖ hϖ0 hrep b)⟩⟩

end Uniformizer

end Generic

end Langlands.Ramification

namespace Langlands.PadicField

open Langlands.Weil.Local LocalClassField Langlands.Ramification IsLocalRing

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (E : FiniteIntermediateExtension F.Carrier)

local notation "EP" => E.asPadicField (p := p)

local instance : Algebra (Padic p) E.field := (EP).algebra

local instance : IsScalarTower (Padic p) F.Carrier E.field :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The degree of the published embedding is the actual degree of `E` over `F`. -/
theorem extensionDegree_intermediateEmbedding :
    extensionDegree F EP (intermediateEmbedding F E) = Module.finrank F.Carrier E.field := by
  have h : extensionAlgebra F EP (intermediateEmbedding F E) =
      (inferInstance : Algebra F.Carrier E.field) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold extensionDegree
  rw [h]

/-- Under the arithmetic hypothesis, the relative residue degree is one. -/
theorem extensionResidueDegree_eq_one_of_ramificationIndex
    (h : (EP).canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier E.field * F.canonicalTopologicalData.ramificationIndex) :
    extensionResidueDegree F EP (intermediateEmbedding F E) = 1 := by
  have key := ramificationIndex_mul_extensionResidueDegree F EP (intermediateEmbedding F E)
  rw [extensionDegree_intermediateEmbedding, ← h] at key
  exact Nat.eq_of_mul_eq_mul_left (EP).canonicalTopologicalData.ramificationIndex_pos
    (key.trans (mul_one _).symm)

/-- With relative residue degree one, images of integers of `F` represent every residue
class of `E` and are fixed by every automorphism of `E` over `F`. -/
theorem fixedResidueRepresentatives
    (hres : extensionResidueDegree F EP (intermediateEmbedding F E) = 1) :
    letI := Padic.integerAction (EP).canonicalTopologicalData F.Carrier
    ∀ x : (EP).canonicalTopologicalData.Integers, ∃ a : (EP).canonicalTopologicalData.Integers,
      (∀ σ : Gal(E.field/F.Carrier), σ • a = a) ∧
        x - a ∈ maximalIdeal (EP).canonicalTopologicalData.Integers := by
  let := Padic.integerAction (EP).canonicalTopologicalData F.Carrier
  let := extensionResidueAlgebra F EP (intermediateEmbedding F E)
  intro x
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : (EP).canonicalTopologicalData.ResidueField)
    one_ne_zero).mp hres ((EP).canonicalTopologicalData.residue x)
  obtain ⟨y, rfl⟩ := residue_surjective c
  refine ⟨extensionIntegerMap F EP (intermediateEmbedding F E) y, fun σ => ?_, ?_⟩
  · apply Subtype.ext
    exact σ.commutes (y : F.Carrier)
  · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, ← hc, Algebra.smul_def, mul_one]
    rfl

/-- With relative residue degree one, the actual Galois group is solvable. -/
theorem isSolvable_of_extensionResidueDegree_eq_one
    (hres : extensionResidueDegree F EP (intermediateEmbedding F E) = 1) :
    Group.IsSolvable Gal(E.field/F.Carrier) := by
  let := Padic.integerAction (EP).canonicalTopologicalData F.Carrier
  have : IsDiscreteValuationRing (EP).canonicalTopologicalData.Integers := by
    let := (EP).canonicalTopologicalData.topology
    let := (EP).canonicalTopologicalData.valuativeRel
    let := (EP).canonicalTopologicalData.localField
    infer_instance
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (EP).canonicalTopologicalData.Integers
  obtain ⟨b, hb⟩ :=
    Padic.exists_lowerRamificationGroup_eq_bot (EP).canonicalTopologicalData F.Carrier
  exact isSolvable_of_fixed hϖ.maximalIdeal_eq hϖ.ne_zero (fixedResidueRepresentatives F E hres)
    ⟨b, hb b le_rfl⟩

/-- Solvability of finite totally ramified Galois groups. -/
theorem totallyRamifiedGaloisSolvability : TotallyRamifiedGaloisSolvability.{u} := by
  intro p _ F E _ _ h
  exact isSolvable_of_extensionResidueDegree_eq_one F E
    (extensionResidueDegree_eq_one_of_ramificationIndex F E h)

end Langlands.PadicField

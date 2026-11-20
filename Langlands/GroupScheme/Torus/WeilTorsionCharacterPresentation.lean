import Langlands.GroupScheme.Torus.TorusTorsionCharacters
import Mathlib.Data.ZMod.Basic

/-! # Embedding presentations of the actual Weil and norm-one torsion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Algebra.SeparableTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

private abbrev multiples (V : Type u) [AddCommGroup V] (n : ℕ) : Submodule ℤ V :=
  ((n : ℤ) • (LinearMap.id : V →ₗ[ℤ] V)).range

private theorem ker_comp_multiples_of_surjective
    {V W M : Type u} [AddCommGroup V] [AddCommGroup W] [AddCommGroup M]
    (f : V →ₗ[ℤ] W) (g : W →ₗ[ℤ] M) (hf : Function.Surjective f) {n : ℕ}
    (hg : g.ker = multiples W n) :
    (g.comp f).ker = f.ker ⊔ multiples V n := by
  apply le_antisymm
  · intro x hx
    have hm : f x ∈ multiples W n := by
      rw [← hg]
      exact hx
    obtain ⟨y, hy⟩ := hm
    obtain ⟨z, rfl⟩ := hf y
    change (n : ℤ) • f z = f x at hy
    refine Submodule.mem_sup.mpr ⟨x - (n : ℤ) • z, ?_, (n : ℤ) • z, ⟨z, rfl⟩, sub_add_cancel _ _⟩
    change f (x - (n : ℤ) • z) = 0
    rw [map_sub, map_smul, hy, sub_self]
  · apply sup_le
    · intro x hx
      change g (f x) = 0
      rw [LinearMap.mem_ker.mp hx, map_zero]
    · rintro _ ⟨x, rfl⟩
      change g (f ((n : ℤ) • x)) = 0
      rw [map_smul, ← LinearMap.mem_ker, hg]
      exact ⟨f x, rfl⟩

namespace characterLattice

variable {k : Type u} [Field k] (T : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "Ω" => SeparableClosure k
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k Ω)
local notation "X" => characterLattice (Functor.obj (BC) T)
local notation "Tₙ" n =>
  Functor.obj (CommGroupScheme.torsionFunctor (S := Spec (CommRingCat.of k)) n) T

theorem torusTorsionRestriction_surjective (hT : IsTorus T.toGrp) {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (torusTorsionRestriction T n) := by
  intro χ
  obtain ⟨q, hq⟩ := (torusTorsionCharacterEquiv T hT hn).surjective χ
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨a, hq⟩

private def moduloCoordinates {I : Type u} (e : X ≃ₗ[ℤ] (I → ℤ)) (n : ℕ) :
    X →ₗ[ℤ] (I → ZMod n) :=
  (LinearMap.pi (fun (i : I) => (Int.castAddHom (ZMod n)).toIntLinearMap.comp
    (LinearMap.proj i))).comp e.toLinearMap

private theorem moduloCoordinates_surjective {I : Type u} (e : X ≃ₗ[ℤ] (I → ℤ)) (n : ℕ) :
    Function.Surjective (moduloCoordinates T e n) := by
  intro x
  choose a ha using fun i => ZMod.intCast_surjective (x i)
  refine ⟨e.symm a, ?_⟩
  funext i
  change ((e (e.symm a) i : ℤ) : ZMod n) = x i
  rw [LinearEquiv.apply_symm_apply]
  exact ha i

private theorem ker_moduloCoordinates {I : Type u} (e : X ≃ₗ[ℤ] (I → ℤ)) (n : ℕ) :
    (moduloCoordinates T e n).ker = multiples X n := by
  ext x
  change moduloCoordinates T e n x = 0 ↔ ∃ a : X, (n : ℤ) • a = x
  constructor
  · intro h
    have hz (i : I) : ((e x i : ℤ) : ZMod n) = 0 := congrFun h i
    choose v hv using fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hz i)
    refine ⟨e.symm v, e.injective ?_⟩
    rw [map_smul, LinearEquiv.apply_symm_apply]
    funext i
    exact (hv i).symm
  · rintro ⟨a, rfl⟩
    funext i
    change ((e ((n : ℤ) • a) i : ℤ) : ZMod n) = 0
    rw [map_smul]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨e a i, rfl⟩

/-- If the geometric torus characters are in integral coordinates `I`,
its actual torsion characters are in the same coordinates modulo `n`. -/
def torusTorsionCharacterCoordinates (hT : IsTorus T.toGrp) {I : Type u}
    (e : X ≃ₗ[ℤ] (I → ℤ)) {n : ℕ} (hn : n ≠ 0) :
    characterLattice ((BC).obj (Tₙ (n : ℤ))) ≃ₗ[ℤ] (I → ZMod n) :=
  (torusTorsionCharacterEquiv T hT (Int.natCast_ne_zero.mpr hn)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_moduloCoordinates T e n).symm).trans
      ((moduloCoordinates T e n).quotKerEquivOfSurjective (moduloCoordinates_surjective T e n)))

end characterLattice

namespace WeilGm

variable (k B : Type u) [Field k] [Field B] [Algebra k B] [FiniteDimensional k B]
  [Algebra.IsSeparable k B]

local notation "Ω" => SeparableClosure k
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k Ω)
local notation "W" => commGroupScheme (CommRingCat.of k) B
local notation "N" => normOneCommGroupScheme (CommRingCat.of k) B
local notation "Tₙ" n => CommGroupScheme.torsionFunctor (S := Spec (CommRingCat.of k)) (n : ℤ)
local notation "E" => (B →ₐ[k] Ω)
local notation "V" => (E → ℤ)

private abbrev splitMinpolys := separable_minpoly_splits k B Ω

private abbrev weilCoordinates : characterLattice ((BC).obj W) ≃ₗ[ℤ] V :=
  (separableEmbeddingCharacterEquiv k B Ω (splitMinpolys k B)).toIntLinearEquiv

/-- Embedding characters restricted to the actual Weil torsion. -/
def weilTorsionEmbeddingCharacter (n : ℕ) :
    V →ₗ[ℤ] characterLattice ((BC).obj ((Tₙ n).obj W)) :=
  (characterLattice.torusTorsionRestriction W (n : ℤ)).comp (weilCoordinates k B).symm.toLinearMap

/-- Ambient embedding characters restricted to the actual norm-one torsion. -/
def normOneTorsionEmbeddingCharacter (n : ℕ) :
    V →ₗ[ℤ] characterLattice ((BC).obj ((Tₙ n).obj N)) :=
  (characterLattice.torusTorsionRestriction N (n : ℤ)).comp
    (normOneEmbeddingCharacterRestriction k B Ω (splitMinpolys k B))

theorem weilTorsionEmbeddingCharacter_surjective {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (weilTorsionEmbeddingCharacter k B n) :=
  (characterLattice.torusTorsionRestriction_surjective W (isTorus_of_finite_separable k B)
    (Int.natCast_ne_zero.mpr hn)).comp (weilCoordinates k B).symm.surjective

theorem normOneTorsionEmbeddingCharacter_surjective {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (normOneTorsionEmbeddingCharacter k B n) :=
  (characterLattice.torusTorsionRestriction_surjective N (normOne_isTorus_of_finite_separable k B)
    (Int.natCast_ne_zero.mpr hn)).comp
    (normOneEmbeddingCharacterRestriction_surjective k B Ω (splitMinpolys k B))

theorem ker_weilTorsionEmbeddingCharacter {n : ℕ} (hn : n ≠ 0) :
    (weilTorsionEmbeddingCharacter k B n).ker = multiples V n := by
  unfold weilTorsionEmbeddingCharacter
  rw [ker_comp_multiples_of_surjective _ _ (weilCoordinates k B).symm.surjective
      (characterLattice.ker_torusTorsionRestriction W (isTorus_of_finite_separable k B)
        (Int.natCast_ne_zero.mpr hn)),
    LinearMap.ker_eq_bot.mpr (weilCoordinates k B).symm.injective, bot_sup_eq]

theorem ker_normOneTorsionEmbeddingCharacter {n : ℕ} (hn : n ≠ 0) :
    (normOneTorsionEmbeddingCharacter k B n).ker = embeddingDiagonal k B Ω ⊔ multiples V n := by
  unfold normOneTorsionEmbeddingCharacter
  rw [ker_comp_multiples_of_surjective _ _
      (normOneEmbeddingCharacterRestriction_surjective k B Ω (splitMinpolys k B))
      (characterLattice.ker_torusTorsionRestriction N (normOne_isTorus_of_finite_separable k B)
        (Int.natCast_ne_zero.mpr hn)),
    normOneEmbeddingCharacterRestriction_ker]

/-- The geometric Weil torsion characters have order `n` to the power of the
field degree. -/
theorem natCard_weilTorsionCharacter {n : ℕ} (hn : n ≠ 0) :
    Nat.card (characterLattice ((BC).obj ((Tₙ n).obj W))) = n ^ Module.finrank k B := by
  let e := characterLattice.torusTorsionCharacterCoordinates W (isTorus_of_finite_separable k B)
    (weilCoordinates k B) hn
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, separableEmbedding_card k B Ω (splitMinpolys k B)]

/-- The geometric norm-one torsion has one fewer independent exponent than
the ambient Weil torsion. -/
theorem natCard_normOneTorsionCharacter {n : ℕ} (hn : n ≠ 0) :
    Nat.card (characterLattice ((BC).obj ((Tₙ n).obj N))) = n ^ (Module.finrank k B - 1) := by
  obtain ⟨a⟩ := separableEmbedding_nonempty k B Ω (splitMinpolys k B)
  let iso := normOneSeparableEmbeddingCommIso k B Ω (splitMinpolys k B) a
  let e := characterLattice.torusTorsionCharacterCoordinates N
    (normOne_isTorus_of_finite_separable k B)
    (((characterLattice.congr iso).trans
      (splitTorus.characterLatticeEquiv Ω {b : E // b ≠ a})).toIntLinearEquiv) hn
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod,
    normOneSeparableEmbedding_card k B Ω (splitMinpolys k B) a]

/-- The Weil torsion presentation is Galois equivariant for the embedding
permutation representation. -/
theorem galoisRepresentation_weilTorsionEmbeddingCharacter
    (n : ℕ) (σ : Ω ≃ₐ[k] Ω) (a : V) :
    characterLattice.galoisRepresentation k Ω ((Tₙ n).obj W) σ
        (weilTorsionEmbeddingCharacter k B n a) =
      weilTorsionEmbeddingCharacter k B n (embeddingPermutationRepresentation k B Ω σ a) := by
  change characterLattice.galoisRepresentation k Ω ((Tₙ n).obj W) σ
      (((BC).map ((CommGroupScheme.torsionInclusion (n : ℤ)).app W)) ≫
        (weilCoordinates k B).symm a) =
    ((BC).map ((CommGroupScheme.torsionInclusion (n : ℤ)).app W)) ≫
      (weilCoordinates k B).symm (embeddingPermutationRepresentation k B Ω σ a)
  rw [characterLattice.galoisRepresentation_precompose]
  simp only [Functor.id_obj]
  congr 1
  apply (separableEmbeddingCharacterEquiv k B Ω (splitMinpolys k B)).injective
  rw [separableEmbeddingCharacterEquiv_galoisRepresentation]
  simp [weilCoordinates]

/-- The norm-one torsion presentation is equivariant for the same embedding
permutation representation. -/
theorem galoisRepresentation_normOneTorsionEmbeddingCharacter
    (n : ℕ) (σ : Ω ≃ₐ[k] Ω) (a : V) :
    characterLattice.galoisRepresentation k Ω ((Tₙ n).obj N) σ
        (normOneTorsionEmbeddingCharacter k B n a) =
      normOneTorsionEmbeddingCharacter k B n (embeddingPermutationRepresentation k B Ω σ a) := by
  change characterLattice.galoisRepresentation k Ω ((Tₙ n).obj N) σ
      (((BC).map ((CommGroupScheme.torsionInclusion (n : ℤ)).app N)) ≫
        normOneEmbeddingCharacterRestriction k B Ω (splitMinpolys k B) a) =
    ((BC).map ((CommGroupScheme.torsionInclusion (n : ℤ)).app N)) ≫
      normOneEmbeddingCharacterRestriction k B Ω (splitMinpolys k B)
        (embeddingPermutationRepresentation k B Ω σ a)
  rw [characterLattice.galoisRepresentation_precompose]
  simp only [Functor.id_obj, galoisRepresentation_normOneEmbeddingCharacterRestriction]

end WeilGm

end Langlands.GroupScheme

import Langlands.Geometry.Building.RootDatumValuation
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.GroupScheme.Rational.RootSubgroupStability

/-! # V0 from actual torus conjugation and nonidentity root points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  {i : S.toGrp ⟶ G} {φ : RootFunctionFamily S G}
  (ω : kˣ →* Multiplicative ℝ)

/-- Integral powers of an actual torus point give an injective sequence in the
actual root-value image. No V0 or root-valuation premise is used. -/
def IsSplitTorusCompatible.rootValueEmbedding
    (hφ : IsSplitTorusCompatible i (fun b => (ω b).toAdd) φ)
    (hS : IsSplitTorus S.toGrp) (hω : ∃ b, (ω b).toAdd ≠ 0)
    (htop : ∀ a ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i a,
      φ a g = ⊤ ↔ g = 1)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    ℤ ↪ (φ a '' (rootGroupPoints i a : Set (rationalPoints G))) := by
  choose u hu hu1 using RelativeRoot.exists_rootPoint_actual hS i ha
  choose r hr using WithTop.ne_top_iff_exists.mp (mt (htop a ha u hu).mp hu1)
  choose b hb using hω
  choose D hD c hc using hS.exists_pairing_eq_pos ha.1
  let s := CocharacterUniformizer.cocharacterPoints k S c b
  let δ : ℝ := (ω (rationalCharacterEval
    ((rationalCharacters.equivCharacterLattice S).symm a) s)).toAdd
  have hδ : δ ≠ 0 := by
    dsimp [δ, s]
    rw [CocharacterUniformizer.rationalCharacterEval_cocharacterPoints,
      map_zpow, toAdd_zpow, hc]
    simpa only [zsmul_eq_mul, Int.cast_natCast] using
      mul_ne_zero (by exact_mod_cast hD.ne' : (D : ℝ) ≠ 0) hb
  let x : ℤ → rationalPoints G := fun n =>
    (rationalPoints.map i (s ^ n))⁻¹ * u * rationalPoints.map i (s ^ n)
  have hx (n : ℤ) : x n ∈ rootGroupPoints i a := by
    have h := RelativeRoot.subgroup_isStable i a (Over.mk (𝟙 _)) ((s ^ n)⁻¹) u hu
    simpa only [rootGroupPoints, AutomorphicAction.conjugation_act,
      ← rationalPoints.map_apply, map_inv, inv_inv] using h
  have hvalue (n : ℤ) : φ a (x n) = ((r - (n : ℝ) * δ : ℝ) : WithTop ℝ) := by
    change φ a ((rationalPoints.map i (s ^ n))⁻¹ * u *
      rationalPoints.map i (s ^ n)) = _
    rw [hφ a ha (s ^ n) u hu, ← hr]
    simp only [map_zpow, toAdd_zpow, zsmul_eq_mul, ← WithTop.coe_add,
      sub_eq_add_neg, δ]
  refine ⟨fun n => ⟨((r - (n : ℝ) * δ : ℝ) : WithTop ℝ),
    x n, hx n, hvalue n⟩, ?_⟩
  intro m n h
  have hreal := WithTop.coe_injective (congrArg Subtype.val h)
  have hprod : (m : ℝ) * δ = (n : ℝ) * δ := by linarith
  have hcast : (m : ℝ) = n := mul_right_cancel₀ hδ hprod
  exact_mod_cast hcast

/-- The constructed torus-conjugation sequence gives infinitely many values on
every actual relative root group. -/
theorem IsSplitTorusCompatible.image_infinite
    (hφ : IsSplitTorusCompatible i (fun b => (ω b).toAdd) φ)
    (hS : IsSplitTorus S.toGrp) (hω : ∃ b, (ω b).toAdd ≠ 0)
    (htop : ∀ a ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i a,
      φ a g = ⊤ ↔ g = 1)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    (φ a '' (rootGroupPoints i a : Set (rationalPoints G))).Infinite := by
  let e := hφ.rootValueEmbedding ω hS hω htop ha
  exact Set.infinite_of_injective_forall_mem
    (Subtype.val_injective.comp e.injective) (fun n => (e n).property)

/-- In particular V0 follows from actual split-torus compatibility, a nontrivial
additive unit character, and the identity criterion on the actual root groups. -/
theorem IsSplitTorusCompatible.three_le_encard
    (hφ : IsSplitTorusCompatible i (fun b => (ω b).toAdd) φ)
    (hS : IsSplitTorus S.toGrp) (hω : ∃ b, (ω b).toAdd ≠ 0)
    (htop : ∀ a ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i a,
      φ a g = ⊤ ↔ g = 1)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    3 ≤ (φ a '' (rootGroupPoints i a : Set (rationalPoints G))).encard := by
  rw [(hφ.image_infinite ω hS hω htop ha).encard_eq]
  exact le_top

end Langlands.Geometry.Building

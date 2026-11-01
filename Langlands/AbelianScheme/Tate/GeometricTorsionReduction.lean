import Langlands.AbelianScheme.Tate.GeometricTorsionRankStatement
import Langlands.AbelianScheme.Tate.IntegralBaseChange
import Langlands.AbelianScheme.Tate.LevelStructureFromCardinality

/-! # Actual fibre comparisons for the finite geometric torsion rank theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate

variable {S S' : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]

/-- An isomorphism of test schemes induces an additive equivalence of actual levels. -/
def levelTestIso {T T' : Over S} (e : T ≅ T') (n : ℕ) :
    Level G T n ≃+ Level G T' n where
  toFun := levelRestrict G e.inv n
  invFun := levelRestrict G e.hom n
  left_inv x := by
    apply toSection_injective G T n
    change e.hom ≫ (e.inv ≫ (Additive.toMul x).val) = (Additive.toMul x).val
    simp
  right_inv x := by
    apply toSection_injective G T' n
    change e.inv ≫ (e.hom ≫ (Additive.toMul x).val) = (Additive.toMul x).val
    simp
  map_add' := (levelRestrict G e.inv n).map_add

/-- The test-scheme comparison preserves the already installed residue actions. -/
def levelTestIsoLinear {T T' : Over S} (e : T ≅ T') (n : ℕ) :
    Level G T n ≃ₗ[ZMod n] Level G T' n where
  __ := levelTestIso G e n
  map_smul' := ZMod.map_smul (levelTestIso G e n).toAddMonoidHom

/-- Pullback adjunction is linear for the actual residue actions at every level. -/
def levelBaseChangeLinear (b : S' ⟶ S) (T : Over S') (n : ℕ) :
    Level ((Over.pullback b).mapGrp.obj G) T n ≃ₗ[ZMod n]
      Level G ((Over.map b).obj T) n where
  __ := levelBaseChange b G T n
  map_smul' := ZMod.map_smul (levelBaseChange b G T n).toAddMonoidHom

/-- Actual torsion of the pulled-back group at its identity test scheme is
residue-linearly equivalent to actual torsion at the original test scheme. -/
def fibreTorsionLinearEquiv (b : S' ⟶ S) (n : ℕ) :
    Level ((Over.pullback b).mapGrp.obj G) (Over.mk (𝟙 S')) n ≃ₗ[ZMod n]
      Level G (Over.mk b) n :=
  (levelBaseChangeLinear G b (Over.mk (𝟙 S')) n).trans
    (levelTestIsoLinear G (Over.isoMk (Iso.refl S') (by simp)) n)

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate

/-- A natural-number unit in global sections remains a unit after arbitrary pullback. -/
theorem isUnit_natCast_pullback {S S' : Scheme.{u}} (b : S' ⟶ S) (n : ℕ)
    (hn : IsUnit (n : Γ(S, ⊤))) : IsUnit (n : Γ(S', ⊤)) := by
  simpa using hn.map b.appTop.hom

/-- A global natural-number unit specializes to a nonzero element of the point field. -/
theorem natCast_ne_zero_at_point {S : Scheme.{u}} (n : ℕ)
    (hn : IsUnit (n : Γ(S, ⊤))) {Ω : Type u} [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ S) : (n : Ω) ≠ 0 := by
  have h := (isUnit_natCast_pullback s n hn).map
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom
  exact (show IsUnit (n : Ω) by simpa using h).ne_zero

/-- The numerical cardinality follows from a linear equivalence, including level one. -/
theorem card_level_of_linearEquiv {S : Scheme.{u}} (A : AbelianScheme S)
    (T : Over S) (n r : ℕ) (hn : 0 < n)
    (e : (Fin r → ZMod n) ≃ₗ[ZMod n] GroupScheme.Tate.Level A.toGrp T n) :
    Nat.card (GroupScheme.Tate.Level A.toGrp T n) = n ^ r := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_fun,
    ZMod.card, Fintype.card_fin]

/-- A field-level additive rank theorem is the remaining geometric input.
This is a reduction hypothesis, not an assertion that the field theorem is proved. -/
def FieldTorsionRankStatement : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (B : AbelianScheme (Spec (CommRingCat.of Ω))) (g : ℕ),
      B.HasRelativeDimension g →
        ∀ (n : ℕ), 0 < n → (n : Ω) ≠ 0 →
          Nonempty ((Fin (2 * g) → ZMod n) ≃+
            GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 _)) n)

/-- All relative specialization and residue-linearity obligations reduce to the
actual field-level torsion theorem. -/
theorem geometricTorsionRank_of_fieldTorsionRank
    (hfield : FieldTorsionRankStatement.{u}) : GeometricTorsionRankStatement.{u} := by
  intro S A g hg n hn hunit Ω _ _ s
  let B := (AbelianScheme.baseChange s).obj A
  have hdim : B.HasRelativeDimension g :=
    AbelianScheme.hasRelativeDimension_baseChange A g hg s
  obtain ⟨e⟩ := hfield Ω B g hdim n hn (natCast_ne_zero_at_point n hunit s)
  let el : (Fin (2 * g) → ZMod n) ≃ₗ[ZMod n]
      GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 _)) n :=
    { e with map_smul' := ZMod.map_smul e.toAddMonoidHom }
  let ef := el.trans (GroupScheme.Tate.fibreTorsionLinearEquiv A.toGrp s n)
  exact ⟨⟨ef⟩, card_level_of_linearEquiv A (Over.mk s) n (2 * g) hn ef⟩

/-- The numerical field-level assertion sufficient for the geometric rank target.
This is an explicit reduction hypothesis, not an unconditional theorem. -/
def FieldTorsionCardinalityStatement : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (B : AbelianScheme (Spec (CommRingCat.of Ω))) (g : ℕ),
      B.HasRelativeDimension g →
        ∀ (n : ℕ), 0 < n → (n : Ω) ≠ 0 →
          Nat.card (GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 _)) n) = n ^ (2 * g)

/-- A field-level numerical cardinality theorem implies the actual torsion structure. -/
theorem fieldTorsionRank_of_fieldTorsionCardinality
    (hcard : FieldTorsionCardinalityStatement.{u}) : FieldTorsionRankStatement.{u} := by
  intro Ω _ _ B g hg n hn hnΩ
  let e := GroupScheme.Tate.levelLinearEquivOfDivisorCard
    B.toGrp (Over.mk (𝟙 _)) n (2 * g) hn (fun d hd hdpos => by
      apply hcard Ω B g hg d hdpos
      obtain ⟨k, hk⟩ := hd
      intro hdΩ
      apply hnΩ
      rw [hk, Nat.cast_mul, hdΩ, zero_mul])
  exact ⟨e.toAddEquiv⟩

/-- The original relative target follows from the numerical cardinality theorem
for actual torsion over algebraically closed fields. -/
theorem geometricTorsionRank_of_fieldTorsionCardinality
    (hcard : FieldTorsionCardinalityStatement.{u}) : GeometricTorsionRankStatement.{u} :=
  geometricTorsionRank_of_fieldTorsionRank
    (fieldTorsionRank_of_fieldTorsionCardinality hcard)

end Langlands.AbelianScheme.Tate

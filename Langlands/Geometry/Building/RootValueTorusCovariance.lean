import Langlands.Geometry.Building.RootValueTorusRestriction
import Langlands.Geometry.Building.RootFunctionNontriviality

/-! # Torus covariance and V0 for actual restricted scalar root functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Evaluating an upper character on a lower torus point raises the lower
character value to its actual integral restriction multiplier. -/
theorem rationalCharacterEval_torusRestriction_eq_pow
    (f : S ⟶ T) (α : characterLattice S) (χ : characterLattice T)
    (m : ℕ) (hχ : f ≫ χ = m • α) (s : rationalPoints S.toGrp) :
    rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm χ)
        (rationalPoints.map (CommGroupScheme.groupHom f) s) =
      rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm α) s ^ m := by
  rw [← rationalCharacterEval_characterRestrict]
  have heq : characterRestrict (CommGroupScheme.groupHom f)
      ((rationalCharacters.equivCharacterLattice T).symm χ) =
      m • (rationalCharacters.equivCharacterLattice S).symm α := hχ
  rw [heq]
  clear hχ heq
  induction m with
  | zero => rw [zero_smul, rationalCharacterEval_zero, pow_zero]
  | succ m ih => rw [succ_nsmul, rationalCharacterEval_add, ih, pow_succ]

/-- Applying an additive unit character gives the corresponding real multiple. -/
theorem unitCharacterValue_torusRestriction_eq_mul
    (ω : kˣ →* Multiplicative ℝ)
    (f : S ⟶ T) (α : characterLattice S) (χ : characterLattice T)
    (m : ℕ) (hχ : f ≫ χ = m • α) (s : rationalPoints S.toGrp) :
    (ω (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm χ)
        (rationalPoints.map (CommGroupScheme.groupHom f) s))).toAdd =
      m * (ω (rationalCharacterEval
        ((rationalCharacters.equivCharacterLattice S).symm α) s)).toAdd := by
  rw [rationalCharacterEval_torusRestriction_eq_pow f α χ m hχ s,
    map_pow, toAdd_pow, nsmul_eq_mul]

variable {i : T.toGrp ⟶ G} {φ : RootFunctionFamily T G}

/-- Inverse conjugation by the actual lower torus point is an automorphism of
the unchanged ambient rational-point group. -/
def torusRestrictionConjugation (f : S ⟶ T) (s : rationalPoints S.toGrp) :
    MulAut (rationalPoints G) :=
  MulAut.conj (rationalPoints.map (CommGroupScheme.groupHom f ≫ i) s)⁻¹

@[simp] theorem torusRestrictionConjugation_apply
    (f : S ⟶ T) (s : rationalPoints S.toGrp) (g : rationalPoints G) :
    torusRestrictionConjugation (i := i) f s g =
      (rationalPoints.map (CommGroupScheme.groupHom f ≫ i) s)⁻¹ * g *
        rationalPoints.map (CommGroupScheme.groupHom f ≫ i) s := by
  simp only [torusRestrictionConjugation, MulAut.conj_apply, inv_inv]

@[simp] theorem torusRestrictionConjugation_inv_apply
    (f : S ⟶ T) (s : rationalPoints S.toGrp) (g : rationalPoints G) :
    torusRestrictionConjugation (i := i) f s⁻¹
      (torusRestrictionConjugation (i := i) f s g) = g := by
  simp [torusRestrictionConjugation_apply, map_inv, mul_assoc]

variable [IsAffineHom G.X.hom] [Mono i.hom.hom.left]

/-- Upper split-torus compatibility carries each canonical lower depth
subgroup into its exactly shifted depth. No geometric product input is used. -/
theorem torusRestrictedRootDepthSubgroup_le_comap_conjugation
    (ω : kˣ →* Multiplicative ℝ) (hφ : IsRootDatumValuation i φ)
    (hcompat : IsSplitTorusCompatible i (fun b => (ω b).toAdd) φ)
    (f : S ⟶ T) (α : characterLattice S) (s : rationalPoints S.toGrp) (r : ℝ) :
    torusRestrictedRootDepthSubgroup hφ f α r ≤
      (torusRestrictedRootDepthSubgroup hφ f α
        (r - (ω (rationalCharacterEval
          ((rationalCharacters.equivCharacterLattice S).symm α) s)).toAdd)).comap
        (torusRestrictionConjugation (i := i) f s).toMonoidHom := by
  let c : ℝ := (ω (rationalCharacterEval
    ((rationalCharacters.equivCharacterLattice S).symm α) s)).toAdd
  change torusRestrictedRootDepthSubgroup hφ f α r ≤
    (torusRestrictedRootDepthSubgroup hφ f α (r - c)).comap _
  refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun m =>
    iSup_le fun hm => iSup_le fun heq => ?_
  intro g hg
  change torusRestrictionConjugation (i := i) f s g ∈
    torusRestrictedRootDepthSubgroup hφ f α (r - c)
  have hle : hφ.filtrationSubgroup χ (m * (r - c)) ≤
      torusRestrictedRootDepthSubgroup hφ f α (r - c) :=
    le_iSup_of_le χ (le_iSup_of_le hχ (le_iSup_of_le m
      (le_iSup_of_le hm (le_iSup_of_le heq le_rfl))))
  apply hle
  have hstable := RelativeRoot.subgroup_isStable i χ (Over.mk (𝟙 _))
    ((rationalPoints.map (CommGroupScheme.groupHom f) s)⁻¹) g hg.1
  have hpoint : rationalPoints.map (CommGroupScheme.groupHom f ≫ i) s =
      rationalPoints.map i (rationalPoints.map (CommGroupScheme.groupHom f) s) := by
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  have hgroup : torusRestrictionConjugation (i := i) f s g ∈ rootGroupPoints i χ := by
    simpa only [rootGroupPoints, torusRestrictionConjugation_apply, hpoint,
      AutomorphicAction.conjugation_act, ← rationalPoints.map_apply, map_inv, inv_inv] using hstable
  refine ⟨hgroup, ?_⟩
  have hvalue : φ χ (torusRestrictionConjugation (i := i) f s g) =
      φ χ g + ((-(m * c) : ℝ) : WithTop ℝ) := by
    rw [torusRestrictionConjugation_apply, hpoint]
    rw [hcompat χ hχ _ g hg.1]
    dsimp only
    rw [unitCharacterValue_torusRestriction_eq_mul ω f α χ m heq s]
  rw [hvalue, show (m : ℝ) * (r - c) = m * r + -(m * c) by ring, WithTop.coe_add]
  exact add_le_add hg.2 le_rfl

private theorem shifted_subgroup_membership_iff
    {A B : Type*} [Group A] [Group B]
    (H : ℝ → Subgroup A) (e : B → MulAut A) (v : B → ℝ)
    (hvinv : ∀ s, v s⁻¹ = -v s)
    (heinv : ∀ s g, e s⁻¹ (e s g) = g)
    (hshift : ∀ s r, H r ≤ (H (r - v s)).comap (e s).toMonoidHom)
    (s : B) (g : A) (r : ℝ) :
    e s g ∈ H r ↔ g ∈ H (r + v s) := by
  constructor
  · intro hg
    have h : e s⁻¹ (e s g) ∈ H (r - v s⁻¹) := hshift s⁻¹ r hg
    simpa only [heinv, hvinv, sub_neg_eq_add] using h
  · intro hg
    have h : e s g ∈ H (r + v s - v s) := hshift s (r + v s) hg
    simpa only [add_sub_cancel_right] using h

/-- Inverse conjugation by a lower torus point shifts the entire canonical
filtration by the value of its lower character. -/
theorem mem_torusRestrictedRootDepthSubgroup_conjugation_iff
    (ω : kˣ →* Multiplicative ℝ) (hφ : IsRootDatumValuation i φ)
    (hcompat : IsSplitTorusCompatible i (fun b => (ω b).toAdd) φ)
    (f : S ⟶ T) (α : characterLattice S) (s : rationalPoints S.toGrp)
    (g : rationalPoints G) (r : ℝ) :
    torusRestrictionConjugation (i := i) f s g ∈
        torusRestrictedRootDepthSubgroup hφ f α r ↔
      g ∈ torusRestrictedRootDepthSubgroup hφ f α
        (r + (ω (rationalCharacterEval
          ((rationalCharacters.equivCharacterLattice S).symm α) s)).toAdd) := by
  exact shifted_subgroup_membership_iff
    (torusRestrictedRootDepthSubgroup hφ f α)
    (torusRestrictionConjugation (i := i) f)
    (fun s => (ω (rationalCharacterEval
      ((rationalCharacters.equivCharacterLattice S).symm α) s)).toAdd)
    (by intro s; simp only [map_inv, toAdd_inv])
    (torusRestrictionConjugation_inv_apply f)
    (torusRestrictedRootDepthSubgroup_le_comap_conjugation ω hφ hcompat f α) s g r

private theorem coe_le_add_neg_iff (v : WithTop ℝ) (c r : ℝ) :
    (r : WithTop ℝ) ≤ v + ((-c : ℝ) : WithTop ℝ) ↔
      ((r + c : ℝ) : WithTop ℝ) ≤ v := by
  induction v using WithTop.recTopCoe with
  | top => simp
  | coe x =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

private theorem value_eq_add_neg_of_shifted_bounds
    (v w : WithTop ℝ) (c : ℝ)
    (h : ∀ r : ℝ, (r : WithTop ℝ) ≤ v ↔ ((r + c : ℝ) : WithTop ℝ) ≤ w) :
    v = w + ((-c : ℝ) : WithTop ℝ) := by
  apply WithTop.eq_of_forall_coe_le_iff
  intro r
  exact (h r).trans (coe_le_add_neg_iff w c r).symm

variable [Smooth G.X.hom]

/-- The actual restricted scalar family inherits split-torus compatibility
from the upper family, on the original ambient rational-point group. -/
theorem torusRestrictedRootFunctionFamily_isSplitTorusCompatible
    (ω : kˣ →* Multiplicative ℝ)
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (hcompat : IsSplitTorusCompatible i (fun b => (ω b).toAdd) φ)
    (f : S ⟶ T) :
    IsSplitTorusCompatible (CommGroupScheme.groupHom f ≫ i)
      (fun b => (ω b).toAdd) (torusRestrictedRootFunctionFamily hS hT hE hφ f) := by
  intro α hα s g hg
  have hstable : torusRestrictionConjugation (i := i) f s g ∈
      rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α := by
    have h := RelativeRoot.subgroup_isStable (CommGroupScheme.groupHom f ≫ i)
      α (Over.mk (𝟙 _)) s⁻¹ g hg
    simpa only [rootGroupPoints, torusRestrictionConjugation_apply,
      AutomorphicAction.conjugation_act, ← rationalPoints.map_apply, map_inv, inv_inv] using h
  have hvalue :
      torusRestrictedRootFunctionFamily hS hT hE hφ f α
          (torusRestrictionConjugation (i := i) f s g) =
        torusRestrictedRootFunctionFamily hS hT hE hφ f α g +
          ((-(ω (rationalCharacterEval
            ((rationalCharacters.equivCharacterLattice S).symm α) s)).toAdd : ℝ) :
            WithTop ℝ) := by
    apply value_eq_add_neg_of_shifted_bounds
    intro r
    exact (le_torusRestrictedRootFunctionFamily_iff
      hS hT hE hφ f α hα _ hstable r).trans
      ((mem_torusRestrictedRootDepthSubgroup_conjugation_iff
        ω hφ hcompat f α s g r).trans
          (le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα g hg _).symm)
  simpa only [torusRestrictionConjugation_apply] using hvalue

/-- A nontrivial additive unit character gives infinitely many values on every
actual lower root group. -/
theorem torusRestrictedRootFunctionFamily_image_infinite
    (ω : kˣ →* Multiplicative ℝ)
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (hcompat : IsSplitTorusCompatible i (fun b => (ω b).toAdd) φ)
    (hω : ∃ b, (ω b).toAdd ≠ 0) (f : S ⟶ T)
    {α : characterLattice S} (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)) :
    (torusRestrictedRootFunctionFamily hS hT hE hφ f α ''
      (rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α :
        Set (rationalPoints G))).Infinite := by
  exact (torusRestrictedRootFunctionFamily_isSplitTorusCompatible
    ω hS hT hE hφ hcompat f).image_infinite ω hS hω
      (torusRestrictedRootFunctionFamily_eq_top_iff hS hT hE hφ f) hα

/-- In particular the actual restricted scalar family satisfies V0 whenever
the additive unit character is nontrivial. -/
theorem torusRestrictedRootFunctionFamily_three_le_encard
    (ω : kˣ →* Multiplicative ℝ)
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (hcompat : IsSplitTorusCompatible i (fun b => (ω b).toAdd) φ)
    (hω : ∃ b, (ω b).toAdd ≠ 0) (f : S ⟶ T)
    {α : characterLattice S} (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)) :
    3 ≤ (torusRestrictedRootFunctionFamily hS hT hE hφ f α ''
      (rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α :
        Set (rationalPoints G))).encard := by
  rw [(torusRestrictedRootFunctionFamily_image_infinite
    ω hS hT hE hφ hcompat hω f hα).encard_eq]
  exact le_top

end Langlands.Geometry.Building

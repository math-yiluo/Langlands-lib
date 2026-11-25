/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence

/-!
# The original-g comparison with a finite derived couple

Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2;
Stacks Project, Tags 011R and 0AMJ.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The explicit recursive lift through the successive image factorizations. -/
private noncomputable def comparisonLift (X : BigradedExactCouple C 0) :
    ∀ (n : ℕ) (p q : ℤ), X.D p q ⟶ (X.pageCouple n).D (p - n) (q + n)
  | 0, p, q => eqToHom (by congr 1 <;> omega)
  | n + 1, p, q => comparisonLift X n p q ≫
      eqToHom (by congr 1 <;> omega) ≫
        factorThruImage ((X.pageCouple n).alpha
          ((p - (n + 1 : ℕ)) + 1) ((q + (n + 1 : ℕ)) - 1))

/-- The recursive inclusions intertwine page alpha with original alpha. -/
private theorem comparisonInclusion_alpha (X : BigradedExactCouple C 0)
    (I : ∀ (n : ℕ) (p q : ℤ), (X.pageCouple n).D p q ⟶ X.D p q)
    (hI0 : ∀ p q : ℤ, I 0 p q = 𝟙 _)
    (hIs : ∀ (n : ℕ) (p q : ℤ), I (n + 1) p q =
      (X.pageCouple n).derivedDInclusion p q ≫ I n p q)
    (n : ℕ) (p q : ℤ) :
    (X.pageCouple n).alpha p q ≫ I n (p - 1) (q + 1) =
      I n p q ≫ X.alpha p q := by
  induction n with
  | zero => simp [hI0, pageCouple]
  | succ n ih =>
    change (Classical.choice (X.pageCouple n).derivedMaps_exists).alpha p q ≫ _ = _
    rw [hIs, hIs, ← Category.assoc,
      (Classical.choice (X.pageCouple n).derivedMaps_exists).alpha_comm,
      Category.assoc, ih, Category.assoc]

/-- Append the final alpha map to the outgoing alpha iterate. -/
private theorem comparisonAlpha_succ (X : BigradedExactCouple C 0)
    (n : ℕ) (p q : ℤ) :
    X.alphaIter (n + 1) p q = X.alphaIter n p q ≫
      X.alpha (p - n) (q + n) ≫ eqToHom (by congr 1 <;> omega) := by
  induction n generalizing p q with
  | zero =>
    simp only [alphaIter]
    apply eq_of_heq
    simp only [← Category.assoc, comp_eqToHom_heq_iff,
      heq_comp_eqToHom_iff, heq_eqToHom_comp_iff]
    congr! 1 <;> omega
  | succ n ih =>
    rw [alphaIter, ih, alphaIter]
    apply eq_of_heq
    simp only [Category.assoc]
    apply heq_comp rfl rfl rfl HEq.rfl
    apply heq_comp rfl rfl rfl
    · rfl
    · simp only [← Category.assoc, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff,
        heq_eqToHom_comp_iff]
      congr! 1 <;> omega

/-- Composing the recursive image lift with its inclusion gives the alpha iterate. -/
private theorem comparisonLift_inclusion (X : BigradedExactCouple C 0)
    (I : ∀ (n : ℕ) (p q : ℤ), (X.pageCouple n).D p q ⟶ X.D p q)
    (hI0 : ∀ p q : ℤ, I 0 p q = 𝟙 _)
    (hIs : ∀ (n : ℕ) (p q : ℤ), I (n + 1) p q =
      (X.pageCouple n).derivedDInclusion p q ≫ I n p q)
    (n : ℕ) (p q : ℤ) :
    comparisonLift X n p q ≫ I n (p - n) (q + n) = X.alphaIter n p q := by
  induction n with
  | zero => simp [comparisonLift, alphaIter, hI0]
  | succ n ih =>
    rw [comparisonLift, hIs]
    simp only [derivedDInclusion, Category.assoc]
    rw [← Category.assoc (factorThruImage _), image.fac]
    rw [comparisonAlpha_succ, ← ih]
    apply eq_of_heq
    simp only [Category.assoc]
    apply heq_comp rfl rfl rfl HEq.rfl
    have h := comparisonInclusion_alpha X I hI0 hIs n (p - n) (q + n)
    apply HEq.trans _ (HEq.trans (heq_of_eq h) _)
    · simp only [eqToHom_comp_heq_iff]
      apply heq_comp (by congr 1 <;> omega) (by congr 1 <;> omega)
        (by congr 1 <;> omega)
      · congr! 1 <;> omega
      · simp only [eqToHom_comp_heq_iff]
        congr! 1 <;> omega
    · simp only [← Category.assoc, heq_comp_eqToHom_iff]
      rfl

/-- The recursive image lift intertwines page g with the canonical cycle projection. -/
private theorem comparisonLift_g (X : BigradedExactCouple C 0)
    (n : ℕ) (p q : ℤ)
    (hg : (X.cycleBoundaryTower.Z n p q).Factors (X.initialG p q)) :
    comparisonLift X n p q ≫ (X.pageCouple n).g (p - n) (q + n) ≫
        eqToHom (by congr 1 <;> omega) =
      (X.cycleBoundaryTower.Z n p q).factorThru (X.initialG p q) hg ≫
        X.cycleBoundaryTower.projection n p q := by
  let T := X.cycleBoundaryTower
  induction n with
  | zero =>
    rw [T.projection_zero, Subobject.factorThru_arrow]
    dsimp only [comparisonLift, pageCouple, initialG]
    apply eq_of_heq
    simp only [← Category.assoc, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff,
      eqToHom_comp_heq_iff]
    congr! 1 <;> omega
  | succ n ih =>
    have hgprev : (T.Z n p q).Factors (X.initialG p q) :=
      Subobject.factors_of_le (X.initialG p q) (T.Z_decreasing n p q) hg
    let a := (T.Z n p q).factorThru (X.initialG p q) hgprev
    let b := (T.Z (n + 1) p q).factorThru (X.initialG p q) hg
    have hb : b ≫ Subobject.ofLE _ _ (T.Z_decreasing n p q) = a := by
      apply (cancel_mono (T.Z n p q).arrow).mp
      simp [a, b, Category.assoc]
    let Y := X.pageCouple n
    let M := Classical.choice Y.derivedMaps_exists
    have hprev := ih hgprev
    have hcycles : comparisonLift X n p q ≫
        eqToHom (by congr 1 <;> omega) ≫
          Y.gToCycles ((p - (n + 1 : ℕ)) + 1) ((q + (n + 1 : ℕ)) - 1) ≫
            eqToHom (congrArg (fun pq : ℤ × ℤ ↦ kernel (Y.d pq.1 pq.2))
              (show (p - (n + 1 : ℕ) + 1 + n, q + (n + 1 : ℕ) - 1 - n) =
                (p, q) by ext <;> omega)) = b ≫ T.cycleLift n p q := by
      apply (cancel_mono (kernel.ι (Y.d p q))).mp
      simp only [Category.assoc]
      rw [T.cycleLift_comm, ← Category.assoc b, hb]
      change _ = a ≫ T.projection n p q
      rw [← hprev]
      rw [← eqToHom_naturality (fun pq : ℤ × ℤ ↦ kernel.ι (Y.d pq.1 pq.2))
        (show (((p - (n + 1 : ℕ)) + 1) + n,
          ((q + (n + 1 : ℕ)) - 1) - n) = (p, q) by ext <;> omega)]
      dsimp only [gToCycles]
      rw [← Category.assoc (kernel.lift _ _ _), kernel.lift_ι]
      apply eq_of_heq
      apply heq_comp rfl rfl rfl HEq.rfl
      simp only [← Category.assoc, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
        heq_comp_eqToHom_iff]
      congr! 1 <;> omega
    rw [T.projection_succ]
    dsimp only [comparisonLift]
    change (comparisonLift X n p q ≫ eqToHom _ ≫
      factorThruImage (Y.alpha ((p - (n + 1 : ℕ)) + 1)
        ((q + (n + 1 : ℕ)) - 1))) ≫ M.g _ _ ≫ _ = _
    simp only [Category.assoc]
    rw [← Category.assoc (factorThruImage _), M.g_comm]
    have hend := eqToHom_naturality
      (fun pq : ℤ × ℤ ↦ Y.derivedEProjection pq.1 pq.2)
      (show (p - (n + 1 : ℕ) + 1 + n, q + (n + 1 : ℕ) - 1 - n) =
        (p, q) by ext <;> omega)
    have hh := congrArg (fun z ↦ z ≫ Y.derivedEProjection p q) hcycles
    simp only [Category.assoc] at hh
    rw [← hend] at hh
    apply eq_of_heq
    apply HEq.trans _ (heq_of_eq hh)
    simp only [← Category.assoc, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
    rfl

/-- The lift of the alpha iterate into the recursively included derived D term,
followed by derived g, is original g followed by the canonical cycle projection.

Proof: First construct canonical image epimorphisms e_n recursively, starting with
identity and endpoint transport. At n+1 compose e_n with the image epimorphism of
incoming alpha on page n, with source (p-n,q+n) and target (p-n-1,q+n+1).
Induction on hIs, using DerivedMaps.alpha_comm, gives I_n compatibility with original
alpha. Therefore e_n followed by I_n is the n-fold outgoing alpha iterate. The
appended-alpha recurrence equals alphaIter's prepended-alpha recurrence by induction
and associativity. Monicity of I_n shows any e satisfying he equals this e_n.
Induct on n to compare g. The base is hI0, projection_zero and factorThru_arrow.
At a successor, Z_decreasing gives the factorization of initialG through Z_n from
its factorization through Z_(n+1). The latter lift followed by ofLE equals the former
lift: compose with the monic arrow of Z_n and use ofLE_arrow and factorThru_arrow.
DerivedMaps.g_comm expresses e_(n+1) followed by g_(n+1) as e_n followed by the
transported gToCycles and derivedEProjection. The induction hypothesis identifies
e_n followed by g_n with the former cycle lift followed by projection n.
The latter cycle lift followed by cycleLift has the same composite with kernel.ι:
use cycleLift_comm and the equality of the two lifts just proved. Cancel this monic
kernel inclusion to identify it with e_n followed by gToCycles. Finish by composing
with derivedEProjection and using projection_succ. Endpoint transports are eqToHom
maps; associativity and eqToHom composition identify the resulting target with (p,q).
Finally cancel I_n to replace the recursive image epimorphism by the supplied e.
No vanishing, positivity or colimit hypothesis is needed. At n=0 this is the initial
projection identity; the zero category satisfies the same equations.
Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2, original-g
projection through successive images; Stacks Tags 011R and 0AMJ. The induction is
an explicit expansion of these sources' induced-g construction.
(blueprint: lem-sp-finite-cycle-derived-comparison) -/
theorem finiteCycle_derived_comparison (X : BigradedExactCouple C 0)
    (I : ∀ (n : ℕ) (p q : ℤ), (X.pageCouple n).D p q ⟶ X.D p q)
    (hI0 : ∀ p q : ℤ, I 0 p q = 𝟙 _)
    (hIs : ∀ (n : ℕ) (p q : ℤ), I (n + 1) p q =
      (X.pageCouple n).derivedDInclusion p q ≫ I n p q)
    (hImono : ∀ (n : ℕ) (p q : ℤ), Mono (I n p q))
    (r : ℕ) (p q : ℤ)
    (hg : (X.cycleBoundaryTower.Z r p q).Factors (X.initialG p q))
    (e : X.D p q ⟶ (X.pageCouple r).D (p - r) (q + r))
    (he : e ≫ I r (p - r) (q + r) = X.alphaIter r p q) :
    e ≫ (X.pageCouple r).g (p - r) (q + r) ≫
        eqToHom (by congr 1 <;> omega) =
      (X.cycleBoundaryTower.Z r p q).factorThru (X.initialG p q) hg ≫
        X.cycleBoundaryTower.projection r p q := by
  have := hImono r (p - r) (q + r)
  have heq : e = comparisonLift X r p q := by
    apply (cancel_mono (I r (p - r) (q + r))).mp
    exact he.trans (comparisonLift_inclusion X I hI0 hIs r p q).symm
  rw [heq]
  exact comparisonLift_g X r p q hg

end CategoryTheory.BigradedExactCouple

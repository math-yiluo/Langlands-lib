/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Sheafification at an object with finite partition refinements

Source: Stacks Project, Pro-étale Topology, Tag 0F63,
`lemma-presheaf-value-weakly-contractible`, abstract finite-partition form;
Sites, Tags 00WB, 00WK and 00WH (blueprint: lem-zl-partition-refinement-sheafification).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- An actual cover inside a generated covering sieve.
Source: Stacks, Sites, Definition 00VH. Induct on the generated topology,
using covering pullbacks and bind composition. The same argument occurs in
`BoundedConstantChainMapLocal.covering_refinement`. -/
private theorem covering_refinement {C : Type u} [Category.{v} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings) {U : C} {S : Sieve U}
    (hS : S ∈ J.toGrothendieck U) : ∃ T ∈ J U, T ≤ S.arrows := by
  classical
  have : J.HasIsos := hJ.1
  induction hS with
  | of X R hR => exact ⟨R, hR, Sieve.le_generate R⟩
  | top X =>
    exact ⟨Presieve.singleton (𝟙 X), J.mem_coverings_of_isIso (𝟙 X), by simp⟩
  | pullback X S hS Y f ih =>
    obtain ⟨R, hR, hle⟩ := ih
    let I := Σ Z : C, {a : Z ⟶ X // R a}
    let V : I → C := fun i ↦ i.1
    let a : ∀ i : I, V i ⟶ X := fun i ↦ i.2.1
    have heq : Presieve.ofArrows V a = R := by
      funext Z b
      apply propext
      constructor
      · rintro ⟨i⟩
        exact i.2.2
      · intro hb
        exact Presieve.ofArrows.mk (Y := V) (f := a) ⟨Z, b, hb⟩
    obtain ⟨P, p, q, hpq, hp⟩ := hJ.2.2 I X V a (heq ▸ hR) Y f
    refine ⟨Presieve.ofArrows P p, hp, ?_⟩
    rintro Z b ⟨i⟩
    change S (p i ≫ f)
    rw [(hpq i).w]
    exact S.downward_closed (hle _ _ i.2.2) (q i)
  | transitive X S T hS hT ihS ihT =>
    obtain ⟨R, hR, hle⟩ := ihS
    have hh : ∀ (Y : C) (f : Y ⟶ X) (_ : R f),
        ∃ Q ∈ J Y, Q ≤ (T.pullback f).arrows := by
      intro Y f hf
      exact ihT (hle _ _ hf)
    choose Q hQ hQT using hh
    refine ⟨R.bind (fun {Y f} hf ↦ Q Y f hf),
      hJ.2.1 X R (fun {Y} f hf ↦ Q Y f hf) hR hQ, ?_⟩
    intro Z f hf
    obtain ⟨Y, g, a, ha, hg, rfl⟩ := hf
    exact hQT Y a ha _ _ hg

end CategoryTheory

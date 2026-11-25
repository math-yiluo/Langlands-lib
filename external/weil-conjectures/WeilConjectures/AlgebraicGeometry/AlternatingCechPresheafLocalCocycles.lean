/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
import WeilConjectures.AlgebraicGeometry.AlternatingCechPresheafPositiveInsertion

/-! # Local ingredients of alternating Čech exactness

Source: Stacks Project, Tags 02FU and 01FM.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Local cocycles of the explicit increasing-tuple presheaf complex are boundaries.
Source: Stacks Project, Tag 02FU (cohomology-lemma-covering-resolution),
with the increasing tuples of Tag 01FM.
(blueprint: lem-pc-s3-alternating-cech-presheaf-local-cocycles).

Proof: For an increasing tuple t of length p+1 omitting i, insert i in its
unique increasing position b and take (-1)^b times that coordinate of z.
For a tuple containing i take zero. Since V is contained in U i, the
intersections with V before and after insertion are equal. Transport the
coordinate through this equality to define y in the explicit finite product.

To compute d y on a tuple t of length p+2 omitting i, let b be the insertion
position in t and s the inserted tuple. For a face deleting position a of t,
the insertion position in that face is b-1 if a<b, and b otherwise. The
corresponding face of s deletes position a if a<b, and a+1 otherwise.
Consequently the coefficient in d y is the negative of the coefficient in
(-1)^b times the cocycle equation on s. The face of s deleting i contributes
z at t with coefficient (-1)^(2*b)=1. The cocycle equation therefore gives
d y at t equal to z at t, including all restrictions to V intersect W_t.

For a tuple t of length p+2 containing i in position b, every face except
its deletion of i still contains i and has y-coordinate zero. On the face
deleting i, insertion returns t, and its two signs multiply to one. This
again gives d y at t equal to z at t. Product projections detect equality,
so d y=z. If there are no middle-degree tuples, the middle term is zero
and y=0 suffices. On an empty test open all sections are zero as well.
-/
theorem alternatingCechSheafPresheaf_local_cocycles
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (p : ℕ) (V : X.Opens) (hV : V ≤ U i)
    (z : (alternatingCechSheafPresheafTerms U G (p + 1)).obj (op V))
    (hz : (alternatingCechSheafPresheafD U G (p + 1)).app (op V) z = 0) :
    ∃ y : (alternatingCechSheafPresheafTerms U G p).obj (op V),
      (alternatingCechSheafPresheafD U G p).app (op V) y = z := by
  obtain ⟨s, t, hs⟩ := alternatingCechSheafPresheaf_positive_insertion U G i p
  let P₀ := alternatingCechSheafPresheafTerms U G p
  let P₁ := alternatingCechSheafPresheafTerms U G (p + 1)
  let a : op V ⟶ op (V ⊓ U i) :=
    (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op
  let b : op (V ⊓ U i) ⟶ op V :=
    (homOfLE (le_inf le_rfl hV : V ≤ V ⊓ U i)).op
  refine ⟨P₀.map b (s.app (op V) z), ?_⟩
  have he := congrArg (fun f ↦ f.app (op V)) hs
  have he' := ConcreteCategory.congr_hom he z
  change P₁.map a z =
    (alternatingCechSheafPresheafD U G p).app (op (V ⊓ U i)) (s.app (op V) z) +
      (show P₁.obj (op (V ⊓ U i)) from
        t.app (op V) ((alternatingCechSheafPresheafD U G (p + 1)).app (op V) z)) at he'
  rw [hz, map_zero, add_zero] at he'
  have hn := ConcreteCategory.congr_hom
    ((alternatingCechSheafPresheafD U G p).naturality b) (s.app (op V) z)
  change (alternatingCechSheafPresheafD U G p).app (op V)
      (P₀.map b (s.app (op V) z)) =
    P₁.map b ((alternatingCechSheafPresheafD U G p).app (op (V ⊓ U i))
      (s.app (op V) z)) at hn
  rw [hn, ← he', ← PresheafOfModules.map_comp_apply]
  have hab : a ≫ b = 𝟙 (op V) := Subsingleton.elim _ _
  rw [hab]
  simp

end AlgebraicGeometry

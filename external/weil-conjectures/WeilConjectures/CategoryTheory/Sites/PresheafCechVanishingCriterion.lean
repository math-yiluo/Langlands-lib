/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.PresheafCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.Sites.PresheafFreeExtLocalKilling
import WeilConjectures.CategoryTheory.Sites.PresheafCechExtEdgeInjective
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# A vanishing criterion using Čech nerves of presheaf maps

Source: Stacks Project, Cohomology on Sites, Tags 03F9 and 079Z.
(blueprint: lem-sc-presheaf-cech-vanishing-criterion)
-/

@[expose] public section

universe u v w'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- A sheaf acyclic for all small-valued presheaf Čech nerves is acyclic over
representable objects. The hypothesis is stronger than vanishing only for coverings;
it permits use of presheaf fibre products even when the site has no pullbacks.
Source: Stacks Project, Cohomology on Sites, Tag 03F9, with Čech complexes
formed in presheaves; Tag 079Z supplies their cohomological descent spectral
sequence, and Hypercoverings, Tag 01GC supplies the augmented free nerve resolution.
(blueprint: lem-sc-presheaf-cech-vanishing-criterion)

Proof: write `Z[P]` for the sheafification of the free abelian presheaf on a
small-valued presheaf of sets `P`. Prove by induction on `q > 0`, simultaneously
for all `P`, that `Ext^q(Z[P], F)` is zero. Represent a class by a finite Yoneda
extension, whose final epimorphism is `G -> Z[P]`. Pull back the underlying
presheaf map of this epimorphism along the generator map `P -> Z[P]` to obtain
`E -> P`. Both presheaves are small-valued; the map is locally surjective because
`G -> Z[P]` is an epimorphism of sheaves. The class pulls back to zero on `Z[E]`,
since the tautological lift `E -> G` extends to `Z[E] -> G` and splits the last
step of the pulled-back Yoneda extension.
Apply the presheaf Čech-to-cohomology spectral sequence of Stacks Tag 079Z to
`E -> P`: its first page has terms `Ext^b(Z[E_a], F)`, where `E_a` is the
`(a+1)`-fold presheaf fibre product over `P`, and it converges to
`Ext^(a+b)(Z[P], F)`. The augmented sheafified free-abelian nerve is exact by
the fibrewise contraction and exact sheafification (Tag 01GC). Filtering its
derived Hom complex gives this first-quadrant spectral sequence; the finite
range relevant to degree `q` can equally be formed using Yoneda Ext, so no
additional chosen injective resolution or enough-injectives instance is part
of the hypothesis. By induction all rows `0 < b < q` vanish. The zero row is
precisely `presheafCechComplex (Arrow.mk (E -> P)) F.obj`, so its positive
cohomology vanishes by `hcech`. Consequently the edge map from
`Ext^q(Z[P], F)` to `Ext^q(Z[E], F)` is injective: the other filtration pieces
in total degree `q` are zero. The class already has zero image under this edge
map, and is therefore zero. This proves the induction, including degree one,
where there are no intermediate rows. Finally take `P = yoneda.obj U`;
Mathlib's definition of `H'` is exactly `Ext^q(Z[P], F)`.
The maps on free-abelian sheaves used here are defined by adjunction, not by
choosing arbitrary objects from existence theorems. -/
theorem isZero_H'_of_presheafCech_vanishing
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v})
    (hcech : ∀ (f : Arrow (Cᵒᵖ ⥤ Type v)) (q : ℕ), 0 < q →
      IsZero ((presheafCechComplex f F.obj).homology q))
    (U : C) (q : ℕ) (hq : 0 < q) : IsZero (H' F q U) := by
  have hfree (n : ℕ) : ∀ (P : Cᵒᵖ ⥤ Type v), 0 < n →
      Subsingleton
        (Abelian.Ext ((presheafToSheaf J AddCommGrpCat).obj (P ⋙ AddCommGrpCat.free)) F n) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hn
      apply subsingleton_of_forall_eq 0
      intro x
      obtain ⟨E, f, hf, hx⟩ := exists_presheaf_ext_local_killing F P n hn x
      have hinj := presheafCech_ext_edge_injective F (Arrow.mk f) hf n hn
        (fun Q b hb hbn ↦ ih b hbn Q hb) (hcech (Arrow.mk f) n hn)
      apply hinj
      change (Abelian.Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
        (Functor.whiskerRight f AddCommGrpCat.free))).comp x (Nat.zero_add n) =
          (Abelian.Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
            (Functor.whiskerRight f AddCommGrpCat.free))).comp 0 (Nat.zero_add n)
      rw [Abelian.Ext.comp_zero]
      exact hx
  have : Subsingleton (H' F q U) := hfree q (yoneda.obj U) hq
  exact AddCommGrpCat.isZero_of_subsingleton (H' F q U)

end CategoryTheory.Sheaf

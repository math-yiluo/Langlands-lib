/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel
import WeilConjectures.CategoryTheory.SignedKoszulTensorAssembly

/-!
# The coproduct property of negative Koszul pure tensors

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, finite free tensor calculation.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u z
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- For a positive number of negative Koszul factors, the specified pure-tensor
inclusions form a coproduct in each degree. This concerns only the underlying
graded object, not its differential.

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul; the first step of
lem-cbc-signed-koszul-tensor-coordinates.
(auxiliary; not a blueprint node).

Proof in words: first expand the graded object of the ordered negative Koszul
complex by induction on its number of factors. The empty tensor is the single
complex O[0], whose only nonzero term has the single empty-subset basis vector.
For the successor, the first double complex is zero except in degrees -1 and 0,
where its displayed basis maps are isomorphisms from O. The coproduct defining
the total tensor therefore reduces to these two degrees. Tensor preserves
coproducts in each variable, so insert the inductive coproduct for the tail.
Pairs consisting of the first degree and a tail subset identify bijectively
with subsets of Fin (r+1), by adjoining zero in degree -1 and shifting all tail
indices by Fin.succ. Cardinality gives exactly the required degree. Under this
bijection the inclusions are the recursive maps ringedNegativeKoszulBasis,
since the recursion uses the inverse left unitor and the total inclusion.
Finally expand K tensor this graded object. For each subset I its Koszul degree
is -|I|, forcing the coefficient degree to be q+|I|. The inverse right unitor
identifies K^(q+|I|) tensor O with K^(q+|I|), and the resulting inclusion is
exactly ringedNegativeKoszulSummand. The iterated coproduct universal properties
therefore give the asserted cofan universal property. Every family after this
reindexing is finite; K can be unbounded. No scalar is inverted and the argument
also applies for r=0, the zero ring, and an empty site. -/
theorem isColimit_ringedNegativeKoszulSummands_succ
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) :
    Nonempty (IsColimit (Cofan.mk
      (((ringedNegativeKoszulTensor O ρ a m).obj K).X q)
      (ringedNegativeKoszulSummand O ρ a m K q))) := by
  classical
  exact isColimit_ringedNegativeKoszulTensor_of_basis O ρ r a m K q (fun n ↦
    isColimit_ringedNegativeKoszulBasis_succ O r
      (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m n)

end CategoryTheory

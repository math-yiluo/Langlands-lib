import Langlands.CategoryTheory.Renard.CompositionChains

/-!
# Renard A.VI.3: the Jordan–Hölder assertion

Source: Renard, *Représentations des groupes réductifs p-adiques*
(French edition dated 9 July 2026), Appendix A.VI.3, printed page 263 /
PDF page 269. This module only defines a proposition; it proves nothing.
It works in an arbitrary abelian category with independent object and Hom
universes and uses the published composition chains and their actual cokernel
factors. No Grothendieck, finite-type or Jordan–Hölder lattice hypothesis is
assumed.
-/

namespace Langlands.Renard

open CategoryTheory

universe u v

/-- Any two composition chains of an object have equal lengths and their
actual successive cokernels are isomorphic after a permutation of factors. -/
def JordanHolderStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ (X : C) (n m : ℕ) (c : CompositionChain X n) (d : CompositionChain X m),
    n = m ∧ ∃ e : Fin n ≃ Fin m, ∀ i : Fin n,
      Nonempty (c.factor i ≅ d.factor (e i))

end Langlands.Renard

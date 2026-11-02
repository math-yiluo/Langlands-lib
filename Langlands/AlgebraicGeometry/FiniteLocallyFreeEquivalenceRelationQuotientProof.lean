import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationQuotientStatement
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation

/-! # Proof of the quotient by a finite locally free equivalence relation with affine classes

Applies the ported FLT theorem
`AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation` with its
`s` and `t` taken to be the `s` and `t` of the statement.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry

/-- Stacks Proposition 66.14.1 (Tag 07S6) when every equivalence class lies in an affine open. -/
theorem finiteLocallyFreeEquivalenceRelationQuotient :
    FiniteLocallyFreeEquivalenceRelationQuotientStatement.{u} := by
  intro U R t s hmono hrefl hsymm htrans ht htf htl hs hsf hsl haff
  have : Mono (prod.lift t s) := hmono
  have : IsFinite t := ht
  have : Flat t := htf
  have : LocallyOfFinitePresentation t := htl
  have : IsFinite s := hs
  have : Flat s := hsf
  have : LocallyOfFinitePresentation s := hsl
  have hj : ∀ {T : Scheme.{u}} (a b : T ⟶ R),
      a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b := by
    intro T a b has hat
    apply (cancel_mono (prod.lift t s)).mp
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst] using hat
    · simpa only [Category.assoc, prod.lift_snd] using has
  have hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ U => ∃ r : T ⟶ R, r ≫ s = x ∧ r ≫ t = y := by
    intro T
    refine ⟨fun x => ?_, ?_, ?_⟩
    · obtain ⟨r, hrt, hrs⟩ := hrefl T x
      exact ⟨r, hrs, hrt⟩
    · intro x y hxy
      obtain ⟨r, hrx, hry⟩ := hxy
      obtain ⟨r', h1, h2⟩ := hsymm T r
      exact ⟨r', h2.trans hry, h1.trans hrx⟩
    · intro x y z hxy hyz
      obtain ⟨r, hrx, hry⟩ := hxy
      obtain ⟨r', hry', hrz⟩ := hyz
      obtain ⟨r'', h1, h2⟩ := htrans T r' r (hry'.trans hry.symm)
      exact ⟨r'', h2.trans hrx, h1.trans hrz⟩
  obtain ⟨M, q, _, hfin, hflat, hlfp, hsurj, hpb, _⟩ :=
    Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation s t hj hequiv haff
  exact ⟨M, q, hpb.flip, hfin, hflat, hlfp, hsurj⟩

end Langlands.AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal

/-! # Local division in the kernel of a principal thickening

## References

* Stacks Project, Tag 01QQ (affine closed subschemes), and Tag 0H3E (the ordinary quotient sheaf in
  the comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- A section killed on a principal thickening is locally a multiple of its defining power. -/
theorem principal_thickening_local_division
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens)
    (k : ℕ) (a : Γ(W.toScheme, ⊤))
    (ha : (FiniteEtale.Adic.openThickeningMap
      (Ideal.Quotient.mk (Ideal.span {g})) W k).appTop a = 0) :
    ∀ x : W.toScheme, ∃ (V : W.toScheme.Opens), x ∈ V ∧
      ∃ b : Γ(W.toScheme, V),
        W.toScheme.presheaf.map (homOfLE le_top).op a =
          (W.toScheme.presheaf.map (homOfLE le_top).op
            (((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g)) ^ (k + 1) * b := by
  let f := Ideal.Quotient.mk (Ideal.span {g})
  let K := RingHom.ker f ^ (k + 1)
  let i := FiniteEtale.Adic.openThickeningMap f W k
  have hdata := quotientBaseChange_closedImmersion_ideal W.ι K
  have : IsClosedImmersion i := hdata.1
  intro x
  obtain ⟨V, hV, hxV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : W.toScheme.Opens) by trivial)
  let U : W.toScheme.affineOpens := ⟨V, hV⟩
  have hker : RingHom.ker (i.app V).hom =
      K.map ((ΓSpecIso (.of R)).inv ≫ W.ι.appLE ⊤ V le_top).hom := by
    rw [← Scheme.Hom.ker_apply i U]
    exact congrArg (fun J ↦ J.ideal U) hdata.2.1 |>.trans (hdata.2.2 U).2.1
  have hmem : W.toScheme.presheaf.map (homOfLE le_top).op a ∈
      RingHom.ker (i.app V).hom := by
    rw [RingHom.mem_ker]
    have hn := congrArg (fun φ ↦ φ a) (i.naturality (homOfLE (le_top : V ≤ ⊤)).op)
    have haz : (i.app ⊤) a = 0 := ha
    simpa only [ConcreteCategory.comp_apply, haz, map_zero] using hn
  have hK : K = Ideal.span {g ^ (k + 1)} := by
    dsimp only [K, f]
    rw [Ideal.mk_ker, Ideal.span_singleton_pow]
  rw [hker, hK, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hmem
  obtain ⟨b, hb⟩ := hmem
  refine ⟨V, hxV, b, ?_⟩
  have hg : ((ΓSpecIso (.of R)).inv ≫ W.ι.appLE ⊤ V le_top) g =
      W.toScheme.presheaf.map (homOfLE le_top).op
        (((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g) := by
    rw [Scheme.Hom.appLE, ← ConcreteCategory.comp_apply]
    congr 2
  simpa only [map_pow, hg] using hb

end AlgebraicGeometry.Scheme

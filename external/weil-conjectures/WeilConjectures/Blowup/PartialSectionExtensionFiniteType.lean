/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.PartialSectionExtension

/-!

# Extending a partial section without a qcqs hypothesis on the target

`AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection` assumes the total space `Y`
of `p : Y ⟶ X` to be quasi-compact and quasi-separated. This follows from `X` being qcqs and
`p` being separated and quasi-compact, so this file restates the theorem without it.

## Main results

- `AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection'`: extension of a partial section
  after a `V`-admissible blow-up, for `p` separated and of finite type over a qcqs base.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Extension of a partial section.**

Let `X` be qcqs, `U ≤ V` quasi-compact opens of `X` with `U` dense, and `p : Y ⟶ X` separated
and of finite type. A section `f` of `p` over `U` whose image is closed in `p⁻¹(V)` extends,
after a `V`-admissible blow-up `π : X' ⟶ X`, to a section `g` of `p` over an open `W` of `X'`
containing `π⁻¹(U)`, and the graph of `g` is closed in `Y ×_X X'`. -/
theorem exists_admissibleBlowup_extend_partialSection' {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X)) (hUdense : Dense (U : Set X))
    {Y : Scheme.{u}} {p : Y ⟶ X} [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (hfc : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    ∃ (B : IsAdmissible X V) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  exact exists_admissibleBlowup_extend_partialSection hUV hU hV hUdense f hf hfc

end AlgebraicGeometry

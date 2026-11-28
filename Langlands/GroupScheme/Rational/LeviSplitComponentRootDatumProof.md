# The weights of a split component inside a relative root datum

`Langlands.GroupScheme.leviSplitComponentRootDatum` proves
[`LeviSplitComponentRootDatumStatement`](LeviSplitComponentRootDatumStatement.md). For a rational
Levi factor `l : M ⟶ P` of a rational parabolic `p : P ⟶ G` of a connected reductive group
over a field, and a split component `a : A ⟶ M`, it produces a maximal split torus
`t : T ⟶ G` of `G` and `g : A ⟶ T` with `g ≫ t = a ≫ l ≫ p`, such that the real cocharacters
of `A` map injectively onto the common kernel of the relative roots of `t` that vanish on
them, and every relative root has an integral coroot whose reflection permutes the relative
roots and preserves the dimensions of their weight spaces.

The module also proves two small lemmas: `torusCentralizer_le_torusCentralizer_comp` (the
centralizer of a torus is contained in the centralizer of every torus mapping to it) and
`eval_cocharacterMapReal_apply` (evaluating a character on the image of a real cocharacter is
evaluating the pulled-back character).

## Proof

`exists_maximalSplitTorus_extension` extends the split subtorus `a` of `M` to a maximal split
torus `s : T ⟶ M` with `f ≫ s = a`; set `t = s ≫ l ≫ p` and `g = Additive.ofMul f`.

*Maximality in `G`.* `leviSplitComponentCentralizer` identifies the centralizer of `A` in `G`
with the subgroup represented by `l ≫ p`. The centralizer of `T` is contained in that of `A`,
so `IsMaximalSplitTorus.comp_of_torusCentralizer_le_range` shows that `t` is a maximal split
torus of `G`.

*Injectivity.* The composite `f ≫ s = a` is a monomorphism, so `f` is one, and
`cocharacterMapReal_injective` applies.

*The image.* `IsSplitComponent.range_cocharacterMapReal_eq_relativeCentralDirections`, with
the root-annihilator centrality theorem `rootAnnihilatorCentrality`, identifies the image with
the common kernel of the relative roots of `s` in `M`. Every relative root of `t` vanishing on
the image of `A` vanishes on this image, which gives one inclusion. Conversely, a relative
root of `s` is a relative root of `t` (`roots_subset_comp`, since `l ≫ p` is a closed
embedding) and restricts to zero on the central torus `A` (`root_restrict_eq_zero_of_isCentral`),
so the common kernel of the roots of `t` vanishing on `A` lies in that of the roots of `s`.

*Coroots.* `relativeRootReflectionExistence` gives, for the maximal split torus `t`, coroots
`D.coroot` with pairing `2` and normalizer representatives whose Weyl action is the integral
reflection `δ ↦ δ - ⟨δ, γ^∨⟩ γ`. The Weyl action maps relative roots to relative roots
(`weylAction_mapsTo_relativeRoots`) and preserves the dimensions of the weight spaces
(`finrank_weightSpace_weylAction`).

## Sources

Borel–Tits, *Groupes réductifs* (1965), `borel-tits-1965-groupes-reductifs`: 4.15 b), printed
pp.90–91 (Levi subgroups as centralizers of split tori); 5.1 and Théorème 5.3, printed
pp.95–96 (relative root systems); Corollaire 5.8, printed p.98.

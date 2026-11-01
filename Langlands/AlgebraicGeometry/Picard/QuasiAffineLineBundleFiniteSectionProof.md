# Proof of finite-point generation on a quasi-affine scheme

`Langlands.AlgebraicGeometry.Picard.quasiAffineLineBundleFiniteSection` proves
the published proposition
`Langlands.AlgebraicGeometry.Picard.QuasiAffineLineBundleFiniteSectionStatement.{u}`
from the module of the same name. The theorem's type is that proposition itself, in
an arbitrary universe `u`, with no further hypotheses. The statement pair and
everything it imports are unchanged.

So for a quasi-affine scheme `X`, a line bundle `L : LineBundle X` and a finite set
`E ⊆ X`, the proof gives a global section `s` of `L.obj` itself with
`E ⊆ trivializationOpen L.obj s`. It does not replace `L` by a tensor power, and it
assumes nothing more about `X` or `E`. The empty set and the empty scheme are
covered: for empty `E` the section is `0`.

All helper declarations are in namespace
`Langlands.AlgebraicGeometry.Picard.QuasiAffineFiniteSection`. Like the Library
module `Modules.LineBundleSectionClearingProof`, this module sets
`backward.isDefEq.respectTransparency false`.

## Dependencies

The module imports only the statement module and two published Library modules:

- `Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingProof`. From it the
  proof uses only the chart coordinates `chartE` and `chartF` of a module isomorphic
  to the structure module on an open `T`, together with their lemmas
  `chartE_chartF`, `chartF_chartE`, `chartE_res` and `chartE_smul`, plus the
  restriction helpers `modules_map_map`, `presheaf_map_map` and `presheaf_map_id`.
  It does not use the clearing theorem itself.
- `Langlands.AlgebraicGeometry.Modules.SectionCoefficients`: the lemmas
  `le_trivializationOpen_of_bijective`, `exists_smul_sectionRes_eq` and
  `basicOpen_coeff_eq`, and `LineBundleDescent.sectionHom_app`.

From Mathlib it uses `exists_eq_pow_mul_of_isAffineOpen`,
`exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact`, the sheaf gluing
lemmas `existsUnique_gluing'` and `eq_of_locally_eq'`,
`Scheme.IsQuasiAffine.isBasis_basicOpen` (on a quasi-affine scheme the basic opens of
global functions form a basis), `Scheme.mem_basicOpen` and
`Finset.exists_minimalFor`.

It uses none of the results the task excludes: the ideal-embedding statement, the
line-bundle extension statements, the valuative statements, or anything depending
on them.

## Relation to the source

The proof follows the inductive structure of Stacks Project Lemma 28.30.7 (tag
[0F20](https://stacks.math.columbia.edu/tag/0F20)) with `W = X`, but some steps differ.
This uses the retained copy `0F20.html` of the registered source
`stacks-section-open-prerequisites-2026-10-29`.

- **One point.** The source gets a section nonvanishing at a point from global
  generation of quasi-coherent modules on quasi-affine schemes (its Lemma 28.28.1 and
  Proposition 28.27.13). Here Parts 2 and 3 prove this directly for `L`: a local
  generator on a basic open, multiplied by a power of the function, extends to a
  global section.
- **Induction.** The source first removes points that specialize to other points.
  It then uses a section that is nonvanishing at the last point and vanishes on the
  closure of the others. Here (Part 5) the point `x` is chosen with a minimal
  vanishing set of global functions. The section that generates at `x` is multiplied
  by a global function that is nonzero at `x` and zero at the other points.

## Part 1: chart lemmas

Let `Ψ : M.restrict T.ι ≅ structureSheaf T` be an isomorphism. For `W ≤ T`, the
maps `chartE Ψ W` and `chartF Ψ W` are mutually inverse bijections between `Γ(M, W)`
and `Γ(X, W)`. Section `Chart` derives some easy consequences:

- `chartE_zero` and `chartE_injective`;
- `chartF_eq_smul`: `chartF z = z • chartF 1`;
- `chartF_res`: `chartF` commutes with restriction;
- `chartF_bijective`.

## Part 2: extending a section from a basic open

`exists_global_smul_pow`: let `X` be quasi-compact and quasi-separated, `M` a module
sheaf in which every point has a neighbourhood `T` with `M.restrict T.ι` isomorphic
to the structure module, `f : Γ(X, ⊤)`, and `t : Γ(M, D(f))`. Then there are `n` and
a global section `a` with `a|_{D(f)} = (f|_{D(f)})^n • t`. Here `fres f W` is the
restriction of `f` to `W`.

This is the standard argument (compare Stacks tag 01PW). The proof:

1. Choose, for each point, an affine open `V ≤ T` around it. By compactness,
   finitely many of these, indexed by a finset `s`, cover `X`.
2. `exists_local`: on an affine `V ≤ T`, take the coordinate `z` of `t|_{V ⊓ D(f)}`.
   Since `D(f|_V) = V ⊓ D(f)` (`Scheme.basicOpen_res`), Mathlib's
   `exists_eq_pow_mul_of_isAffineOpen` writes `f^n z` as the restriction of a function
   `y` on `V`. Then `b = chartF y` satisfies
   `b|_{V ⊓ D(f)} = f^n • t|_{V ⊓ D(f)}`. By `good_smul`, any larger exponent also
   works, so `Filter.eventually_all` gives one common exponent `e` with local
   solutions `b i` for all `i`.
3. `exists_pow_smul_eq_zero`: a section `d` over a quasi-compact `W ≤ T` that vanishes
   on `W ⊓ D(f)` satisfies `f^k • d = 0` for some `k`. Its coordinate vanishes on
   `D(f|_W)`, and Mathlib's
   `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact` applies. Apply this
   to the differences `b i|_{V_i ⊓ V_j} - b j|_{V_i ⊓ V_j}`. They vanish on
   `V_i ⊓ V_j ⊓ D(f)`, and each `V_i ⊓ V_j` is quasi-compact because `X` is
   quasi-separated. This gives one common exponent `k` that kills every difference.
4. The sections `f^k • b i` are then compatible, so they glue to a global section
   `a` (`existsUnique_gluing'`). The identity `a|_{D(f)} = f^{e+k} • t` is checked on
   the cover `V_i ⊓ D(f)` of `D(f)` (`eq_of_locally_eq'`).

## Part 3: one point

`exists_mem_trivializationOpen`: on a quasi-affine `X`, every point `x` lies in the
generation open of some global section of `L`. Take a trivialization
`Ψ : L.obj.restrict T.ι ≅ structureSheaf T` with `x ∈ T`. Since basic opens form a
basis, there is `f` with `x ∈ D(f) ≤ T`. Quasi-affine schemes are quasi-compact and
separated, hence quasi-separated, so Part 2 applies to `t = chartF Ψ (D(f)) 1`. It
gives `a` with `a|_{D(f)} = f^n • chartF 1`.

For every `V ≤ D(f)` we have `a|_V = u • chartF 1`, where `u = (f|_V)^n` is a unit
(`isUnit_res_basicOpen`). Hence `(sectionHom L.obj a).app V` is the map
`c ↦ chartF (c * u)`, which is bijective. Then
`le_trivializationOpen_of_bijective` gives `D(f) ≤ trivializationOpen L.obj a`.

## Part 4: two sum rules

Let `s, s'` be global sections of `L` and `g : Γ(X, ⊤)`.

- `mem_trivializationOpen_add_smul_of_mem`: if `x` is in the generation open `U` of
  `s` and `g` vanishes at `x` (`x ∉ D(g)`), then `x` is in the generation open of
  `s + g • s'`. Write `s'|_U = c • s|_U` (`exists_smul_sectionRes_eq`). Then
  `(s + g • s')|_U = (1 + g c) • s|_U`, so by `basicOpen_coeff_eq` the generation open
  of `s + g • s'` meets `U` in `D(1 + g c)`. The germ of `g c` at `x` is not a unit,
  because the germ of `g` is not. In the local ring `O_{X,x}`, a unit plus a nonunit
  is a unit (`isUnit_add_of_not_isUnit`), so `x ∈ D(1 + g c)`.
- `mem_trivializationOpen_add_smul_of_not_mem`: if `x` is not in the generation open
  of `s`, `g` is nonzero at `x`, and `x` is in the generation open `U` of `s'`, then
  `x` is in the generation open of `s + g • s'`. Write `s|_U = c • s'|_U`. Then
  `basicOpen_coeff_eq` shows `x ∉ D(c)`, since otherwise `x` would lie in the
  generation open of `s`. And `(s + g • s')|_U = (c + g) • s'|_U`. The germ of `g` at
  `x` is a unit and the germ of `c` is not, so `x ∈ D(c + g)`, which is the
  generation open of `s + g • s'` inside `U`.

## Part 5: finite sets

`vanishingSet x` is the set of global functions `g` with `x ∉ D(g)`.

`exists_separating`: on a quasi-affine `X`, let `y ≠ x` and assume that
`vanishingSet y ⊆ vanishingSet x` implies `vanishingSet x ⊆ vanishingSet y`. Then some
global `g` has `x ∈ D(g)` and `y ∉ D(g)`. Otherwise both inclusions hold, so `x` and
`y` lie in exactly the same basic opens. Since basic opens form a basis, `x` and `y`
are then inseparable. Schemes are `T0`, so `x = y`, a contradiction.

`exists_forall_mem_trivializationOpen` proves the result for a `Finset E` by strong
induction on `E`.

- If `E` is empty, take `0`.
- Otherwise `Finset.exists_minimalFor` gives `x ∈ E` whose vanishing set is minimal
  among those of points of `E`. Then every `y ∈ E` with `y ≠ x` satisfies the
  hypothesis of `exists_separating`. The induction hypothesis gives a section `s`
  generating at every point of `E \ {x}`. If `s` also generates at `x`, we are done.
- Otherwise Part 3 gives `s'` generating at `x`, and `exists_separating` gives
  functions `g y` with `x ∈ D(g y)` and `y ∉ D(g y)` for each `y ∈ E \ {x}`. Let
  `G = ∏ g y`. Then `x ∈ D(G)` (`Scheme.basicOpen_mul`), and `G` vanishes at every
  such `y`. The section `s + G • s'` generates at `x` by the second sum rule and at
  every `y ≠ x` by the first.

Finally, `quasiAffineLineBundleFiniteSection` introduces `X`, `L` and a finite set
`E`, applies `exists_forall_mem_trivializationOpen` to `hE.toFinset`, and converts
membership back with `Set.Finite.mem_toFinset`.

# Forward propagation of component flatness

`Langlands.Algebra.LocalApproximationFlatnessPropagationStatement` is a
Prop-valued definition of a supporting proposition for the published
`LocalApproximationSystem` interface. It states forward propagation along one
transition. This module does not provide a Lean proof.

For every nonempty directed preorder `ι`, commutative local rings `R,S` with
their local algebra map, additive commutative group `M` with its `S`-module
structure, and systems

```lean
D : LocalAlgebraSystem.{uI,uA,uB,uR,uS} ι R S
E : LocalModuleSystem.{uI,uA,uB,uN,uR,uS,uM} D M
```

the proposition quantifies over `i j : ι` and `h : i ≤ j`. Its transition
hypotheses are exactly

```lean
D.IsPrimeLocalization h
Function.Bijective (E.moduleBaseChangeMap h)
```

Under these hypotheses it asserts

```lean
Module.Flat (D.base i) (E.obj i) →
Module.Flat (D.base j) (E.obj j)
```

Both base-module structures are explicitly bound in the proposition by

```lean
Module.compHom (E.obj k) (algebraMap (D.base k) (D.alg k))
```

for `k = i,j`. Here the `D.alg k` action is `E.objModule k`, and the
algebra map comes from `D.componentAlgebra k`. Thus these are the restrictions
of the actual component actions. There are no independent base-module actions
or scalar-tower hypotheses.

The seven universe parameters `uI,uA,uB,uN,uR,uS,uM` remain independent:
they respectively govern the index, component base rings, component algebra
rings, component modules, and the three ambient targets. The proposition adds
no colimit, essential-finite-type, finite-generation, Noetherian, ambient-target
flatness, injective-transition, or flat-transition assumption. It does not
require `E.IsApproximation`.

## Canonical transitions and the intended argument

Write `Rᵢ = D.base i`, `Sᵢ = D.alg i`, and `Mᵢ = E.obj i`. The ring
transition is the actual map

\[
A=S_i\otimes_{R_i}R_j\longrightarrow S_j,\qquad
s\otimes r\longmapsto
D.\mathrm{algMap}_{ij}(s)\,f_j(r),
\]

where `fⱼ` is the component algebra map. The definition
`D.IsPrimeLocalization h` installs the algebra structure induced by this exact
`D.ringBaseChangeMap h` and asserts that it presents `Sⱼ` as localization at
some prime of `A`. It does not assert bijectivity of the ring map.

The module hypothesis concerns the actual `Sⱼ`-linear comparison

\[
S_j\otimes_{S_i}M_i\longrightarrow M_j,\qquad
s\otimes m\longmapsto s\cdot E.\mathrm{map}_{ij}(m).
\]

Its bijectivity identifies the source with `Mⱼ` as an `Sⱼ`-module and,
by restriction, with the specified `Rⱼ`-action.

The mathematical justification is the following derived argument. Base change
of an `Rᵢ`-flat `Mᵢ` gives the `Rⱼ`-flat module
`P = Rⱼ ⊗[Rᵢ] Mᵢ`. Its compatible `A`-action is
`(s ⊗ r) • (r' ⊗ m) = (r * r') ⊗ (s • m)`.
The canonical map `A → Sⱼ` respects the `Rⱼ`-algebra structures. Localizing
the `A`-module `P` at the prime supplied by the first hypothesis preserves
flatness over the unchanged base ring `Rⱼ`: module localization is a filtered
colimit of copies of `P` along multiplication maps, these maps are
`Rⱼ`-linear, and filtered colimits of flat `Rⱼ`-modules are flat. Tensor
associativity and scalar compatibility identify this localized module with
`Sⱼ ⊗[Sᵢ] Mᵢ`. The second hypothesis then transports flatness to `Mⱼ`
with the explicitly specified base action.

This localization over the auxiliary algebra `A` is a necessary step of a
future Lean proof. Base change alone does not establish the conclusion.
`Module.Flat.of_isLocalizedModule` concerns localization of the flatness base
ring; it does not directly discharge localization over `A` with `Rⱼ`
unchanged. A future implementation must establish that preservation and the
canonical scalar-compatible identifications. No such Lean proof or unchecked
application of a tensor-product flatness instance is claimed here.

## Approximation systems and source provenance

The registered original is
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
in the retained folder
`literature/Stacks Project - Algebra flatness criteria and essentially finite presentation (HTML snapshot 2026-10-22)/`.
The relevant passages are:

- `00QL.html`, Lemma 10.127.13
  ([00QX](https://stacks.math.columbia.edu/tag/00QX)), especially clauses (5)
  and (6), giving the prime-localization and module base-change conditions;
- `00QV.html`, Lemma 10.127.11
  ([00QV](https://stacks.math.columbia.edu/tag/00QV)), clause (4) and the
  local polynomial-quotient construction;
- `00R3.html`, Lemma 10.128.3
  ([00R6](https://stacks.math.columbia.edu/tag/00R6)), which concludes
  existence of one flat component;
- `00R7.html`, Lemma 10.128.8
  ([00R7](https://stacks.math.columbia.edu/tag/00R7)), whose proof uses
  flatness at all sufficiently late components after two applications of 00R6.

This proposition is an internal consequence of the canonical transition
properties, justified by the argument above; it is not a displayed lemma
quoted from those sources. In particular, it is distinct from the existential
descent statement 00R6.

In the published interface, `E.IsApproximation` supplies both transition
hypotheses for every `i ≤ j` through its fifth and sixth clauses. Consequently,
once this proposition is proved, flatness of a single component implies
flatness at every later component. Applying this to the two approximation
systems used for 00R7 permits passage to a common directed bound after the
two existential descent steps. It imposes no extra hypothesis on 00R6.
The final plain-tensor identities printed in the source proof of 00R7 omit
localization; this statement does not use them as unconditional identities.

The module imports the published `LocalApproximationSystem` by Lean name and
leaves its Lean/Markdown pair and imports intact. The statement applies to
any systems of that interface, including derived fibre systems when their
transition hypotheses have been established. Construction of those systems,
generic colimit ascent, and the exact proof successor are separate work.

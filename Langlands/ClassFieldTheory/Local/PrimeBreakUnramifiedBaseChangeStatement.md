# The prime ramification break under unramified base change

Authors: Worker 27 (Lean statement and first Markdown draft) and Worker 231
(source and interface audit, Markdown revision). This module defines a
proposition; it does not prove the ramification comparison.

## Exact statement

`Langlands.LocalClassField.PrimeBreakUnramifiedBaseChange.{u}` quantifies a
prime `p`, `[Fact p.Prime]`, any `F : PadicField.{u} p`, and finite
intermediate extensions `E` and `K'` of `F.Carrier` in
`AlgebraicClosure F.Carrier` (`FiniteIntermediateExtension F.Carrier`). It
assumes `[IsGalois F.Carrier E.field]`, that the relative degree
`ell := Module.finrank F.Carrier E.field` is prime, and

```
e(E) = ell * e(F),     e(K') = e(F).
```

Each `e` is the `ramificationIndex` of the canonical topological data
(`canonicalTopologicalData`) of `F` or of the indicated `asPadicField`
package, that is, an absolute ramification index over `Padic p`. These
equalities express that `E/F` is totally ramified and that `K'/F` is
unramified. No other hypothesis is placed on `K'`: its degree is arbitrary
and degree one is allowed. No Galois hypothesis is placed on `K'/F`. A finite
unramified extension of a p-adic field is in fact Galois, but the statement
neither assumes nor uses this.

The proposition then quantifies every finite intermediate extension `M` with
`M.field = E.field ⊔ K'.field`, every pair of inclusion proofs
`hE : E.field ≤ M.field` and `hK : K'.field ≤ M.field`, and every natural
number `t`, including `t = 0`. Its premise is

```
G_i(E/F) = if i ≤ t then ⊤ else ⊥     for every natural i,
```

and its conclusion is the identical formula, with the same `t`, for every
natural `i`:

```
G_i(M/K') = if i ≤ t then ⊤ else ⊥.
```

Here `G_i` is the existing
`Langlands.Ramification.Padic.lowerRamificationGroup`, applied to
`(E.asPadicField (p := p)).canonicalTopologicalData` over `F.Carrier`, and
to `(M.asPadicField (p := p)).canonicalTopologicalData` over `K'.field`.
Its ambient group is the full algebra automorphism group of the upper field
over the displayed base: `E.field ≃ₐ[F.Carrier] E.field` and
`M.field ≃ₐ[K'.field] M.field`. An automorphism `σ` lies in `G_i` exactly
when `σ x - x` lies in the `(i+1)`st power of the maximal ideal for every
`x` in the actual integer ring of the canonical data
(`mem_lowerRamificationGroup`). So `⊤` and `⊥` are the whole automorphism
group and the trivial subgroup, and the premise is a hypothesis about the
actual filtration of `E/F`, not a supplied filtration or group isomorphism.

There is no assertion here that such a `t` exists. For the present `E/F`,
existence is the separate published statement
`Langlands.LocalClassField.PrimeTotallyRamifiedBreak`, which is not yet
proved in the Library. The conclusion only
needs the top/bottom pattern, so the statement does not name a restriction
isomorphism between the two automorphism groups.

## Scalar maps and local structures

The statement installs, by `letI`, the `Padic p`-algebras of the three
`asPadicField` packages before it forms any scalar tower. On `E.field` this
is the composite `Padic p → F.Carrier → E.field`, and similarly on
`K'.field` and `M.field`. The algebras `E.field → M.field` and
`K'.field → M.field` are `(IntermediateField.inclusion hE).toAlgebra` and
`(IntermediateField.inclusion hK).toAlgebra`, the actual inclusions into the
compositum. These installations are the same as in
`Langlands.LocalClassField.TotalUnramifiedCompositum`.

The scalar towers `Padic p → F.Carrier → E.field`,
`Padic p → E.field → M.field` and `Padic p → K'.field → M.field` are
supplied by `IsScalarTower.of_algebraMap_eq' rfl`, so they hold by
definitional equality of the installed maps. The first and third are the
towers that the two lower groups require; the second is the compatible
tower for `E.field → M.field` requested by the task and is not used by
either lower group. The lower groups therefore use the same `Padic p`
structures as the canonical topological data of `E` and `M`.

The lower-group definition does not require an `IsGalois` instance.
Accordingly, the statement does not assume separately that `M/K'` is Galois.
That property is an arithmetic consequence of the hypotheses. The separate
statement `TotalUnramifiedCompositum` includes it among its conclusions, so
a proof of that statement would supply it to a proof of this one.

## Original source and derived provenance

Source: Jean-Pierre Serre, *Local Fields*, English translation by Marvin
Jay Greenberg, Graduate Texts in Mathematics 67, Springer (1979),
registered as `serre-1979-local-fields`. The source file is
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The relevant text is Chapter V, §4 ("Extension of the Residue Field in a
Totally Ramified Extension"), printed pages 87–88 (PDF pages 94–95). It is
the setup paragraph before Proposition 6. Worker 27 read these pages on
2026-10-23 and Worker 231 reread them on 2026-10-24.

Errata: Jean-Pierre Serre, *Corrections to J-P. Serre's books* (Collège de
France author file, 2019), registered as `serre-book-corrections-2019`. The
file is `/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to
J-P. Serre's books (2019).pdf`, SHA256
`b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`. Its
section for *Local Fields* (Springer-Verlag, third printing, 1979) is on PDF
pages 2–3. Workers 27 and 231 checked it on 2026-10-24. It lists corrections
for printed pages 14, 15, 31, 63, 74 and 75, and then from page 110 onward,
so it has none for printed pages 87–88.

Serre's `K`, `L`, `K'`, `L'` correspond to `F`, `E`, `K'`, `M`. Serre
takes `L/K` finite and totally ramified with perfect residue field, and `K'`
the unramified extension of `K` corresponding to a finite extension of the
residue field. Here the residue fields are finite, hence perfect. He shows
that `L` and `K'` are linearly disjoint, identifies the compositum `L'` with
`K' ⊗_K L`, and states that a uniformizer of `L` is also a uniformizer of
`L'`. Assuming `L/K` Galois with group `G`, he states that `L'/K'` is Galois
and that "the ramification groups of `G`" are the same for `L/K` and
`L'/K'`. Serre leaves the identification of the two groups implicit. It is
restriction from the automorphism group of `L'/K'` to that of `L/K`, an
isomorphism by linear disjointness.

The Lean proposition is a derived specialization of that comparison. Serre's
setup allows any finite totally ramified Galois `L/K`. Here the degree is
prime and the actual filtration of `E/F` has the displayed single-break
pattern. If restriction is an isomorphism `r` with `G_i(M/K')` equal to the
preimage of `G_i(E/F)` under `r` for every `i`, then `G_i(E/F) = ⊤` gives
`G_i(M/K') = ⊤`, and `G_i(E/F) = ⊥` gives `G_i(M/K') = ⊥`. This yields the
displayed conclusion. Three features are formal interface choices, not
claims quoted from Serre: the canonical p-adic packages, the absolute
ramification-index form of the hypotheses, and the universal quantification
over every `M` and every inclusion proof presenting the actual compositum.

A proof must establish the genuine restriction and filtration comparison.
One route is the uniformizer test for lower groups of a totally ramified
extension together with the retained uniformizer of `E` in `M`. The supplied
break pattern alone does not establish these facts. This statement does not
construct a compositum, compare degrees, residues, norms or traces, prove a
norm-polynomial identity, or assert norm surjectivity.

## Validation status

Worker 27's development check `e73a3145-81f7-4696-99bd-a4aea0c263f0` and
Worker 231's development check `ef0c3260-eac2-426c-8403-52654a7831f6`
compiled this module with zero errors or warnings. Both checks inspected the
declaration as `Prop`-valued with universe parameter `u`, depending only on
`propext`, `Classical.choice` and `Quot.sound`. These checks neither prove the
arithmetic nor constitute independent semantic acceptance.

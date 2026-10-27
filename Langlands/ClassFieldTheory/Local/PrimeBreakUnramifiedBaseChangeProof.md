# Preservation of the prime ramification break under unramified base change

Author: Worker 32.

The theorem
`Langlands.LocalClassField.primeBreakUnramifiedBaseChange` proves the exact
published proposition
`Langlands.LocalClassField.PrimeBreakUnramifiedBaseChange.{u}` from
`Langlands.ClassFieldTheory.Local.PrimeBreakUnramifiedBaseChangeStatement`.
There are no additional outer hypotheses or instances.

For a prime `p` and `F : PadicField.{u} p`, let `E` and `K'` be finite
intermediate extensions in an algebraic closure of `F.Carrier`. The target
assumes that `E/F` is Galois, that its degree `ell` is prime, and that the
canonical absolute ramification indices satisfy
`e(E) = ell * e(F)` and `e(K') = e(F)`. For every presentation `M` of
`E.field ⊔ K'.field`, every pair of inclusion proofs, and every supplied
natural number `t`, it transfers the actual lower-group pattern

```text
G_i(E/F) = if i ≤ t then ⊤ else ⊥
```

to `G_i(M/K')` for every natural `i`, with the same `t`. The theorem proves
this conditional preservation statement; it does not construct a break.
The prime-degree hypothesis is retained in the theorem's exact type, although
the implemented comparison uses total ramification and the supplied pattern.

## Implemented proof

The proof first installs exactly the algebras of the target's three
`asPadicField` packages, the inclusion-induced algebras `E.field → M.field`
and `K'.field → M.field`, and the target's three scalar towers. The tower
equalities hold by definitional equality. It abbreviates the canonical
topological data of `E`, `K'`, and `M` by `TE`, `TK`, and `TM`.

The published support theorem `primeBreakCompositumData` applies the proved
`totalUnramifiedCompositum` to total ramification of `E/F` and
unramifiedness of `K'/F`. It supplies both:

- Surjectivity of the actual relative residue map for `M/K'`.
- The identity `TM.ord (inclusion hE z) = TE.ord z` for every `z : E.field`.

That support theorem already transports the existential compositum witness
to the quantified `M`, by equality of finite-intermediate-extension
packages. Thus these conclusions apply to every presentation and every
inclusion proof in the target. The proof also uses
`primeBreakResidueMap_surjective_of_total` to obtain surjectivity of the
actual relative residue map for `E/F`.

Take `π = TE.uniformizer`. The published `TE.ord_uniformizer` gives
`TE.ord π = 1`, and order preservation gives
`TM.ord (inclusion hE π) = 1`. The independently proved
`Ramification.Padic.mem_lowerRamificationGroup_iff_uniformizer` applies
to both extensions with these uniformizers and the two residue-map
surjectivity results. It characterizes membership by the actual field
displacement being zero or having normalized order at least `(i : ℤ) + 1`.

For `σ : M.field ≃ₐ[K'.field] M.field`, the actual restriction
`primeBreakRestriction E.field K'.field M.field hE hK σ` is an
`F.Carrier`-automorphism of `E.field`. Its commutation with the inclusion
identifies the displacement in `M` with the image of the displacement in
`E`. The support identity `primeBreakRestriction_displacement` combines
this fact, order preservation, and injectivity of the inclusion. Hence the
local fact `hmem` proves, for every `σ` and the current natural `i`,

```text
σ ∈ G_i(M/K') ↔ restriction(σ) ∈ G_i(E/F).
```

If `i ≤ t`, the supplied pattern for `E/F` makes every restricted element
belong to `G_i(E/F)`. The equivalence therefore puts every `σ` in
`G_i(M/K')`, proving that this group is top. If `i > t`, membership forces
the restriction to be the identity. The published
`primeBreakRestriction_injective`, using `M.field = E.field ⊔ K'.field`,
then forces `σ` itself to be the identity, proving that the lower group is
bottom. This is enough to transfer the pattern; the argument requires only
injectivity of restriction.

All natural indices, including `i = 0`, and all supplied `t`, including
`t = 0`, follow from the same equivalence and case split. No Galois
assumption on `K'/F` is introduced, and no lower bound is imposed on its
degree. The displacement-zero alternative remains explicit throughout,
as required by the convention `ord 0 = 0`. The lower groups are the
published groups defined by congruences for every element of the actual
integer ring.

## Dependencies and provenance

All dependencies are imported by their published Lean names. This module
imports the unchanged target statement, the support module, and
`Langlands.LocalFactor.Ramification.UniformizerCriterionProof`. The support
module imports the proved
`Langlands.ClassFieldTheory.Local.TotalUnramifiedCompositumProof`.
Neither the target pair nor its import closure is edited.

Worker 32 wrote the support and this final proof. Workers 27 and 231
authored the target statement and its source audit. Worker 231 proved the
uniformizer criterion, whose statement was authored by Worker 507 with
Worker 32's formulation and derivation. The criterion uses Worker 40's
actual integer-ring ramification groups, Worker 90's relative integer and
residue maps, Worker 96's uniformizer coordinates, and Worker 27's
normalization results reused by Worker 12. These are imported results,
not copied drafts or code in this module. Worker 159 authored the
finite-compositum proof, with Worker 27 credited there for the suggested
arithmetic route. That arithmetic is consumed through its published theorem
and the previously published support projections.

The original mathematical background is Jean-Pierre Serre, *Local Fields*,
English translation by Marvin Jay Greenberg, GTM 67, Springer (1979),
registered as `serre-1979-local-fields`, at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Chapter V, §4, the setup before Proposition 6, printed pp.87–88
(PDF pp.94–95), preserves a uniformizer under finite unramified base change
and identifies the ramification groups in the Galois case. Chapter IV, §1,
Lemma 1 and Proposition 1, printed pp.61–62 (PDF pp.68–69), provides the
all-integer lower-group congruence; Chapter IV, §2, Proposition 5,
printed p.66 (PDF p.73), provides the inertia-element uniformizer test.
Worker 32 read these passages during the prerequisite development.

The registered author errata `serre-book-corrections-2019` is
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA256
`b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`.
Its *Local Fields* entries on PDF pp.2–3 give no correction to the cited
passages.

This implementation derives the single-break comparison from the published
compositum arithmetic and the proved uniformizer criterion. The criterion's
proof propagates congruences from a uniformizer using fixed residue
representatives and induction on ideal powers. The final top/bottom
argument is a specialization of the filtration comparison, and does not
use a norm calculation, reciprocity, or existence of the supplied break.

Development compilation and declaration inspection succeeded in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with no errors or warnings.
The theorem has universe parameter `u` and uses only `propext`,
`Classical.choice`, and `Quot.sound`. Independent semantic review and the
submission's Lake and exact-target checks are required for acceptance.

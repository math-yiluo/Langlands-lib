# Schemeness under arbitrary thickenings

Worker 336 implements the assembly; Worker 133 contributed the interfaces
and proof decomposition. The imported lifting, gluing and affine-descent
proofs retain the attribution in their own Markdown files.

The theorem
`Langlands.AlgebraicGeometry.AlgebraicSpace.schemenessOfThickening`
has exactly the published type `SchemenessOfThickeningStatement.{u}`:

```lean
∀ (S : Scheme.{u}) (X X' : AlgebraicSpace S) (i : X ⟶ X'),
  IsThickening (hom i) →
    IsRepresentedByScheme X → IsRepresentedByScheme X'
```

Thus every actual thickening of an algebraic space represented by a scheme
is represented by a scheme over the original base. The conclusion supplies
an actual `W : Over S` and a natural isomorphism
`(schemeYoneda S).obj W ≅ X'.presheaf`.
The universe, base, spaces and morphism are arbitrary. The thickening is
unrestricted, with no nilpotence-order bound. No affineness, Noetherian,
quasi-compactness, quasi-separatedness or target-representer hypothesis is
added. The published statement and its entire import closure are unchanged.

The entry theorem applies
`ThickeningAssembly.schemeness_of_finite_descent` to the published
`finiteSurjectiveAffineDescent`. The former already uses the published
`openFamilyLifting` and `openChartGluing` theorems. This discharges every
input proposition; no geometric result remains as an extra hypothesis.
The helper module `ThickeningAssembly` implements the following argument.

1. Choose a scheme over `S` representing `X`. Its native affine open cover
   gives actual affine schemes `U k : Over S`, open chart maps to
   `X.presheaf`, and local surjectivity of their presheaf coproduct for the
   slice fppf topology.
2. Apply `openFamilyLifting` to lift these charts across `i`. It supplies
   open algebraic spaces `V k` covering `X'` and actual unrestricted
   thickenings `(schemeToSpace S).obj (U k) ⟶ V k`.
3. Each chart thickening is finite by `IsThickening.finite` and
   geometrically surjective by its thickening hypothesis. Its source is
   represented by the absolute affine scheme `(U k).left`. Therefore
   `finiteSurjectiveAffineDescent` gives an actual affine scheme over `S`
   representing each `V k`.
4. Precompose the open inclusions of `V k` with these representing
   isomorphisms. `coproduct_cover_of_isos` preserves local coverage.
   `openChartGluing` then gives a scheme over `S` and a natural isomorphism
   representing `X'`.

The helpers use Mathlib's affine covers and relative morphism-property
and coproduct APIs, together with the published algebraic-space
definitions. They introduce no new axioms. The theorem uses only
`propext`, `Classical.choice` and `Quot.sound`.

The target is [Stacks Project Lemma 76.9.5, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR),
in registered source `stacks-algebraic-space-thickenings-2026-11-01`,
retained page `05ZJ.html`. Its general proof uses reductions and
Tag 07VU; its separate finite-order proof does not restrict the statement.
The implemented proof above is an alternative assembly using the
unrestricted published lifting theorem and finite-surjective affine descent,
[Lemma 70.15.1, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS).
That result is in registered source
`stacks-algebraic-space-affine-descent-2026-11-01`, retained page `07VQ.html`.
Its published proof contains the approximation and cohomological inputs.
The open-chart gluing theorem and its provenance are explained in
`OpenChartGluingProof.md`; the unrestricted lifting construction is
explained in `OpenFamilyLiftingProof.md` and `OpenSubfunctorLifting.md`.

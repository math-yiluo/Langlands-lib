# The generation locus of a positive power of a line-bundle section

`Langlands.SchemeModule.positiveSectionPowerGenerationLocus` proves the
published proposition
`Langlands.SchemeModule.PositiveSectionPowerGenerationLocusStatement.{u}` from
module `Langlands.AlgebraicGeometry.Modules.PositiveSectionPowerGenerationLocusStatement`.
The theorem's type is that proposition itself, with an arbitrary universe `u`
and no further hypotheses. For every scheme `X : Scheme.{u}`, every
`L : LineBundle X`, every global section `s` of `L.obj` and every `n : ℕ` with
`0 < n`, it proves the equality in `X.Opens`

```lean
trivializationOpen (tensorPow L.obj n) (sectionPow L.obj s n) =
  trivializationOpen L.obj s
```

of the whole maximal trivialization opens. The scheme is arbitrary, the
section may be zero, and every positive exponent is covered, including
`n = 1`, where the left side is the locus of `s ⊗ 1` in
`tensorObj L.obj (structureSheaf X)`. The powers are the published
right-associated `tensorPow` (module `Langlands.AlgebraicGeometry.Modules.Tensor`)
and the published recursive `sectionPow` (module
`Langlands.AlgebraicGeometry.Modules.SectionPowers`). The published statement
pair and everything it imports are unchanged.

All declarations of the module are public theorems in namespace
`Langlands.SchemeModule`, with universe parameter `u`:

- `trivializationOpen_sectionPow_zero (M : X.Modules) (s : GlobalSections M)`:
  `trivializationOpen (tensorPow M 0) (sectionPow M s 0) = ⊤`, for an
  arbitrary module sheaf `M` (no line-bundle property is used).
- `trivializationOpen_sectionPow_succ_eq_inf (L : LineBundle X) (s) (n : ℕ)`:
  `trivializationOpen (tensorPow L.obj (n + 1)) (sectionPow L.obj s (n + 1)) =
  trivializationOpen L.obj s ⊓ trivializationOpen (tensorPow L.obj n) (sectionPow L.obj s n)`.
- `trivializationOpen_sectionPow_succ (L : LineBundle X) (s) (n : ℕ)`: the
  successor-exponent form
  `trivializationOpen (tensorPow L.obj (n + 1)) (sectionPow L.obj s (n + 1)) =
  trivializationOpen L.obj s`, without a positivity hypothesis.
- `positiveSectionPowerGenerationLocus :
  PositiveSectionPowerGenerationLocusStatement.{u}`, the target.
- `trivializationOpen_sectionPow {X : Scheme.{u}} (L : LineBundle X)
  (s : GlobalSections L.obj) {n : ℕ} (hn : 0 < n)`: the consumer form, with
  exactly the target's conclusion. The scheme and the exponent are implicit
  arguments; otherwise its scope is that of the target.

In the first three, `X : Scheme.{u}` is an implicit variable.

## Implemented proof

### The zeroth power

`trivializationOpen_sectionPow_zero` shows that the zeroth power, the unit
section `1` of the structure sheaf, trivializes on the whole scheme. The
published `sectionHom_sectionPow_zero` identifies
`sectionHom (tensorPow M 0) (sectionPow M s 0)` with
`𝟙 (structureModule X)`, so this section morphism is an isomorphism. Its
image under the restriction functor to the open `⊤` is then an isomorphism, so
`TrivializesOn (tensorPow M 0) (sectionPow M s 0) ⊤` holds by definition
(module `Langlands.AlgebraicGeometry.Modules.SectionLocus`). Since
`trivializationOpen` is the supremum of all opens with this property, it
contains `⊤` and therefore equals `⊤`.

### The successor step

`trivializationOpen_sectionPow_succ_eq_inf` is one application of the
published theorem `Langlands.SchemeModule.tensorSectionGenerationLocus`
(module `Langlands.AlgebraicGeometry.Modules.TensorSectionGenerationLocusProof`),
which proves `TensorSectionGenerationLocusStatement`:
for line bundles `L` and `M` and sections `s` and `t`,
`trivializationOpen (tensorObj L.obj M.obj) (tensorSection L.obj M.obj s t)`
is `trivializationOpen L.obj s ⊓ trivializationOpen M.obj t`. It is applied to
`L`, to the line bundle

```lean
M = ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩,
```

and to the sections `s` and `sectionPow L.obj s n`. The proof that `M` is a
line bundle is the published theorem
`Langlands.AlgebraicGeometry.Picard.tensorPow_isLocallyFreeRankOne` (module
`Langlands.AlgebraicGeometry.Picard.TensorRankOneProof`), which states that every
tensor power of a line bundle is locally free of rank one. Since
`tensorPow L.obj (n + 1)` is by definition `tensorObj L.obj (tensorPow L.obj n)`
and `sectionPow L.obj s (n + 1)` is by definition
`tensorSection L.obj (tensorPow L.obj n) s (sectionPow L.obj s n)`, the
conclusion of that application is the stated equality without any rewriting.

### Induction

`trivializationOpen_sectionPow_succ` is proved by induction on `n`.

- For `n = 0`, the successor step gives
  `trivializationOpen L.obj s ⊓ trivializationOpen (tensorPow L.obj 0) (sectionPow L.obj s 0)`;
  the second open is `⊤` by `trivializationOpen_sectionPow_zero`, and
  `inf_top_eq` finishes.
- For `n + 1`, the successor step gives
  `trivializationOpen L.obj s ⊓ trivializationOpen (tensorPow L.obj (n + 1)) (sectionPow L.obj s (n + 1))`;
  the induction hypothesis replaces the second open by
  `trivializationOpen L.obj s`, and `inf_idem` finishes.

### The target and the consumer form

`positiveSectionPowerGenerationLocus` introduces `X`, `L`, `s`, `n` and
`0 < n`, writes `n = m + 1` with `Nat.exists_eq_succ_of_ne_zero`, and applies
`trivializationOpen_sectionPow_succ L s m`.
`trivializationOpen_sectionPow` is `positiveSectionPowerGenerationLocus X L s n hn`.

## Scope

Both sides are the whole maximal trivialization opens; no smaller
neighbourhood or affine subopen is chosen. The proof assumes no residue-field
comparison, pullback compatibility, flatness, quasi-coherence, coherence,
monoidal-preservation or ampleness hypothesis, and uses neither final
ampleness theorem. The rank-one property of the powers is the published
theorem `tensorPow_isLocallyFreeRankOne`, not an assumption, and the
tensor-section locus identity is the published theorem
`tensorSectionGenerationLocus`. The module defines no new tensor power,
section power, line bundle, locus or sheaf tensor. The axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The proposition is the fact `X_{s^n} = X_s` used in the proof of The Stacks
Project, Lemma 28.27.2 (tag 01PT), registered as
`stacks-ample-powers-restriction-quasiaffine-2026-10-24`; the statement's
Markdown explains how the source's locus is represented by the whole
trivialization open and the right-associated convention. The source gives no
further argument for this fact. The Lean proof is the induction above: the
locus of a product of two line-bundle sections is the intersection of their
loci (Stacks, Section 28.27, tag 01PR, `X_s ∩ X_{s'} = X_{ss'}`, proved in the
Library as `tensorSectionGenerationLocus`), and the unit section generates
everywhere.

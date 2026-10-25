# Normalization under ordered refinement coordinates

This module states the comparison between the composed and ordinary presentations
of the same ordered block parabolic. It defines propositions; it does not prove
them. The combined target is
`Langlands.Parabolic.RefinementCoordinatesNormalizationTheorem.{uF,uV}`.

## Quantifiers and concrete coordinate maps

The target quantifies over every natural prime `p` with `[Fact p.Prime]`,
every actual `F : PadicField.{uF} p`, every compatible
`T : F.TopologicalData`, every natural rank `n`, shapes
`B D : GeneralLinear.BlockShape n`, and refinement
`S : Geometric.BlockRefinement D`. Its coordinate data are exactly

- `e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length`;
- `hs : ∀ a, (S a.1).size a.2 = B.size (e a)`;
- `hc : ∀ i k x, D.index i ((S i).index k x) =
  B.index (e ⟨i,k⟩) (Fin.cast (hs ⟨i,k⟩) x)`.

Here `i`, `k` and `x` range respectively over `Fin D.length`,
`Fin (S i).length` and `Fin ((S i).size k)`. The size cast goes from the
inner block to the corresponding original block. There is no separately
assumed order law.

Write
`E_L = B.leviRefinementEquiv D S e hs F.Carrier` and
`E_P = B.parabolicRefinementEquiv D S e hs F.Carrier hc`.
These are the existing constructions in
`Langlands.Group.GL.RefinementCoordinates`. Their directions are
`B.Levi F.Carrier ≃* Geometric.refinedLevi F.Carrier D S` and
`B.parabolic F.Carrier ≃* Parabolic.composedParabolic F.Carrier D S`.
The parabolic map retains the underlying ambient matrix. No arbitrary
equivalence, subgroup equality or normalization identity is an input.

## The three clauses

The helper propositions lie in
`Langlands.Parabolic.RefinementCoordinatesNormalization`.

`ModulusClause F T B D S e hs` asserts, for every `m : B.Levi F.Carrier`,

```text
T.composedLeviModulus D S (E_L m) = T.leviModulus B m.
```

This is an equality in `ℝ≥0ˣ`. The composed character is the product of the
outer modulus restricted to the actual refined Levi and the product of the
inner block moduli. The ordinary character uses the ordered pairs of original
blocks, with determinant norms raised to the opposite block sizes.

`HalfModulusClause F T B D S e hs hc` asserts both

```text
∀ m, T.composedLeviHalfModulus D S (E_L m) = T.leviHalfModulus B m
∀ q, T.composedParabolicHalfModulus D S (E_P q) = T.parabolicHalfModulus B q.
```

The first quantifier ranges over `B.Levi F.Carrier`; the second over the actual
`B.parabolic F.Carrier`. Both equalities are in `ℂˣ`. Each half is the canonical
positive square root of its full positive modulus, embedded in complex units.
The parabolic characters are inflated through the actual Levi projections.
Thus the clause compares these specified positive halves themselves, rather
than just their squares.

`InductionClause.{uF,uV} F T B D S e hs` explicitly installs `T.topology`
and `T.generalLinearTopologicalGroup n`. It quantifies over every
`V : Type uV`, `[AddCommGroup V]`, `[Module ℂ V]`, and
`σ : Representation ℂ (B.Levi F.Carrier) V`. Put

```text
σL = σ.comp E_L.symm.toMonoidHom.
```

The inverse coordinate map is used here so that `σL` acts on the actual refined
Levi, with the same value space `V`. The clause asserts existence of

```text
E : Representation.Equiv
  (T.normalizedComposedInduced D S σL)
  (T.normalizedParabolicInduced B σ).
```

For every function `f` in the source and every `g : GeneralLinear n F.Carrier`,
the forward identity is
`Induction.eval _ _ (E f) g = Induction.eval _ _ f g`.
For every function `f` in the target and every such `g`, the inverse identity is
`Induction.eval _ _ (E.symm f) g = Induction.eval _ _ f g`.
Both are equalities in `V`. The equivalence is linear and intertwines the
actual right-translation representations.

These are the published `Induction.SmoothFunctions` carriers: covariant
functions on the same ambient matrix group, each with one open subgroup
stabilizing the entire function under right translation. Their carrier universe
is `max uF uV`; the field and value universes are independent. No topology is
required on `V`, and no smoothness assumption is imposed on `σ`. In particular,
the assertion includes every smooth `σ`.

The combined target quantifies over `e`, `hs` and `hc` and conjoins the three
clauses in the order above. The first and third helper predicates do not need
`hc` to be formed; they are conclusions under `hc` in the combined target,
not asserted unconditionally for arbitrary coordinates.
Rank zero and empty block families remain permitted. There are no irreducibility,
admissibility, finite-length, finite-dimensionality or positive-rank hypotheses.

## Provenance and proof boundary

This is an internal derived statement motivated by Bernstein and Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977).
Section 1.8, printed page 444 (PDF page 5), specifies positive-half left
covariance, a uniform open right stabilizer, and right translation.
Proposition 1.9(c), printed page 445 (PDF page 6), gives composition of
normalized induction, with the subsequent discussion explicitly requiring
compatibility of the normalizing factors. Sections 2.1–2.3, printed page 446
(PDF page 7), describe ordered standard block refinements and normalized
transitivity.

The retained source is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
registered as `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
These three original pages were read and the hash checked. No source-specific
errata directory was present in the workspace or current public notes.

The exact coordinate formulation and its extension to arbitrary input
representations through their constructed smooth induced spaces are internal
specializations of the imported definitions, not a separately quoted theorem
of the source. A later proof must compare the explicit determinant products,
pass through the same canonical positive square root, and use the published
coordinate/projection comparisons to preserve covariance and uniform right
stabilizers. This module does not supply that proof or prove the Haar-scaling
interpretation of the determinant modulus. Concrete adjacent and first/tail
coordinates, tensor regrouping, block-character absorption and induction in
stages are outside this statement unit.

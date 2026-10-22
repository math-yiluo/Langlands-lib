# Prime-degree norms after finite unramified base change

`Langlands.LocalClassField.PrimeNormAfterUnramifiedBaseChange.{u}` is a
`Prop`-valued definition. This module states the arithmetic target and does
not prove it.

## Exact statement and constructions

For every prime `p`, every `F : PadicField.{u} p`, and every actual finite
intermediate field `E` of `AlgebraicClosure F.Carrier / F.Carrier`, assume
`E/F` is Galois. Put `ell := Module.finrank F.Carrier E.field`. Assume
`ell` is prime and

```text
e(E) = ell * e(F),
```

where both indices are the canonical absolute ramification indices, with
`E` repackaged using `E.asPadicField (p := p)`. This is the derived p-adic
encoding of total ramification. It uses the compatible scalar maps from
`Q_p` and the canonical valuations; no independent valuation data are
supplied. A finite Galois extension of prime degree is cyclic, so a
separate cyclicity assumption is unnecessary.

For every `x : F.Carrierˣ`, the conclusion supplies:

- An actual finite intermediate field `K'` of the same algebraic closure,
  Galois over `F`, with `e(K') = e(F)` and `[K' : F] ≤ ell`.
- An actual finite intermediate field `M` and an equality
  `M.field = E.field ⊔ K'.field`. Thus `M` is exactly the compositum.
- An inclusion proof `h : K'.field ≤ M.field` and `y : M.fieldˣ` satisfying
  `FiniteIntermediateExtension.unitsNorm K' M h y =
  Units.map (algebraMap F.Carrier K'.field).toMonoidHom x`.

The quantifier over `x` is over all nonzero field elements, including
nonzero valuation. It is not restricted to units of the valuation ring.
The choice of `K'` may depend on `x`, and degree one is allowed. No bound
stronger than `≤ ell` is asserted. The common universe `u` is arbitrary.
Finiteness certificates are part of `FiniteIntermediateExtension`.

The imported `unitsNorm` installs the algebra structure from the actual
inclusion `h`, its scalar tower over `F`, and relative finite
dimensionality. It then uses `normUnits`, which is Mathlib's determinant
norm `Algebra.norm` on multiplicative groups. The target does not take a
norm map as input. The equality defining `M` prevents replacement of the
compositum by an arbitrary overfield.

## Original source and derived specialization

The source is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, Graduate Texts in Mathematics 67, Springer, 1979, registered as
`serre-1979-local-fields`. The retained original is
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The primary locator is Chapter V, section 4, Proposition 6 and its proof,
printed page 88 (PDF page 95); the ensuing corollary and its proof occupy
printed pages 88–89 (PDF pages 95–96). The setup for residue-field base
change starts on printed page 87 (PDF page 94). The supporting norm
filtration results are Chapter V, section 3, Propositions 4–5 and
Corollaries 1–7, printed pages 84–87 (PDF pages 91–94). Unramified lifts
and their embeddings are described in Chapter III, section 5,
Theorems 2–3 and their corollaries, printed pages 54–55 (PDF pages 61–62).

Serre's Proposition 6 treats a totally ramified cyclic extension of prime
degree over a complete discretely valued field with perfect residue
field. It produces a residue-field extension of degree at most that
prime such that the original nonzero element becomes a norm after the
corresponding unramified lift and compositum. The present target is its
p-adic specialization: finite residue fields are perfect, and their
finite extensions are separable and Galois. Thus the unramified lift is
Galois and its degree equals the residue degree, retaining the bound.
Realizing the lift inside the chosen `AlgebraicClosure` and expressing
ramification through the canonical absolute indices are derived encoding
choices, rather than literal notation in Serre.

The corollary passes to the maximal unramified extension and asserts norm
surjectivity there. This module isolates the finite base-change step; it
does not state or prove that corollary or the inertia-fixed-field norm
surjectivity target.

## Remaining arithmetic proof obligations

Serre reduces the full multiplicative norm obstruction to the critical
unit-filtration quotient at the ramification break `t`, using Corollary 7
to Proposition 5. For `t = 0`, the critical map on residue units is the
`ell`-th power map. For `t > 0`, necessarily `ell = p`, it is an additive
polynomial `a * z^p + b * z` with nonzero coefficients. A root of the
corresponding equation can be obtained in a residue extension of degree
at most `ell`. Section 4 shows that these norm polynomials have the same
coefficients after residue-field extension. Lifting that extension
unramifiedly removes the critical obstruction; the norm-filtration
surjectivity above the break then gives an actual field norm solution.

A Lean proof still needs the applicable ramified norm-filtration formulas,
the reduction of arbitrary multiplicative elements to the critical
quotient, the polynomial root degree bound, and compatibility of those
formulas under residue-field extension. It must also connect unramified
lifting in the specified closure to the canonical index convention,
identify the finite compositum and its inclusions, and transport the
resulting norm equation to the determinant-based `unitsNorm` in this
statement. The standard arithmetic justification uses linear disjointness
of a totally ramified extension and an unramified extension; its required
formal realization is not supplied here.

The existing `Langlands.LocalClassField.unramifiedUnitNorms` result in
`Langlands.ClassFieldTheory.Local.UnitNormProof` proves norm
surjectivity on valuation-unit filtrations for an extension that is itself
unramified. The extension whose norm occurs here is the base change of
`E/F` and remains totally ramified in the source argument. That existing
result does not prove this target. Unramified extension existence and
stage-containment constructions supply only part of the required
arithmetic, not the additional norm equation. In particular,
`Langlands.ClassFieldTheory.Local.unramifiedExtensionDegreeExistence` in
`UnramifiedExtensionDegreeProof` already supplies unramified Galois
intermediate fields of every positive degree; connecting a suitable such
field to the required critical residue solution remains part of the norm
argument.

No local reciprocity theorem, class formation, Brauer vanishing,
inertia cohomology vanishing, or parent inertia-fixed-field norm theorem
is assumed. This target is an arithmetic prerequisite for those later
arguments. Acceptance of this statement is not acceptance of its proof.

Authored by Worker 27.

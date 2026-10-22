# Finite norm surjectivity over the actual inertia fixed field

Author: Worker 60.

`Langlands.ClassFieldTheory.Local.InertiaFixedFieldNormSurjectivity.{u}`
is a proposition definition, not a proof. For every prime `p` and every
`F : PadicField.{u} p`, put

```lean
U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
```

For all fields `E L : Type u` with `Algebra U E`, `FiniteDimensional U E`,
`Algebra E L`, `FiniteDimensional E L`, and `IsGalois E L`, the proposition
asserts

```lean
Function.Surjective (Langlands.LocalClassField.normUnits E L)
```

Thus every element of `Eˣ` is the norm of some element of `Lˣ`. The prime
is universally quantified with `[Fact p.Prime]`; the common universe `u`
is arbitrary. These are all the quantified data and hypotheses.

## Exact fields, maps, and scope

`U` is the actual intermediate field of `AlgebraicClosure F.Carrier`
fixed pointwise by `F.absoluteInertia F.canonicalTopologicalData`. This
subgroup is the existing absolute inertia defined from the residue action
using the canonical topological data of `F`. Its fixed field has the
inherited field structure, the standard inclusion algebra over
`F.Carrier`, and the standard inclusion into that same algebraic closure.
No separately chosen field or postulated maximal unramified field occurs
in the proposition.

The quantified `Algebra U E` and `Algebra E L` give the tower
`U → E → L`. There is no independently supplied `U`-algebra on `L` that
could disagree with its composite algebra map. Finiteness of `L/U`
follows mathematically by composition of these finite extensions.
`E` and `L` may be arbitrary field presentations; they are not required
to be presented as intermediate fields of the chosen closure.
In particular, neither is required to be finite over `F.Carrier`:
finiteness is over the generally infinite field `U`, and then over `E`.
Since `U` contains the characteristic-zero field `F.Carrier`, `E/U` is
separable automatically. No separate separability hypothesis is imposed.
The explicit `IsGalois E L` includes the separability of `L/E`.

`Langlands.LocalClassField.normUnits E L`, imported from
`Langlands.ClassFieldTheory.Local.Norms`, is exactly
`Units.map (Algebra.norm E)`. It maps the full multiplicative group of
nonzero field elements, not just the units of a valuation ring.
`Algebra.norm` is the determinant norm for the given finite-dimensional
`E`-algebra `L`. No replacement norm, norm image, or chosen preimage
function is defined here.

There are no additional unramifiedness, finite-degree-over-`F`,
algebraically-closed-residue-field, fixed-field-identification, lifting,
norm-surjectivity, Brauer, or cohomology assumptions. The conclusion is
unconditional for the stated fields and finite Galois extension data.

## Original source and derived formulation

Jean-Pierre Serre, *Local Fields*, Greenberg English translation,
Springer GTM 67 (1979), registered as `serre-1979-local-fields`, retained
at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 60 read the following original passages. PDF page numbers count
from one. No project errata entry for this source was present when checked.

- Chapter III, section 5, Theorems 2–3 and Corollaries 1–3, printed
  pages 54–55 / PDF pages 61–62: construction of finite unramified
  extensions from finite separable residue extensions, their embeddings,
  and the maximal unramified extension as a directed union.
- Chapter IV, section 1, Proposition 1 and the corollary to Proposition 2,
  printed pages 62–63 / PDF pages 69–70: finite inertia and its fixed
  field, the maximal unramified subextension in a finite Galois extension.
- Chapter V, section 4, setup, Proposition 6 and its corollary, Lemmas 6–7,
  and Proposition 7, printed pages 87–90 / PDF pages 94–97. Proposition 6
  and its corollary establish the cyclic prime-degree norm calculation
  after unramified base extension. Lemma 6 descends finite extensions
  of directed unions to finite stages. Lemma 7 gives totally ramified
  finite models for finite extensions of the maximal unramified field.
  Proposition 7 concludes surjectivity of the multiplicative norm for
  finite separable extensions between finite extensions of that field.
- Chapter X, section 7, Proposition 11 and example b, printed pages
  161–162 / PDF pages 167–168: the norm condition for finite Galois
  extensions over finite separable extensions is equivalent to
  cohomological triviality and to Brauer vanishing. Example b applies
  V.4 Proposition 7 to the maximal unramified field.
- Chapter XII, section 1, Theorem 1, printed page 181 / PDF page 186:
  Brauer vanishing over the maximal unramified field and passage to a
  finite stage give finite unramified splitting fields.

The primary source theorem is V.4 Proposition 7. In Serre's notation its
base complete discretely valued field `K` corresponds to `F.Carrier`,
its maximal unramified extension `K_nr` must be identified with the
precise `U` above, and its finite tower `F/E/K_nr` corresponds to the
Lean tower `L/E/U`. The residue field of a p-adic local field is finite,
hence perfect, as required by Serre. The present target restricts his
finite separable top extension to a finite Galois extension. It is an
internally derived actual-fixed-field specialization, not a verbatim
statement of the source. The X.7 and XII.1 passages explain its intended
use in the subsequent inertia cohomology argument; their conclusions
are not asserted or assumed by this file.

## Arithmetic and comparison work still required

A later proof must implement the following bridges or an equivalent
argument for these exact objects.

1. Relate the canonical valuation and residue action used to define
   absolute inertia to the finite unramified extensions in Serre III.5.
   Establish that `U` is exactly their directed union inside the chosen
   algebraic closure. This needs both containment directions and the
   finite-level inertia/fixed-field comparison, with compatibility
   through finite Galois extensions. Defining `U` as a fixed field does
   not establish this arithmetic identification.
2. Descend arbitrary finite `E/U` and finite Galois `L/E` to compatible
   finite models over sufficiently large finite unramified subextensions
   of `F.Carrier`, preserving degrees, the Galois structure, and the
   required linear disjointness. Identify these extensions with the
   maximal unramified extensions of their totally ramified models, as
   in Lemmas 6–7. This includes passage from abstract `E` and `L` to
   compatible embeddings or algebra-equivalent presentations.
3. Prove the actual norm arithmetic of V.4: cyclic prime-degree
   surjectivity after unramified base extension, then the reduction
   through the solvable totally ramified Galois group and norm
   transitivity. The residue perfection and valuation hypotheses must
   come from the p-adic field and the constructions, not be supplied
   as extra premises of this target.
4. Check determinant norm compatibility under the finite-stage base
   changes and the field/algebra equivalences used in this descent,
   and transfer the resulting surjectivity to the literal map
   `Langlands.LocalClassField.normUnits E L` on units.

The published proposition `Langlands.PadicField.CanonicalUnramifiedCriterion`
supplies a target for the finite Galois inertia criterion. Its proof is
separate work; even that finite criterion alone does not supply the
infinite directed-union identification, finite descent, or the norm
argument above. The published `Langlands.Galois.Local.AbsoluteProof`
proves inertia closedness and residue exactness, which also do not by
themselves prove these arithmetic assertions. `UnitNormProof` concerns
finite unramified p-adic extensions and does not cover this generally
infinite base field. `ClosureRestrictionTransport` and
`ClosureUnitTransport` provide Galois/topological/coefficient transports
for normal intermediate fields without a finiteness assumption; they
supply no arithmetic norm theorem. No new such transport is constructed
here.

Only the proposition target is defined in the Lean file. A proof of it,
the subsequent deduction of `InertiaH2Vanishing`, and the finite
unramified splitting theorem remain separate obligations. Existing
statement, proof, and transport files are unchanged.

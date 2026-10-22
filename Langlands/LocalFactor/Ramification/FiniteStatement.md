# Finite-Galois Artin and Swan conductor statements

Worker 70 states one coherent family about the published rational Artin and Swan
conductor sums. These are proposition definitions, with no theorem proofs or
new arithmetic constructions. The combined target is
`Langlands.Ramification.Padic.FiniteGaloisConductorStatement`.

## Domain and concrete objects

The combined target quantifies over every prime `p`, every actual
`PadicField p` named `F`, and every compatible `F.TopologicalData` named `T`.
The base `K` is a field equipped with `Algebra (Padic p) K`,
`Algebra K F.Carrier`, and the compatible scalar tower. Since `F.Carrier` is
finite dimensional over `Padic p`, both the intermediate base and the extension
over it are finite dimensional. Each component explicitly requires
`IsGalois K F.Carrier`; this hypothesis is inside its proposition and cannot
be dropped by Lean's section-variable elaboration.

The group is the actual algebra-automorphism group
`F.Carrier ≃ₐ[K] F.Carrier`. The supplied valuation ring and its residue action
give `inertia T K` and `lowerRamificationGroup T K i`. The conductor functions
are exactly `artinConductor T K` and `swanConductor T K`, which specialize the
published finite weighted sums

`a(ρ) = Σ_{i≥0} |G_i|/|G_0| · (dim V − dim V^{G_i})`,

`sw(ρ) = Σ_{i≥1} |G_i|/|G_0| · (dim V − dim V^{G_i})`.

The denominator for both sums is the inertia cardinality. Finite support is
proved in the imported construction. No truncation, termination assertion,
abstract factor value, or integrality assumption is an input here.

The coefficient field is specifically `ℂ`. Each carrier is an actual finite
dimensional complex vector space, with an actual `Representation`. The field
carriers and the three representation carriers have independent universe
parameters `uK`, `uL`, `uU`, `uV`, and `uW`. A representation of this finite
group is automatically an action by invertible linear maps. The statements
include the zero vector space and do not assume irreducibility or faithfulness.

## The seven components

1. `FiniteGaloisConductorIntegralityStatement` says that each actual rational
   sum equals the rational cast of some natural number. This simultaneously
   expresses nonnegativity and integrality of both conductors.
2. `FiniteGaloisConductorExactSequenceStatement` uses three representations
   and genuine `IntertwiningMap`s `i : U → V` and `q : V → W`. Its hypotheses
   explicitly require injectivity of `i`, equality of its linear range with
   the kernel of `q`, and surjectivity of `q`. Each middle conductor is the
   sum of the two endpoint conductors.
3. `FiniteGaloisConductorDirectSumStatement` specializes additivity to
   Mathlib's `ρ.prod σ`, on `V × W` with componentwise action. A binary
   product of vector spaces is their binary direct sum.
4. `FiniteGaloisConductorDualStatement` uses Mathlib's actual `ρ.dual` on
   `Module.Dual ℂ V`, with action
   `(ρ.dual g ℓ)(v) = ℓ(ρ(g⁻¹)v)`. Both conductors are unchanged.
5. `FiniteGaloisConductorUnramifiedTwistStatement` uses a homomorphism
   `χ : G →* ℂˣ` with `χ g = 1` for every `g` in actual inertia. The published
   `Langlands.twist χ ρ` acts on the same space by
   `(χ g : ℂ) • ρ g`. This is the scalar realization of tensoring with the
   actual one-dimensional representation `Langlands.characterRepresentation χ`.
   Both conductors are unchanged.
6. `FiniteGaloisConductorVanishingStatement` gives both equivalences:
   Artin vanishes exactly when every inertia element fixes every vector;
   Swan vanishes exactly when every element of the first lower group fixes
   every vector. These are conditions on the representation, not assertions
   that the corresponding field-theoretic ramification subgroup is trivial.
7. `FiniteGaloisTameArtinStatement` says that trivial action of the first
   lower group makes the Artin conductor equal to
   `fixedCodimension G ρ (inertia T K)`, cast to `ℚ`. This is the natural
   codimension of the actual inertia-fixed subspace.

## Original sources and correspondence

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979:

- Literature ID: `serre-1979-local-fields`.
- Retained file: `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
- SHA256: `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
- Read Chapter VI, sections 1–2, printed pages 97–102, PDF pages 104–109.
  Section 1 fixes finite-dimensional complex representations. Section 2,
  Theorem 1' on printed page 99 is nonnegative integral Artin conductor for
  every character of the finite Galois group. Proposition 2 and Corollary 1'
  on pages 100–101 identify this conductor with the weighted fixed-space
  codimension sum. Page 102 contains the proof of Theorems 1 and 1'.

The Artin half of component 1 is a direct translation of Theorem 1', expressed
on a representation through Corollary 1'. Replacing a nonnegative integer by a
natural witness embedded in the rationals preserves its content. The finite
p-adic Galois domain is a specialization of Serre's complete discrete valuation
field setting. No theorem about arbitrary local-ring actions or arbitrary
coefficient fields is inferred.

Pierre Deligne, *Les constantes des équations fonctionnelles des fonctions L*,
Lecture Notes in Mathematics 349 (1973), 501–597:

- Literature ID: `deligne-1973-local-constants`.
- Retained file:
  `/home/taskhub/central-library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`.
- SHA256: `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
- Read section 4.5, internal/PDF pages 37–38, printed pages 537–538,
  especially equations (4.5.1)–(4.5.4). The Swan representation is obtained
  by removing the augmentation representation from the Artin representation;
  equation (4.5.4) gives Artin as Swan plus inertia codimension.

The Swan half of component 1 is the derived positive-tail formulation:
the published decomposition subtracts the integral inertia codimension from
the integral Artin value, and every positive-index term is nonnegative.
Thus the rational Swan value is a nonnegative integer. This agrees with
Deligne's definition and is not attributed to a separate Swan assertion in
Serre's Theorem 1'.

Components 2–7 are derived formulations of the weighted fixed-space formula,
not literal restatements of separately numbered theorems in these pages.
For a finite group over `ℂ`, averaging a lift over any subgroup shows that
taking invariant vectors preserves short exact sequences. Dimensions and
fixed dimensions therefore add, giving component 2 term by term. The canonical
inclusion and projection for `V × W` give component 3. Averaging also identifies
the invariant dual with the dual of the invariant space, preserving its
dimension and giving component 4. A twist trivial on inertia leaves each
lower-group action unchanged, giving component 5.

Every summand is nonnegative. The index-zero term detects inertia-fixed
codimension, and every positive-index group is contained in the first lower
group. Conversely, the index-one Swan weight is positive since both finite
groups contain their identity. A zero Swan sum therefore forces the first
fixed-space codimension to vanish. In finite dimension zero codimension means
the entire space is fixed. These observations give component 6. Component 7
then uses the already published decomposition and the vanishing of Swan.
These explanations describe mathematical derivations of the statement family;
no corresponding Lean theorem proofs are claimed by this module.

## Reuse and scope

The import `Langlands.LocalFactor.Ramification.Descent` brings in the current
Library's `Filtration`, `Conductor`, and `Galois` modules. The finite-support
proofs, `Padic.artinConductor_equiv`, `Padic.swanConductor_equiv`, and explicit
quotient/descent constructions remain existing results, with no duplicate
proposition targets here. The tame consequence uses
`Langlands.Ramification.artinConductor_eq_tame_add_swan`, specialized to the
same integer-ring action as the Padic conductor, and
`Padic.lowerRamificationGroup_zero`. It does not restate that decomposition
as a new obligation.

The twist constructor is imported from the published
`Langlands.Representation.Twist.Definitions`; products, duals, and intertwiners
are the pinned Mathlib interfaces. No substantial prerequisite definition is
missing. No Artin-character construction, comparison between distinct
extensions, upper numbering, reciprocity transport, epsilon system, or
Weil–Deligne factor is asserted.

Prepared environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Lean commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Independent semantic acceptance and current Library publication are separate
from compilation.

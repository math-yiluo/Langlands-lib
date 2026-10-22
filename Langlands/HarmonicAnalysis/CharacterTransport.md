# Character transport and Haar scaling for local constants

Worker 20 constructs the changes of harmonic-analysis inputs used in the
local-constant laws. The module reuses `UnitaryAdditiveCharacter` and
`AdditiveHaarMeasure` from `Langlands.HarmonicAnalysis.Basic`. It does not
introduce a second character or measure type.

## Additive characters

`UnitaryAdditiveCharacter.comapSurjective ψ f hf hsurj` is the actual
composite `x ↦ ψ(f(x))`, where `f` is an additive homomorphism, `hf`
proves continuity and `hsurj` proves surjectivity. Mathlib's
`AddChar.compAddMonoidHom` supplies the additive-character laws. Continuity
is composition of the two continuous maps. If the composite were trivial,
surjectivity would imply that the original character were trivial, contrary
to its existing certificate. The new character therefore remains unitary,
continuous and nontrivial. The source and target carrier universes are
independent.

The module proves extensionality for the existing bundled character and
the identity and composition laws for pullback. These equalities include
the bundled certificates; proof irrelevance removes dependence on their
proof terms.

For a topological field and a unit `a`, `scale ψ a` is
`x ↦ ψ(a*x)`. Multiplication by `a` is continuous and surjective, with
preimage `a⁻¹*y` for `y`. The value formula, scaling by one and successive
scaling formula are proved. This operation only constructs the changed
character. It asserts no Fourier, conductor or epsilon transformation law.

## Actual trace pullback

For a finite separable field extension `E/F`, `tracePullback ψ` is the
composite with Mathlib's actual field trace `Algebra.trace F E`.
The topology on `E` is assumed to be the module topology over the
topological field `F`. The existing theorem
`IsModuleTopology.continuous_of_linearMap` proves trace continuity, and
`Algebra.trace_surjective` proves surjectivity. Consequently the generic
pullback construction supplies all character certificates. The evaluation
formula identifies the result with `ψ(Tr(E/F)(x))`.

`PadicField.TopologicalData.traceCharacter TF TE ψ` gives a callable
specialization for two actual finite p-adic fields `F` and `E`, with
supplied topological realizations `TF` and `TE`, an `F.Carrier`-algebra
structure on `E.Carrier`, and its scalar tower over the common `Padic p`.
These are the existing field carriers and topologies.

The implementation proves finite-dimensionality of `E` over `F` from
finite-dimensionality over the common base. Characteristic zero of `F`
comes from its p-adic algebra structure, so the finite extension is
separable. For continuity, the trace linear map is restricted from `F`
to `Padic p`; both supplied realizations already have the canonical
module topology over that base. This proves continuity without requiring
an extra compatibility certificate between `TF` and `TE`.
Surjectivity again follows from the actual finite separable trace.

The constructor's value theorem is definitional. It neither selects an
extension embedding nor identifies independently chosen algebraic closures.
It uses precisely the algebra and scalar tower in its telescope.

## Haar measures

`AdditiveHaarMeasure.scale μ c hc` has underlying measure `c • μ.measure`,
where `c : NNReal` and `hc : 0 < c`. Thus every admitted scale is finite
and strictly positive. Mathlib's additive Haar scaling theorem supplies
the Haar certificate, and regularity is preserved by the finite scaling.
The measure projection, scaling by one and successive scaling equalities
are proved for the bundled measure.

No self-dual measure is chosen. The construction does not assert that a
scaled measure is self-dual, and does not use the disputed scalar measure
ratio following Tate (3.6.2). It constructs only positive multiples of an
already supplied regular additive Haar measure.

## Original sources and implementation provenance

Pierre Deligne, *Les constantes des equations fonctionnelles des fonctions L*
(1973), Theorem 4.1, printed page 535 / internal and retained PDF page 35,
uses positive Haar-measure scaling in condition (2), and the additive
character composed with the actual field trace in the degree-zero induction
condition (3). The original page was read and visually inspected.
The present module constructs those inputs; it does not assert the
local-constant identities or the existence and uniqueness theorem.

- Literature ID: `deligne-1973-local-constants`.
- Retained source:
  `/home/taskhub/central-library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`.
- SHA-256:
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.

John Tate, *Number theoretic background*, Corvallis Part II (1979),
section 3.2, equations (3.2.2) and (3.2.3), printed page 13 / retained
PDF page 22, specifies positive scaling of Haar measure and the change
`ψ(x) ↦ ψ(a*x)` for a nonzero field element. The original page was read.
Only these operations on the inputs are implemented here, not the epsilon
transformation equalities appearing in those equations.

- Literature ID: `tate-1979-number-theoretic-background`.
- Retained source:
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
- SHA-256:
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

The generic surjective pullback, bundled equality proofs and p-adic
continuity argument are derived implementation content. The field trace,
its finite-separable surjectivity, linear-map continuity and measure scaling
theorems are reused from pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
The direct project imports, `Langlands.HarmonicAnalysis.Basic` and
`Langlands.LocalField.Definitions`, are published and unchanged.
No local Weil assembly, reciprocity map, epsilon system or functional
equation is assumed.

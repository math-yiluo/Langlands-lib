# Involutivity of the actual unadjusted Aubert operator

Author: Worker 320.

`Langlands.Aubert.InvolutivityStatement.{uF,uV} F T` is the proposition
that, for every natural rank `n`,

```text
(alternatingOperator F T n).comp (alternatingOperator F T n) = LinearMap.id.
```

The equality is in the integer module of linear endomorphisms of
`GeneralLinear.FiniteLengthGrothendieckGroup.{uV,uF} n F.Carrier`.
Thus it concerns every virtual class, including differences of actual
representation classes. This module defines a proposition and supplies no
proof of it.

## Original source and translation

Registered source `aubert-1995-duality`: Anne-Marie Aubert, *Dualité dans le
groupe de Grothendieck de la catégorie des représentations lisses de longueur
finie d'un groupe réductif p-adique*, Transactions of the American
Mathematical Society 347 (1995), 2179–2189. Retained PDF SHA-256:
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
The precise statement is Théorème 1.7(3), printed p.2181, one-based PDF p.3.
Its proof is on printed p.2183, one-based PDF p.5. Both pages were directly
checked as rendered images for this module.

Définition 1.5 on printed p.2181 defines the unadjusted operator
`D_G = sum_{I ⊆ S} (-1)^|I| i_I r_I`, using normalized induction and
Jacquet restriction. Théorème 1.7(3) asserts `D_G² = Id`. For `GL_n` in
positive rank, the ordered positive block shape `B` corresponds to the
subset of simple roots inside its blocks. Its cardinality is
`n - B.length`. Consequently the imported `alternatingOperator`, whose
summand is `(-1 : ℤ)^(n - B.length)` times induction after Jacquet, is
precisely the block-shape version of that source operator.

This statement uses that existing operator unchanged. It makes no
cuspidal-support-dependent sign adjustment. The adjusted operator of
Définition 2.1 is a separate construction.

## Actual objects, universes and normalization

The outer parameters are arbitrary `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p`, and supplied `T : F.TopologicalData`. The
proposition installs `T.topology`. Field universe `uF` and carrier parameter
`uV` remain independent; the actual smooth complex representation carriers
used by the group and functors are in `Type (max uF uV)`.

The imported group is the exact Grothendieck group of actual smooth
representations of finite group-algebra length, using relations from all
actual short exact sequences, including nonsplit ones. It does not require
finite-dimensional representations. The imported maps are induced by the
actual normalized upper-block parabolic induction and Jacquet functors.
Induction uses positive half-modulus covariance and right translation;
Jacquet restriction uses upper-unipotent coinvariants with inverse
half-modulus Levi action. Their preservation and exactness arguments are
already supplied by the imported operator construction.

There is no admissibility, central-character, irreducibility, cuspidality,
tensor-factorization or extra theorem-valued premise in this proposition.
In particular, `∀ n : ℕ` includes zero. At rank zero the unique shape is
empty and has sign `(-1)^0 = 1`; both `GL_0` and the empty Levi are trivial.
The asserted identity in that case is the natural empty-root-system case
of the formula. Establishing it for the actual imported functors is part
of the future proof, rather than a theorem of this statement module.

## Proof obligations and independence

The source proof on printed p.2183 commutes `D_G` past induction using
Théorème 1.7(2), expands the operator on each Levi, applies transitivity,
and cancels the alternating sum over supersets of a root subset. Only
the full-root term remains. This describes the source route and is not a
Lean proof. A finite Solomon or pointwise Weyl coefficient formula alone
does not supply the required identity of actual representation maps.

The source induction-commutation proof uses the whole-Levi conjugacy
identity (1.2), whose printed citation needs a separately checked
classification-independent replacement in the upstream segment
classification application. The published source audit
[`notes/henniart/aubert-duality-route.md`](../../../notes/henniart/aubert-duality-route.md)
records that boundary and the corrections to later irreducibility
arguments. This statement assumes no such replacement theorem and proves
no irreducible-image or segment-classification result.

The sole direct import is
`Langlands.Representation.Aubert.AlternatingOperator`; no existing Lean or
Markdown pair is edited. A future proof must remain independent of the
analytic segment classification, multisegment exhaustion, ordered
strong-head existence, quotient exhaustion, tempered block uniqueness,
square-integrable Langlands classification or exhaustion, and regular
Langlands exhaustion, including their proof successors and transitive
proof dependencies. These are proof-route obligations, not hypotheses
added to `InvolutivityStatement`.

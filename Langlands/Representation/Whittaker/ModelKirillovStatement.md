# Kirillov lifting into actual coefficient models

Author: Worker 332.

This module defines the propositions
`Langlands.Whittaker.IsMirabolicTestFunction` and
`Langlands.Whittaker.ModelKirillovTransferStatement`. The latter is an internal
consumer adapter from the existing full
`Langlands.WhittakerTypeKirillovStatement` to supplied field topologies and
actual coefficient images. Neither the adapter nor Kirillov surjectivity is
proved here; the canonical Kirillov proposition occurs once as an explicit
antecedent, not as an axiom.

## Mirabolic test functions

For a field `F` with a topology, a unitary additive character `ψ`, and `n : ℕ`,
the input `φ : Langlands.RankinSelberg.WhittakerFunctions ψ n` is an actual
function on `GL_(n+1)(F)` with global left covariance
`φ(u * g) = standardCharacter ψ n u * φ(g)` for every element of the actual
`upperUnipotent (n + 1) F`. Its subtype already imposes this condition.
The helper can be formed from `[Field F] [TopologicalSpace F]`; in particular
it applies to any topological field without requiring local-field structure.

`IsMirabolicTestFunction ψ n φ` adds exactly two conditions:

1. There is an `OpenSubgroup K` of the ambient general linear group such that
   `φ(q * k) = φ(q)` whenever `q` and `k` are mirabolic and `k ∈ K`.
2. There is an ambient compact set `C` such that every mirabolic `q` with
   `φ(q) ≠ 0` has the form `u.val * c`, where
   `u : upperUnipotent (n + 1) F` and `c ∈ C`.

Each occurrence of “mirabolic” is the actual last-row condition
`∀ a, q.val (Fin.last n) a = if a = Fin.last n then 1 else 0`.
It is the same condition used by `WhittakerTypeKirillovStatement`.
The module defines no competing mirabolic group. The smoothness condition
tests right multiplication only by the intersection of `K` with the
mirabolic subgroup. The support condition bounds only the mirabolic
restriction modulo the upper-unipotent subgroup; it does not require compact
support on the whole general linear group.

In the p-adic setting of the transfer statement, these are the concrete
smoothness and compact-modulo-unipotent conditions of the compact mirabolic
model. Although `C` is an ambient compact set, `q = u.val * c` forces each
representative `c` used there to be mirabolic. The existing
`KirillovStatement.md` explains the relation with compact representatives
inside the closed mirabolic subgroup and with open subgroups of that subgroup.

The values of `φ` off the mirabolic subgroup are harmless ambient data, subject
to its existing global covariance. The helper imposes no smoothness or support
condition there, and the lifting conclusion compares values only at actual
mirabolic matrices. In particular, it does not assert equality of the ambient
functions.

## Conditional transfer

`ModelKirillovTransferStatement.{uF,uV}` assumes the already-published
`WhittakerTypeKirillovStatement.{uF,uV}` and then quantifies over every prime
`p`, every `F : PadicField.{uF} p`, and every supplied
`T : F.TopologicalData`. It installs `T.topology` before all the subsequent
topological inputs and conditions.

For every `n : ℕ`, complex module `V : Type uV`, representation `π` on
`GL_(n+1)(F)`, and `ψ : UnitaryAdditiveCharacter F.Carrier`, it assumes
`Langlands.RankinSelberg.IsOfWhittakerType n (standardCharacter ψ n) π`.
This is admissibility, finite generation over the complex group algebra,
and a linear equivalence of the actual functional space with `ℂ`. It allows
reducible representations and imposes no topology on `V`.

For every actual `ℓ : glFunctionals ψ n π` with `ℓ.val ≠ 0`, and every `φ`
satisfying the helper, the conclusion supplies
`f : (coefficientModel π ℓ).toSubmodule` with
`f.val.val q = φ.val q` for every mirabolic `q`. The model is the actual
coefficient-map image belonging to the specified functional. There is no
choice of a preferred functional. The universes `uF` and `uV` are independent,
and `n = 0` is included, so the group has rank one in that case.

This interface contains no integration, convergence, unit-integral,
normalized-generator, irreducibility or supercuspidality conclusion or
additional hypothesis. Those belong to separate consumers and results.

## Provenance and relationship to existing transfers

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`. Printed pages 385–386
(one-based PDF pages 20–21) were read visually. Section 2.1, page 385,
defines Whittaker type by admissibility, finite type and a one-dimensional
functional space. Equation (3), page 386, defines the coefficient functions.
Section 2.2 on that page defines the smooth, covariant, compact-modulo-unipotent
functions on the mirabolic subgroup, denoted `K₀(ψ)`, and states their inclusion
in the restricted Whittaker model `K(π; ψ)`, with attribution to [G-K].
The present module relies on this JPSS passage and the existing canonical
statement; it does not claim an independent reading or proof of [G-K].

The test-function predicate extracts the two additional conditions from that
source's compact mirabolic model, using the existing covariance subtype.
The conditional supplied-topology/coefficient-image formulation is an internal
derived interface, not a separately quoted theorem of JPSS.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
No JPSS errata entry was found in the checked project or Library notes.

The published
`Langlands.Representation.RankinSelberg.ModelAsymptoticProof` provides a
comparison for a future proof: `topology_eq_canonicalModule` identifies each
supplied topology with the canonical one, and `modelMap_surjective` converts
coefficient-image elements to representing vectors. For the direction here,
a vector obtained from canonical Kirillov lifting would be sent into the image
by `modelMap`. The existing `standardCharacter_eq_product` and
`mem_glFunctionals_iff_entrywise` in `Whittaker.PrerequisiteInterfaces` connect
the bundled character and functionals with entrywise formulas. These are
available proof techniques, not a proof in this file; asymptotic transfer
does not establish Kirillov lifting.

The module imports `Whittaker.KirillovStatement` for the canonical antecedent
and `RankinSelberg.AnalyticStatement` for `IsOfWhittakerType` and its existing
function and coefficient-model dependencies. Existing Library declarations
and their imports are unchanged.

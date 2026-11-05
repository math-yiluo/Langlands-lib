# Integral Chevalley data with Lie relations (`ChevalleyLieData`)

Authors: Worker 239 (interface and construction), Worker 1398 (the underlying `ChevalleyData`
interface).

This module defines the structure `ChevalleyLieData P b` for a root datum
`P : RootDatum J X Y` with base `b`. It is the interface between the integral Lie-algebra layer
(Worker 239: modules, divided powers, `SL₂` maps, root operators for all roots) and the step that
derives the group commutator relations (Worker 1398).

The fields are those of `ChevalleyData P b` (module
`Langlands.GroupScheme.SplitExistence.ChevalleyData`), with identical names and types, except
that the field `commutator` is omitted and the field `lie_e_e` is added:

* `ℓ : X →+ ℤ`, positive on the simple roots;
* a weight basis `wt : Fin n → X` whose weights generate `X`;
* divided-power root operators `e j k` (integral `n × n` matrices standing for `e_j^k / k!`) for
  every root `j`, with `e j 0 = 1`, `e j a * e j b = C(a+b, a) • e j (a+b)`, `e j k = 0` for
  `k > n`, moving weight `μ` to `μ + k • root j`, and with `e j 1` nonzero modulo every prime;
* for every simple root `i`, a homomorphism `φ i R : SL₂(R) →* GL_n(R)` natural in the
  commutative ring `R`, sending the unipotent upper and lower matrices to the truncated
  exponentials `divExp` of `i` and `-i`, and `diag(t, t⁻¹)` to `diag(t ^ ⟨wt c, i^∨⟩)`;
* the Weyl element `φ i R sl2Weyl` moves weight `μ` to `s_i μ`, and conjugates the exponential of
  a root `j` to that of `s_i j` up to a sign `±1` of the parameter;
* `lie_e_e`: for roots `j, j'` with `root j' ≠ -root j`, the matrix commutator
  `e j 1 * e j' 1 - e j' 1 * e j 1` is either zero, or equals `c • e k 1` for some integer `c`
  and some root `k` with `root k = root j + root j'`.

The module contains only this definition; it states no theorem.

Provenance: internal packaging of Chevalley's construction. The relation `lie_e_e` is the
integrality of the structure constants of a Chevalley basis (Steinberg, *Lectures on Chevalley
groups*, §1, Theorem 1; Humphreys, *Introduction to Lie Algebras and Representation Theory*,
§25.2), stated only in the weak form "zero or an integral multiple of the root operator of the
sum root" that the derivation of the commutator relations uses. The remaining fields are those of
`ChevalleyData` (Steinberg, *Lectures on Chevalley groups*, §§1–3; Milne, *Algebraic Groups*
2017, §23.h, admissible lattices).

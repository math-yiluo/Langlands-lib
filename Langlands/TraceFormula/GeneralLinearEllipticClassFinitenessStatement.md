# Finiteness of rational classes meeting a compact adelic regular elliptic set

`Langlands.TraceFormula.GeneralLinearEllipticClassFinitenessStatement` is a
Prop-valued definition. This module states the proposition and supplies no proof.

## Statement and Library objects

For every number field `K : Type u` in an arbitrary universe, every natural number
`n`, every finite place `v : Langlands.Global.FinitePlace K`, and every set
`Ω : Set (Langlands.Global.AdelicGL K n)`, assume:

- `IsCompact Ω`;
- for each `ω ∈ Ω`, the local component
  `FiniteAdelicGL.localProjection K n v (AdelicGL.finite K n ω)` is
  `Langlands.JacquetLanglands.IsRegularElliptic` over the completion `K_v`.

Then there exists `R : Finset (Langlands.Global.RationalGL K n)` such that
for every `γ : RationalGL K n`, if
`x⁻¹ * AdelicGL.rational K n γ * x ∈ Ω` for some `x : AdelicGL K n`, then
`IsRegularElliptic γ` over `K` and
`y⁻¹ * γ * y = r` for some `r ∈ R` and `y : RationalGL K n`.
Thus the rational elements whose adelic conjugacy orbit meets `Ω` lie in finitely
many rational conjugacy classes, and each such element is regular elliptic.
The proposition places no requirement on unused representatives in `R`.
There is no positive-rank or nonemptiness hypothesis.

The groups are the Library's concrete matrix groups: `RationalGL K n` is
Mathlib's `Matrix.GeneralLinearGroup (Fin n) K`; `AdelicGL K n` is the
matrix unit group over `AdeleRing (𝓞 K) K`, with its unit-group topology.
`AdelicGL.rational K n` applies the diagonal ring map to matrix entries.
`AdelicGL.finite K n` projects to the finite adelic matrix group, and
`FiniteAdelicGL.localProjection K n v` evaluates at the finite place `v`,
with codomain `FiniteLocalGL K n v = GL_n(K_v)`. Finite places are height-one
primes of the ring of integers. `IsRegularElliptic` means that the characteristic
polynomial is separable and irreducible over the indicated field. No replacement
groups, projection maps or ellipticity predicates are introduced here.

## Sources and derived provenance

This is derived content specialized to `GL_n`; the cited sources do not print this
exact Lean formulation with a finite set of rational matrix representatives.
The statement's name and Lean form are chosen for the identity-twist application
to the abstract simple twisted trace formula.

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), registered
  `getz-hahn-2024-automorphic-representations`, Lemma 17.7.11, printed pp. 461–462:
  if a smooth affine group with reductive identity component acts on an affine
  scheme of finite type, only finitely many closed geometric orbits defined over
  the global field can meet a compact adelic set in the stated way. The proof
  uses that rational points of the affine quotient are closed and discrete in
  its adelic points. Lemma 18.2.6, printed p. 479, is the analogous finiteness
  statement in the setting modulo the split centre; it is used for the geometric
  side of the simple relative trace formula, Theorem 18.2.5 on the same page.
  The retained October 2026 errata, registered
  `getz-hahn-2024-errata-2026-10`, p. 4, clarify the standing affine-group convention
  in Chapter 17 and add a proof-ending symbol in §18.2; they do not alter these
  finiteness statements.
- Deligne–Kazhdan–Vignéras, *Représentations des algèbres centrales simples
  p-adiques*, in *Représentations des groupes réductifs sur un corps local* (1984),
  registered `bdkv-1984-representations-local-field`, Appendix A.1, especially
  printed pp. 43–44: regular ellipticity in one local component ensures global
  ellipticity, and local regular elliptic support excludes the other rational
  conjugacy classes. A.1.c gives the simple trace formula as a sum indexed by
  images of regular elliptic rational elements modulo the centre; A.1.d gives
  sufficient local hypotheses for that formula. Here the conclusion concerns
  conjugacy in the full rational matrix group, without quotienting by its centre.

The specialization is justified by the following mathematical route for a
proof; none of its steps is proved in this module. The proof is
`Langlands.TraceFormula.generalLinearEllipticClassFiniteness`, in the separate module
`Langlands.TraceFormula.GeneralLinearEllipticClassFinitenessProof`. The characteristic polynomial
is continuous in its coefficients and invariant under conjugation. Its coefficient
vectors on `Ω` therefore form a compact subset of `𝔸_K^n`. The rational vectors
`K^n` form a closed discrete subset, so only finitely many such vectors occur.
If the adelic orbit of `γ` meets `Ω`, its characteristic polynomial becomes
separable and irreducible over `K_v`: local projection preserves conjugation.
Separability descends along the field embedding, and any nontrivial factorization
over `K` would persist over `K_v`. Hence `γ` is regular elliptic over `K`.
Two matrices over `K` with the same separable characteristic polynomial are
conjugate over `K`: each is cyclic and conjugate to the companion matrix.
This supplies the passage from finitely many characteristic polynomials, or
closed geometric orbits, to finitely many rational conjugacy classes for `GL_n`.
Choosing one rational representative from each occurring class gives `R`.

For a compactly supported test function whose support satisfies the same local
regular ellipticity hypothesis, this proposition supplies the finiteness and
regular ellipticity needed on the geometric side. It asserts neither a trace
identity nor a twisted analogue.

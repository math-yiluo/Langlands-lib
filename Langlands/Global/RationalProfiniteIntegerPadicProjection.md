# Rational projections of residue scalars to a local field

This module extends the canonical integral projections in
`ProfiniteIntegerPadicProjection` to rationalized residue scalar algebras.
For a natural prime `p`, expressed by `[Fact p.Prime]`, it constructs the
\(\mathbb Q\)-algebra homomorphism

\[
\mathbb Q\otimes_{\mathbb Z}\widehat{\mathbb Z}
 \longrightarrow \mathbb Q_p,\qquad
q\otimes a\longmapsto q\,\operatorname{toPadic}_p(a).
\]

Here \(\widehat{\mathbb Z}\) means the existing `ProfiniteIntegerRing`,
the ring of compatible residues at all positive moduli. The second
factor on the right is mapped from \(\mathbb Z_p\) to \(\mathbb Q_p\)
by the canonical algebra map. All declarations lie in
`Langlands.Global`, with the namespaces specified below.

## Full scalar algebra

`ProfiniteIntegerRing.rationalToPadic p` has type
`(ℚ ⊗[ℤ] ProfiniteIntegerRing) →ₐ[ℚ] ℚ_[p]`.
The construction uses `Algebra.TensorProduct.lift` on the canonical
\(\mathbb Q\)-algebra map from \(\mathbb Q\) to \(\mathbb Q_p\) and
the composite ring map
\[
\widehat{\mathbb Z}\xrightarrow{\operatorname{toPadic}_p}
\mathbb Z_p\longrightarrow\mathbb Q_p,
\]
viewed as a \(\mathbb Z\)-algebra map. Their images commute because
\(\mathbb Q_p\) is commutative. Thus this definition requires neither
a product decomposition of the profinite integers nor a finite-adele
comparison.

`rationalToPadic_tmul` is the displayed pure-tensor formula, proved by
reflexivity. `rationalToPadic_one_tmul` says that \(1\otimes a\) maps
to the image of the integral projection. `rationalToPadic_tmul_one`
says that \(q\otimes1\) maps to the rational cast \(q\). These two
lemmas simplify the formula using preservation of one.

`rationalToPadic_unique` states that any \(\mathbb Q\)-algebra
homomorphism with the same formula for all \(q\) and \(a\) equals
`rationalToPadic p`. Its proof passes to the underlying
\(\mathbb Q\)-linear maps and applies tensor extensionality.

## Away scalar algebra

For an arbitrary excluded modulus `m : ℕ` and a witness
`h : Nat.Coprime p m`, the definition
`PrimeToProfiniteIntegerRing.rationalToPadic p m h` has type
`(ℚ ⊗[ℤ] PrimeToProfiniteIntegerRing m) →ₐ[ℚ] ℚ_[p]`.
The source's integral factor is the existing limit over positive
moduli coprime to \(m\). There is no assumption that \(m\) is prime.

The construction uses the same tensor lift with the existing away
projection `PrimeToProfiniteIntegerRing.toPadic p m h`.
The lemmas `rationalToPadic_tmul`, `rationalToPadic_one_tmul`,
`rationalToPadic_tmul_one`, and `rationalToPadic_unique` in this
namespace give the same normalization and uniqueness properties,
with the same proofs.

## Restriction compatibility

`PrimeToProfiniteIntegerRing.rationalToPadic_restrict` states, for
every \(x\in\mathbb Q\otimes_{\mathbb Z}\widehat{\mathbb Z}\),
\[
r_{p,m,h}\big((\mathrm{id}_{\mathbb Q}\otimes
 \operatorname{restrict}_m)(x)\big)=r_p(x).
\]
The tensor restriction is written directly as
`Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) (restrict m).toIntAlgHom`.
It is the rationalization of the published integral restriction;
no alternate restriction is defined. The proof uses tensor
induction. On pure tensors it reduces to the imported integral
identity `toPadic_restrict`; additivity handles sums.

## Provenance and scope

This is an internal construction from the published full and away
integral projections and Mathlib's algebra tensor universal property
in `RingTheory.TensorProduct.Maps`. The implemented proofs are
described above. No new result is attributed to external literature.

These are algebraic maps. The module introduces no rational topology
and makes no continuity, injectivity, or surjectivity claim. It does
not identify either tensor algebra with finite adeles or a restricted
product. Compatibility of these scalar projections with rational
Tate modules or twists is a separate construction.

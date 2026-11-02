# Punctual perfect complexes over a regular local ring

Authors: Worker 975 and Worker 1015.

`Langlands.CommutativeAlgebra.RegularLocalPunctualComplexStatement.{u}` is a
`Prop`-valued definition for an arbitrary universe `u`. This module states the
proposition and supplies no proof.

Let `(R, m, k)` be a regular local ring of Krull dimension `g`, and let `K` be
a bounded cochain complex of finite projective `R`-modules. The proposition
assumes, in this order:

1. `Hⁱ(K ⊗ k)` vanishes for every integer `i < 0` or `g < i`;
2. `H⁰(K ⊗ k)` has dimension one over `k`;
3. for each integer `i`, some power `m^N` annihilates `Hⁱ(K)`;
4. for every ideal `J` with `m² ≤ J` and `J ⋖ m`, the `R/J`-module
   `H⁰(K ⊗ R/J)` is not isomorphic to `R/J`.

The conclusion is that `Hⁱ(K)` vanishes for every `i ≠ g`, and that
`H^g(K)` is isomorphic to `k` as an `R`-module. The dimension `g` is any
natural number, including zero.

## Lean correspondence

The binders start with `R : Type u`, `[CommRing R]`,
`[IsRegularLocalRing R]`, and `g : ℕ`, followed by `ringKrullDim R = g`,
`K : CochainComplex (ModuleCat.{u} R) ℤ`, and `IsStrictlyPerfect K`.
The four assumptions above then precede the conjunction in the conclusion.
There are no other hypotheses.

`IsRegularLocalRing` is Mathlib's class extending `IsLocalRing` and
`IsNoetherianRing`; it equates the minimal number of generators of the maximal
ideal with `ringKrullDim R`. In the dimension equality, `g` is coerced to
`WithBot ℕ∞`. Integer degree comparisons and the final homology degree coerce
`g` to `ℤ`.

The Library module `Langlands.Cohomology.PerfectModuleComplex` supplies
`IsStrictlyPerfect` and `baseChange`. The former requires bounds on the
terms themselves and requires every term to be finite and projective.
The latter is ordinary degreewise extension of scalars:
`(ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)`.
Thus `K ⊗ k` denotes
`(baseChange (algebraMap R (ResidueField R))).obj K`, and `K ⊗ R/J`
denotes `(baseChange (Ideal.Quotient.mk J)).obj K`.

All other notions are Mathlib's. `HomologicalComplex.homology` is applied to
these actual cochain complexes, and `IsZero` expresses vanishing in the
appropriate module category. `Module.finrank` expresses the residue-field
dimension. The inclusion
`maximalIdeal R ^ N ≤ Module.annihilator R (K.homology i)` expresses
annihilation by the entire ideal power; `N` may depend on `i`.

`J ⋖ maximalIdeal R` is `CovBy`: `J < m` with no ideal strictly between.
Together with `m² ≤ J`, it makes `m/J` a one-dimensional `k`-vector space,
so `Spec(R/J)` is a first-order thickening of the closed point. This
description does not require a coefficient field in `R/J` or an isomorphism
with the ring of dual numbers over `k`.

`ModuleCat.of (R ⧸ J) (R ⧸ J)` is the free module of rank one over `R/J`.
`IsEmpty` asserts that its type of isomorphisms with `H⁰(K ⊗ R/J)` is empty.
The conclusion uses `Nonempty` for an isomorphism
`K.homology (g : ℤ) ≅ ModuleCat.of R (ResidueField R)`, with the residue
field viewed as an `R`-module through its canonical quotient map.
When `g = 0`, the regular local ring is a field and the premises imposed
on `J` in assumption 4 have no instances.

## Source and derived provenance

The source is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian
Varieties*, preliminary version of the first chapters, (9.6)–(9.9),
printed pp.128–130 (PDF pp.132–134), in the second proof of Theorem (9.1).
It is registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`;
the retained file is
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`,
SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
There is no project errata note for this source.

This proposition is derived content, rather than a verbatim proposition
in the source. It isolates the local algebra used there, including Lemma
(9.7), which the source takes from Matsumura (its reference MA V, p.127).

- The source's `A = O_{X^t,0}` is `R`, and its complex `K^•` of (9.6) is
  `K`. The source constructs a finite free complex in degrees `0, …, g`.
  Assumption 1 replaces that termwise length condition by the corresponding
  bound on residue homology of a strictly perfect complex.
- Assumption 2 corresponds to
  `H⁰(K^• ⊗ k) = H⁰(X, O_X) = k` in (9.8).
- Assumption 3 corresponds to the source's assertion before Lemma (9.7)
  that the homology modules are artinian. For finite modules over a
  Noetherian local ring, this is equivalent to annihilation by a power
  of the maximal ideal.
- Assumption 4 replaces the use in (9.8) of the universal property of the
  Poincaré bundle `P` together with functoriality of the base-change
  isomorphisms in `J`. In the geometric application,
  `H⁰(K ⊗ R/J)` computes sections of `P` on `X × Spec(R/J)`.
  Freeness of rank one permits a generator to lift the nonzero section
  on the closed fiber, trivializing `P` there. The universal property
  rules out this triviality on a nontrivial first-order thickening.
  The present statement takes the resulting module condition as a
  hypothesis and contains no geometric data.
- The conclusion corresponds to `Rⁿp_{2,*}P = 0` near the origin for
  `n ≠ g`, as used in (9.6) and Lemma (9.7), and
  `(R^g p_{2,*}P)_0 ≅ k`, obtained in (9.9) by comparison with a Koszul
  resolution and dualizing back.

The source also uses `H^g(K^• ⊗ k) = k` in (9.8). This statement does
not assume that equality. Its hypotheses are precisely those listed above;
the generalized local algebra assertion remains to be proved separately.

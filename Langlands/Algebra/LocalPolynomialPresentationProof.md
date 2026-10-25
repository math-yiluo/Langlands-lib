# Local polynomial presentation of an essentially finite type local algebra

`Langlands.Algebra.localPolynomialPresentation` proves exactly the published
`Langlands.Algebra.LocalPolynomialPresentationStatement`. Its complete,
unapplied type is

```lean
Langlands.Algebra.localPolynomialPresentation.{u, v} :
  Langlands.Algebra.LocalPolynomialPresentationStatement.{u, v}
```

Thus the two ring universes remain independent. The hypotheses and conclusions
are those of the published statement: for a local map of commutative local
rings \(R\to S\) with \(S\) essentially of finite type over \(R\), there are
\(n\), a prime \(\mathfrak q\) of `MvPolynomial (Fin n) R`, and a surjective
\(R\)-algebra map
\[
f:\operatorname{Localization.AtPrime}(\mathfrak q)\longrightarrow S
\]
such that both the canonical scalar map from \(R\) and \(f\) are local.

## Implemented proof

Let \(A\subseteq S\) be the finite type \(R\)-subalgebra supplied by
`Algebra.EssFiniteType.subalgebra`. The associated
`Algebra.EssFiniteType.submonoid` consists of those elements of \(A\) whose
images in \(S\) are units, and \(S\) is its localization.
`Algebra.FiniteType.iff_quotient_mvPolynomial''` supplies a surjection
\[
g:R[X_1,\ldots,X_n]\longrightarrow A.
\]
Compose \(g\) with the inclusion of \(A\) in \(S\), obtaining \(\varphi\).
Define \(\mathfrak q=\varphi^{-1}(\mathfrak m_S)\). Since the maximal ideal of
a local ring is prime, its inverse image is prime. Every element outside
\(\mathfrak q\) maps to a unit in \(S\); `IsLocalization.liftAlgHom` therefore
produces \(f\). The localization carries its canonical \(R\)-algebra structure
through the polynomial ring throughout this construction.

For surjectivity, `IsLocalization.surj` expresses each \(s\in S\) using
\(a,t\in A\), with \(t\) mapping to a unit and
\(s\,t=a\). Choose polynomial preimages \(a',t'\) under \(g\). Then
\(t'\notin\mathfrak q\), and these two preimages satisfy precisely
`IsLocalization.lift_surjective_iff`. This proves that \(f\) is surjective.
The composite of the canonical map \(R\to\operatorname{Localization.AtPrime}
(\mathfrak q)\) with \(f\) is the given local scalar map \(R\to S\), by
`AlgHom.comp_algebraMap`. Hence `isLocalHom_of_comp` proves locality of
the canonical map from \(R\). Finally `IsLocalHom.of_surjective` proves
locality of \(f\), using that its source is local.

There is no assertion that the kernel of \(f\) is finitely generated. No
Noetherian, flatness, finite presentation, or injectivity hypothesis is added.
All auxiliary constructions are internal to this proof.

## Verification

The proof module passed a Lake build and complete unapplied declaration
inspection in the assigned Lean 4.34.0 environment with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The inspected theorem has exactly
the universe parameters `u` and `v`, and its only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Exact-target validation against the
unchanged published proposition, independent semantic review, and Library
publication are recorded separately by the project's contribution workflow.

## Provenance and scope

This is a derived proof of the intermediate polynomial presentation at the
start of the proof of Stacks Lemma 10.128.9 (tag 05UV). The registered original
is `stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
retained file `05UV.html`, displayed hypothesis (2) and the opening proof
paragraph.

The original opening sentence says “essentially of finite presentation”,
whereas displayed hypothesis (2) is “essentially of finite type”.
The implemented proof uses only the displayed finite-type hypothesis and
establishes the same polynomial-localization quotient presentation directly
through the finite type subalgebra and localization fractions. It does not
use or establish the later kernel-finiteness or flatness steps of 05UV.

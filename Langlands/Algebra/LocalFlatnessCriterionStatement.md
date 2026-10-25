# The Noetherian local flatness criterion

`Langlands.Algebra.LocalFlatnessCriterionStatement` states the local
criterion for flatness of Stacks Project Lemma 10.99.7, tag
[00MK](https://stacks.math.columbia.edu/tag/00MK), in tensor-kernel form.
This module defines a proposition; it does not prove the criterion.

Let \(R\to S\) be a local homomorphism of commutative Noetherian local
rings, and let \(M\) be a finite \(S\)-module. Write
\(\mathfrak m\) for the maximal ideal of \(R\). If the canonical map
\[
\mathfrak m\otimes_R M\longrightarrow R\otimes_R M
\]
is injective, then \(M\) is flat over \(R\).

In Lean, `IsLocalHom (algebraMap R S)` specifies the local homomorphism.
The compatible `Module R M` and `Module S M` structures, with
`IsScalarTower R S M`, express restriction of scalars along this map.
`Module.Finite S M` is finiteness over \(S\); finiteness over \(R\) is
not assumed. The types \(R\), \(S\), and \(M\) have three independent
universes `u`, `v`, and `w`. There is no nonzero-module, finite-type,
finite-presentation, or field hypothesis.

The source uses \(\operatorname{Tor}_1^R(\kappa,M)=0\), where
\(\kappa=R/\mathfrak m\). The long exact Tor sequence for
\(0\to\mathfrak m\to R\to\kappa\to0\), using that \(R\) is free over
itself, identifies this vanishing with injectivity of
\(\mathfrak m\otimes_R M\to R\otimes_R M\).
Stacks Remark 10.75.9, tag
[00M6](https://stacks.math.columbia.edu/tag/00M6), gives the kernel
description with the Tor arguments in the opposite order; symmetry of
Tor over a commutative ring gives the order used in 00MK.
The tensor unit isomorphism \(R\otimes_R M\simeq M\) identifies our
map with the source's \(\mathfrak m\otimes_R M\to M\).
`LinearMap.rTensor M (IsLocalRing.maximalIdeal R).subtype` tensors the
maximal-ideal inclusion with the identity of \(M\), so it is exactly
the displayed map. This source correspondence explains the formulation;
the module contains no formal Tor comparison theorem or abstract Tor
assumption.

The main registered original is
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `00MK.html`, Lemma 10.99.7, statement and proof.
The kernel comparison is registered as
`stacks-tor-tensor-kernel-00m6-2026-10-25`, content SHA256
`be19720d07b77c0aceb928935560856893fee7afb6dc2c33f7d5ba2cd2ee287e`,
Remark 10.75.9, displayed identity. The tensor formulation is an internal
presentation of these source statements, with the translation explained
above.

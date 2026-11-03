# The unipotent envelope in Chevalley's Borel intersection

`Langlands.GroupScheme.ChevalleyUnipotentEnvelopeStatement.{u}` is a
proposition target, not a proof.

Let `k : Type u` be an algebraically closed field and `G` a smooth connected
affine group scheme over `Spec k`. Let `t : T ⟶ G` be a maximal torus.
Suppose `i : U ⟶ G` is a smooth connected unipotent closed subgroup and
lies in every Borel subgroup of `G` that contains `T`. Then there is a smooth
connected normal unipotent closed subgroup `n : N ⟶ G` containing `U`.
Both containment premises and the final containment mean inclusion of range
subgroup functors on every test scheme. Normality also uses the existing
all-test-scheme definition. No reductivity assumption is imposed on `G`.

This is a derived consequence of J. S. Milne, *Algebraic Groups* (2017),
Theorem 17.56, printed p.371 (PDF page 387, zero-based page 386), together
with the usual properties of the unipotent radical. The theorem identifies
the reduced identity component of the intersection of the Borels through `T`
with the product of the unipotent radical of `G` and `T`. Since `U` is
smooth, reduced, and connected, its inclusion in the intersection factors
through that reduced identity component. The projection to `T` is trivial
on a unipotent group, so `U` is contained in the unipotent radical of `G`.
That radical supplies the `N` in this formulation. Milne's proof appears
in Section 17.h, printed pp.373–375 (zero-based PDF pages 388–390); it uses
the Kostant–Rosenlicht theorem and invariant affine open sets in the flag
variety. The deduction in Corollary 17.57 on p.371 uses this same
unipotent-to-torus step.

The target avoids choosing a canonical unipotent-radical construction:
it asks for an actual closed group-scheme inclusion with all its properties.
It does not assert that `U` itself is normal in `G`; a subgroup of the
unipotent radical need not be normal in `G`. The smoothness, connectedness
and affineness assumptions put `G` in the finite-type setting of the source:
an affine morphism is quasi-compact, and a smooth morphism is locally of
finite presentation. The same applies to the closed smooth subgroup `U`.

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read; it has no correction
to Theorem 17.56 or Corollary 17.57. This module supplies a broader
structural prerequisite target for the unrestricted dynamic-centralizer
reductivity task. It proves neither this target nor connected reductivity.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

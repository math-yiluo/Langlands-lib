# Existence of the anti-affine affinization quotient

`Langlands.GroupScheme.AntiAffineQuotientExistenceStatement.{u}` asserts that
every smooth connected group scheme `G` over an arbitrary field `k : Type u`
admits `AntiAffineQuotient G`. No affineness, quasi-compactness or finite-type
premise is imposed on `G`.

The witness supplies an actual smooth connected affine group `Q` and a group
homomorphism `q : G → Q`. The projection is smooth, surjective and
quasi-compact. Its actual scheme-theoretic kernel is smooth, connected and
anti-affine. The `IsAffinization q` field asserts that the specified map induces
an isomorphism on global sections. The existing `IsAffinization.targetIso`
and `comp_targetIso` identify `Q` with `Spec Γ(G, O)` and identify `q` with the
canonical scheme affinization morphism.

The source is SGA 3, Exposé VI_B, Theorem 12.2 and Lemma 12.3, printed
pp.430–431 / PDF pp.100–101, Gille–Polo recomposed edition of 13 October 2024,
registered as `sga3-expose-vib-gille-polo-2024`. The official Tome I errata of
the same date do not change these results. The theorem gives the canonical
affine quotient of an algebraic group and its smooth connected anti-affine
kernel. For the smooth connected specialization here, the kernel geometry
makes the faithfully flat quotient smooth, and smoothness and connectedness
descend to its target. Quasi-compactness follows from finite type. The Library's
`Langlands.GroupScheme.quasiCompact_of_smooth_connected` supplies
quasi-compactness of `G` without an extra premise; smoothness supplies local
finite type, and field group schemes are separated. Thus this scope is the
smooth connected algebraic specialization of the cited result.

This module states existence as a proposition definition. It does not prove
existence or preservation under field extension, and it does not prove
`SmoothAlgebraicallyClosedUnipotentRadicalExtensionStatement`.

# Tangent images for Cartan dimension induction

This is a derived interface for the dimension-induction argument in
Milne, *Algebraic Groups* (2017), Theorem 17.91, printed p.381 / PDF p.397.
It applies to any actual subgroup functor `F` of an affine group `G`
represented by `j : C ⟶ G`, with `C` smooth and affine over a field
`k : Type u`. It does not assume that `F` is a Lie-element centralizer.

`PreservesMaximalTori j` is the proposition that every maximal torus of
the source remains maximal after composition with `j`. This reusable
predicate has no smoothness or closedness assumptions of its own.
The tangent-containment lemma below uses it for `C⁰ ⟶ G`.

`SubgroupFunctor.IsRepresentedBy.lie_eq_range_identityComponent` identifies
`F.lie A` with the range of the actual differential of
`identityComponentι C ≫ j`, over every commutative `k`-algebra `A`.
The proof combines the represented tangent-range comparison with the
published fact that passing to the identity component preserves this
range. The latter uses the smoothness of the open inclusion `C⁰ ⟶ C`
to lift actual dual-number identity points.

`Lie.dimension_identityComponent_lt_of_lie_ne_top` assumes additionally
that `G` is smooth and connected, `j` is closed, and `F.lie k ≠ ⊤`.
It concludes that `C⁰` has strictly smaller actual Lie dimension than
`G`. The composite inclusion is closed. If it were an isomorphism its
differential would be surjective, contradicting the proper tangent image.
The published dimension comparison then gives the strict inequality.
There is no positive-dimension hypothesis.

`IsGeneratedByCartanSubgroups.lie_le_of_maximalTori` assumes inductive
Cartan generation for `C⁰` and that every maximal torus of `C⁰` remains
maximal in `G`. If any closed competitor `H ⟶ G` contains all Cartans
of `G`, its tangent submodule contains `F.lie k`. The proof first applies
the published Cartan intersection argument to `C⁰ ⟶ G`, then takes
tangent submodules and uses the first comparison. The competitor is
arbitrary: it need not be smooth, reduced or connected.

The provenance is internal and derived from the published actual
identity-component, represented-subgroup, tangent-image, dimension and
Cartan-intersection constructions. Milne's Theorem 17.91 motivates their
combination; the file is not a literal additional statement of that
theorem. For a semisimple Lie-element centralizer, smoothness and
preservation of maximal tori must still be supplied, as must the tangent
spanning and final generation arguments. This file proves none of
those structural inputs and does not prove Cartan generation.

The registered original is `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete registered errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` contains no correction
to Theorem 17.91.

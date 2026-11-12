# A unitary finite-length highest-derivative irreducibility criterion

Author: Worker 105.

`Langlands.Classification.BernsteinUnitaryFiniteLengthIrreducibilityCriterion F T`
is a sufficient criterion for irreducibility. It is a proposition definition;
no irreducibility theorem is proved in this file.

The source is J. N. Bernstein, *P-invariant distributions on GL(N) and the
classification of unitary representations of GL(N)*, LNM 1041 (1984),
registered as `bernstein-1984-p-invariant`, Proposition 8.1(a), printed
pages 87–88 (PDF pages 38–39), and the criterion of section 8.2, printed
page 88 (PDF page 39).

The Lean statement assumes an actual finite-length unitarizable smooth
representation `A` of positive-rank `GL_N`, an actual highest positive
derivative order `hd`, positivity of every lower shifted derivative, and
irreducibility and unitarizability of the actual shifted derivative at `hd`.
It concludes that `A` is irreducible.

This is a derived sufficient specialization of the source, with the following
changes made explicit. Proposition 8.1(a) assumes equality with the Hermitian
dual in the Grothendieck group; here actual unitarizability of `A` supplies the
required self-duality for finite-length admissible representations.
The source requires positivity at positive derivative orders below the
highest order. The Lean hypothesis includes order zero, which is a stronger
hypothesis and agrees with the condition used for products in section 8.2.
The highest shifted derivative is required to be both irreducible and
unitarizable, as in Proposition 8.1(a). Unitarizability of `A` is already an
input, so the conclusion records just irreducibility.

A possible proof uses the source's Hermitian-dual argument. Alternatively,
semisimplicity of an admissible unitary representation permits a proof by
actual irreducible subquotients: lower positivity excludes any constituent
whose highest derivative order is smaller, and exactness plus irreducibility
of the highest derivative excludes multiple surviving constituents. This
paragraph describes proof obligations, not results supplied by this file.

All finite-length, scalar-exponent, positivity, highest-order, irreducibility
and unitarizability conditions are the Library's actual representation
conditions. No Grothendieck-class equality, scalar character, or abstract
nonvanishing certificate replaces the actual conclusion. The independent
field and carrier universe parameters and arbitrary supplied topology match
the intended Bernstein unitary-product application.

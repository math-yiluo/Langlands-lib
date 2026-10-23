# Additivity of the relative Lie differential

For any scheme \(S\), commutative group schemes \(G,H\) over \(S\), and actual
group-scheme homomorphisms \(f,g:G\to H\), the intended statement is
\[
  d(f+g)_e = df_e + dg_e :
  \operatorname{Lie}(G/S)\longrightarrow\operatorname{Lie}(H/S).
\]

`Langlands.CommGroupScheme.LieAdditivityStatement S` quantifies over all
these objects and morphisms and asserts this equality. Addition on the left
is the existing pointwise group law on homomorphisms; addition on the right
is addition of morphisms of \(\mathcal O_S\)-modules. The differential is the
actual `lieMap` obtained by dualizing the induced cotangent map. Neither the
differential nor additivity is supplied as an input.

The target requires no smoothness, finite presentation, affineness, or
relative-dimension hypothesis. It concerns commutative group schemes, so
that their Hom sets have the published additive commutative group
structure. Abelian-scheme homomorphisms are a specialization through the
existing bundle.

## Provenance

This is a derived statement, based on Conrad--Gabber--Prasad,
*Pseudo-reductive Groups*, second edition (2015), Section 2.1, printed
page 52 (PDF page 78), and Appendix A.7, printed pages 529--532 (PDF
pages 555--558). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`,
SHA256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

Section 2.1 describes tangent vectors as the dual of the cotangent module
at the identity. Appendix A.7 identifies such tangent vectors with
points over dual numbers reducing to the identity. Lemma A.7.2 expresses
their right translations on the structure sheaf using a derivation and a
square-zero parameter. Multiplying two such translations adds their
derivations, because the term containing the square of the parameter
vanishes; the same calculation is used in the opening of printed page 532.
Applying this to the pointwise sum of \(f\) and \(g\) gives the displayed
additivity equation on tangent vectors.

The passage to the sheaf on an arbitrary base is local on that base.
The published Lie object uses the internal dual of the identity pullback
of relative differentials; a proof following the cited dual-number route
must establish the comparison with that specific construction and its
specific `lieMap`. Alternatively, it may calculate the differential of
the group law using relative differentials. The source discussion
explains the mathematical derivation; this statement file proves neither
route nor the required comparison.

## Consequences and scope

An accepted proof supplies the missing geometric input for an additive
Lie functor. Together with its identity and composition laws, this yields
a ring map from the actual endomorphism ring of an abelian scheme to the
endomorphism ring of its Lie module. Over a base equipped with a morphism
to the spectrum of a rational algebra, the existing rationalization lift
then extends the action to rational endomorphisms.

These actions are subsequent constructions. The present file only
defines the proposition. In particular, additivity of the generic
module-sheaf operation `dualMap` does not itself prove this target:
one must relate the differential of the pointwise group-law sum of
scheme homomorphisms to the sum of their differentials.

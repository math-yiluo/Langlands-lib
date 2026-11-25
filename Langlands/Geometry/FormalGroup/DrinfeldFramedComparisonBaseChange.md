# Actual original framed comparisons under Nilp-base extension

This module constructs `DrinfeldFramedAtlas.Comparison.baseChange`:
the specified original framed comparison between the actual base-extended
representatives. Its target comparison is exactly supplied coefficient
extension of the original formal target comparison along the Nilp scalar map.
Its residue equality is forced by composing the original stored equality with
the actual reduced scalar map. No new frame automorphism is chosen.

`framingSquare_baseChange` proves the original framing certificate on every
new quotient test and every invertible finer reduced-comparison chart. The
actual old reduced finer chart and its unit evidence are constructed from
that new chart. The two previously proved further-refinement framing squares
supply the framing corrections. The exact target-comparison square supplies
the same correction maps. Scalar transport of the given original comparison
square supplies the original equation, and the proved fixed-frame residue
naturality square identifies the two frame routes.

The generic `QuasiIsogeny.framing_transport` reassociates those five actual
map equations and cancels the invertible target correction on the right using
its actual rational inverse. It proves equality of the complete rational
quasi-isogenies. Scalar transport preserves composition and integral
rationalization in the original-square step. No equality of point evaluations,
extra framing certificate or new comparison-compatibility hypothesis is used.

The construction retains all local-field, finite-dimensional central-division,
embedded-field, coefficient/residue and height-certified fixed-frame
hypotheses, with Nilp universes `{v,u}`. Each actual base-extended representative
already carries its proved local kernel-rank height-zero framing certificate.
Covers may be infinite and scalar maps may merge generators. The large
dependent framing proof has a finite local elaboration bound. Comparison-class
functoriality, action laws and representability are outside this module;
`DrinfeldFramedClassFunctor` constructs the comparison-class functor, and action
laws and representability remain separate.

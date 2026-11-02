# Comparing etale presentations through a represented kernel pair

These internal derived helpers specialize the common etale presentation
comparison to two presentations with the same represented kernel pair.
They apply over an arbitrary scheme and on its full scheme slice.

`commonEtaleKernelPairIso` takes two etale sheaves, a locally surjective
presentation of each by the same scheme `U`, and the same represented
kernel-pair square for both presentation maps. It returns actual
presheaf-isomorphism data, including an inverse and both inverse laws.
`commonEtaleKernelPairIso_hom_fac` proves that its forward map identifies
the two presentation maps.

The implementation first applies
`same_kernel_of_common_represented_kernelPair` to obtain the sectionwise
common-kernel condition on every test scheme. It then applies the
existing `commonEtalePresentationIso` and its compatibility theorem.
The effective-epimorphism comparison proof is reused through those
declarations.

`isSheaf_fppf_of_common_etale_kernelPair` assumes the second codomain is
an actual fppf sheaf and concludes that the first presheaf is an fppf
sheaf. It applies the existing common-presentation transport lemma to
the same sectionwise kernel condition.

The fppf sheaf, both etale-local presentations and both represented
kernel-pair squares are inputs. No quotient is constructed here, and
these results alone do not establish fppf descent for an arbitrary etale
sheaf. The provenance is the imported internal common-presentation
comparison and the pointwise represented-kernel-pair lemma.

# Small actual recognition fibre-product quotients

The full affinoid algebra of a compatible chart pair does not depend on the
chosen common base chart, up to a constructed bounded algebra equivalence.
`commonBaseAlgebraEquiv` constructs both maps using the actual closed-quotient
pushout universal properties. Coherence of the original compatible maps
transfers each pushout equation between common base charts. Bounded pushout
uniqueness proves both inverse identities on entire algebras. This does not
infer algebra equality from ordinary spectrum points.

If the first bounded map is finite Banach over any supplied common base, the
finite Banach pushout statement makes the corresponding pushout spectrum
small whenever the second factor spectrum is small. The comparison's actual
spectrum homeomorphism transfers this to the pair algebra built over its
chosen base chart. The universe of this smallness is the ambient space
universe, independently of the coefficient field universe.

`small_fibreProductSpace_of_pointedFiniteEtalePairs` applies this to every
point of the actual gluing quotient. The projections give compatible ambient
points, and the pointed finite-pair interface gives two original factor chart
indices containing their projections, with a finite first bounded map over a
supplied common base. The proved `mem_range_chart_iff` shows that the given
quotient point itself belongs to this pair chart. The second chart spectrum
is small by its embedding into the original space. Thus small pair spectra,
indexed by a subset of the original small pair index type, surject onto the
whole original quotient. This proves the quotient is small. No injectivity of
the ordinary point-pair map is assumed or proved. The etale part of the
pointed interface is not needed for this size argument.

`recognition_fibreProductSpace_small` combines this with unconditional pointed
finite chart-pair coverage of the canonical recognition-selected cospan from
the original `strongEtale` input. It retains the explicit
`FiniteBanachPushoutStatement K` premise. Every source, target and index of
the cospan has the original space universe. No Hausdorff condition on the
global spaces is imposed.

These are internal deductions from actual coherent chart systems, bounded
pushout universality, finite Banach base change and the recognition-selected
cospan interface. No external theorem is transcribed. This is a size result
for the actual quotient, not a construction or proof of its full localized
pullback universal property or its etale second projection.

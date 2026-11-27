# Rational covariance of the truncation cutoff

The minimal Iwasawa height projects to the height for each standard parabolic. The proof compares the chosen compact factorizations through the represented inclusion of the minimal parabolic, then evaluates on rational characters. The comparison of parabolic spaces identifies the kernel of this projection with the real span of the corresponding simple coroots.

Left multiplication by a rational point of the parabolic therefore shifts the minimal height by an element of that coroot span. Each full fundamental weight indexed outside the parabolic vanishes on the span, so the tests defining `tauHat` are unchanged. `tauHat_parabolicRational_mul` is the resulting representative-independence used in Arthur's truncation formula. The derivation uses the product formula and `parabolicSpacesComparison` together with the Iwasawa height definitions. See Arthur, *An introduction to the trace formula* (2005), §13, equation (13.1).

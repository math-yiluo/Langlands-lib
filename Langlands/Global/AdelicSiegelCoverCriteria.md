# Forward coverage and uniform weak thresholds for actual Siegel products

Author: Worker 1377.

This internal adapter constructs the positive `uniformCharacterThreshold`
and proves criteria for the existing `IsSiegelCover`.
All fields, group schemes, actual point groups and root sets retain the
arbitrary universe `u`. Its inputs still include the algebraic setup and
actual rational coverage; it supplies neither existence theorem.

For a finite set `Δ` of actual characters and arbitrary positive indexed
thresholds `b χ : ℝ≥0ˣ`, the image `b '' Δ` is finite and therefore has a
lower bound in the linearly ordered group of positive nonnegative-real
units. `uniformCharacterThreshold Δ b hΔ` chooses such a lower bound,
and `uniformCharacterThreshold_le` proves it lies below every `b χ`
with `χ ∈ Δ`. This construction works for any index type, so it imposes
no further algebraic hypotheses on the characters.
This lower bound is itself positive. It gives a common threshold
`t` such that the indexed weak character chamber is contained in the
uniform weak chamber. The existing strict-to-weak inclusion gives the
same conclusion for the indexed strict chamber. The finite-set lower
bound theorem includes the empty set, so no positive-rank or nonempty-root
assumption appears. Every inequality uses the unchanged normalized
`normCharacter`; there is no replacement by unnormalized coordinates.

`normOne_subset_rational_mul_iff` establishes the precise left-action
convention. An expression `g = q s` with a principal rational point `q`
and `s ∈ S` gives `q⁻¹ g ∈ S`. Conversely `q g ∈ S` expresses `g` as the
product of the principal point `q⁻¹` and that member of `S`. Rational
inversion and the actual principal-point homomorphism implement both
directions. This lemma works for every subset `S` of the actual adelic
point group and requires no affine, reductive or finite-type hypotheses.
It does not convert a right-action reduction statement.

For an actual `IsSiegelAlgebraicSetup`, the companion
`AdelicSiegelNormOne` proves that the rational left saturation of every
canonical weak Siegel product is contained in the actual norm-one group.
Consequently `isSiegelCover_iff_forward` reduces the equality in the cover
predicate to its other inclusion while retaining the exact
`IsParabolicIwasawaCompact` condition. `isSiegelCover_iff_translate`
expresses that remaining inclusion as the individual rational-left-
translate criterion just proved.

Finally `exists_isSiegelCover_of_strictCover` starts with the actual
setup, the required Iwasawa condition on its chosen compact subgroup, and
forward rational coverage by the canonical ordered strict Siegel product
with indexed positive thresholds. Splitness of the setup's maximal split
torus and the ambient affine locally finite type interfaces give finiteness
of the actual simple roots through the published
`IsSplitTorus.finite_simpleRelativeRoots`. The common-threshold argument
enlarges the strict torus chamber to a uniform weak chamber. Monotonicity
of the existing `productSet` and rational left multiplication transfers
coverage. The containment theorem then gives the equality required by
`IsSiegelCover`.

The compact unipotent set, compact norm-one Levi set, compact subgroup,
actual canonical inclusions, restriction map `j`, ordered factors and
normalized character norms are identical in the input and output.
In particular, any separately proved positive-torus compatibility for
that compact subgroup can be retained; compatibility is not asserted here.

The provenance is internal: finite lower bounds in Mathlib,
`RelativeRootChamber`, `AdelicSiegelFactors`, `AdelicSiegelNormOne`,
`AdelicSiegelReductionStatement` and `RootSupportFiniteness` supply the
interfaces used. The result addresses only uniformity of thresholds and
strict-to-weak enlargement once the actual forward coverage has been
proved. It does not identify general-parabolic chambers, compare roots
with those of a minimal parabolic, convert arbitrary reference Levi
points to torus points, establish rational reduction, or prove
`AdelicGoodSiegelReductionStatement`.

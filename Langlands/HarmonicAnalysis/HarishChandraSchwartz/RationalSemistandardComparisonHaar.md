# The split-central quotient Haar scale in semistandard Weyl comparison

Waldspurger (2003), I.1, printed pp. 238–240, fixes Levi and split-center
Haar measures by their compact traces. `SourceMeasure.IntrinsicQuotientNormalization`
specifies the corresponding mass-one scale on the quotient by the
actual split center. The trace is taken in the same compact group as
the comparison, restricted by the actual Levi inclusion.

`SourceMeasure.comparisonCenter_map` uses maximal split-center
independence in the two models of that literal Levi. The quotient
homeomorphism from the dynamic Levi used in V.3 to the intrinsic Levi
then preserves the Haar by uniqueness at the specified trace scale.
The comparison's `HasIntrinsicSourceNormalization` supplies the
dynamic scale, and `IntrinsicQuotientNormalization` supplies the scale of
the measure used in synthesis and the form.

For the Weyl arrow, the inverse of the actual Levi conjugation transports
the split-center images and the compact traces. The lift lies in the
common compact, so it conjugates this compact to itself. Uniqueness at
mass one gives `SourceMeasure.weylQuotientHaar_map`.

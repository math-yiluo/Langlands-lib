# Ordered support of a polar part

This internal auxiliary module implements the support part of the correspondence
in Lemma `lem:BKlabels` of the operator’s numerical local Langlands route note
(`operator-numerical-llc-route-2026-11-16`). `PositiveLevels` records the
descending positive support, including the prescribed top level, and the gcd
condition from the route note’s Definition 3.1.

The equivalence `polarPartsEquiv` lists the positive support in descending order
and appends the constant coefficient. Its inverse puts these coefficients back
at the recorded indices and fills all other indices with zero. Adjoining zero
does not change the generated field. The indexed gcd agrees with the gcd of the
support finset. At level zero, `zeroPolarPartsEquiv` identifies the polar parts
with generating nonzero one-tuples for the parameter `a = 1`.

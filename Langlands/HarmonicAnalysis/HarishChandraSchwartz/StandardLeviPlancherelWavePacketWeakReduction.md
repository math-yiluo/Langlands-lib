# Proper-parabolic inputs for the source-normalized packet estimates

`StandardLeviPacketWeakConstantTermInputs` uses an auxiliary compact-open
subgroup `L` with minimal-parabolic Iwasawa factorization and the corresponding
literal factorization on every standard Levi. For each proper standard
parabolic and compatible split component, it asks for the per-section
constant-term threshold, the per-section positive exponential decay, and the
fixed-level weighted weak-packet bound with its integrability clause. The weak
bound uses the original standard-Levi Plancherel weight and the original orbit
measure induced by the source-normalized character Haar measure. The compact
used for continuation remains the original `Ks`.

`standardLeviPacketDerivativeEstimates_of_weakConstantTerms` combines these
inputs with a simultaneous standard basis, a finite ambient Cartan cover and
finite Cartan covers of every standard Levi at `L`, and a positive-definite
seminorm on the real cocharacter space. From the simultaneous basis it obtains
a compatible split component and the required basis-member properties for
each proper parabolic. The standard cocharacter theorem supplies the
cocharacter. The compact-fiber uniformization lemmas then give one threshold
and positive decay rate at each level. The spherical and matrix-height
comparisons convert the positive bound to all-real rapid decay, and the weak
and positive integral assembly yields the proper-region estimates at `L`.
The continuity of the weight on the compact finite-measure orbit and the
published weighted-coefficient integrability supply the integrability inputs.

The compact-change theorem carries these proper-region estimates to the
original packet compact `K`. The central estimate and the chamber and Cartan
assemblies then give the finite derivative estimates for the original packet
on the whole group. Those are the input to the published synthesis theorem
for Schwartz membership and continuity. This is a derived analytic reduction
along Waldspurger VI.3.1 with the three proper-parabolic inputs explicit.

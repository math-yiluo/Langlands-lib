# Unitary normalized Jacquet exponents and vanishing

Author: Worker 17.

The set `unitaryJacquetExponents` consists of the actual normalized Jacquet
exponents with zero normalized real part. It uses the same split component,
normalized Jacquet module and `q^(-s)` real-part convention as the published
`unitaryJacquetPart`. This is an internal extraction of the indexing set in
that construction, motivated by Renard 2026, VII.2.3–VII.2.4 (printed
pp.229–230 / PDF pp.235–236).

The set is a subset of `normalizedJacquetExponents`. Reindexing the
supremum defining `unitaryJacquetPart` gives precisely the supremum of
weight spaces over this set. Each actual exponent has nonzero weight
space, so if the unitary part vanishes then no exponent with zero real
part can occur. Conversely, if every actual exponent has nonzero real
part, every index in the defining supremum for the unitary part is
impossible and the supremum is bottom. Consequently, the unitary
exponent set is empty exactly when the unitary part vanishes, and is
nonempty exactly when the unitary part is nonzero.

The proof uses only the published part and exponent definitions and the
complete lattice of subrepresentations. It imposes no admissibility,
temperedness, finite-length or irreducibility condition. The actual
parabolic, Levi, matching radical and split-component data, arbitrary
field and carrier universes, canonical rational-point topology,
local compactness and nonarchimedean hypotheses are retained.
This algebraic criterion does not prove the square-integrability
criterion or any of the three exact parent statements.

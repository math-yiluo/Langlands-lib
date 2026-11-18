# Actual component valuations and a strict point for positive decay

This derived supporting module packages the actual `rationalComponentH0` as a
homomorphism and compares its evaluation by every integral character with the
positive normalized character order on the specified torus image. The comparison
uses the actual minimal Levi scheme, its published point equivalence, and the
published restriction formula for `centralizerValuation`.

On the common uniformizer section, the value of a character is the integer
pairing with the pushed-forward cocharacter. Hence a standard cocharacter, lifted
integrally through the specified compatible split component, gives an actual
point of its uniformizer subgroup on whose `H₀` every root in `J` vanishes and
every simple root outside `J` is strictly positive. The conclusion includes the
improper parabolic, for which the outside-root condition is empty.

This is internal infrastructure for the shift in Waldspurger's Lemma VI.2.3,
printed pp.300–301 of *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), source `waldspurger-2003-plancherel`. The proof
composes the published actual torus-factor comparison, normalized valuation
restriction, intrinsic common-uniformizer evaluation, and integral standard
cocharacter lift. It assumes no coefficient estimate or exponent decomposition
and does not prove the principal positive-decay target.

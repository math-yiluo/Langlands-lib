# Finite-normalization charts from Zariski’s Main Theorem

This internal draft combines the closed-fibre polynomial chart with Mathlib’s
algebraic Zariski Main Theorem. At each maximal ideal of a characteristic-zero
finite type integer domain, it obtains a polynomial subbase P and a subalgebra
C finite as a P-module. An element r of C outside that maximal ideal induces
an isomorphism C[1/r] → A[1/r]. The finite normal subbase theorem proves finite
normalization of C, since P is a noetherian normal domain of finite type over
the integers. Faithfulness of P’s action on C follows by its inclusion into A
and the injectivity of the polynomial chart.

The theorem records this finite-normalization chart. It does not yet transfer
finiteness to A after localization or patch the resulting local modules.
Those steps will use the independently developed normalization-localization
and local-to-global helpers.

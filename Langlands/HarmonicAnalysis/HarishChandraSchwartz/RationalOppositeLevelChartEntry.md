# Entry of opposite-radical modulus levels into the identity neighborhood

`exists_oppositeLevel_chart_entry` localizes each level for the volume
estimate of Waldspurger II.4.1. Let `a` be the value of the standard cocharacter at the chosen
uniformizer, and let `L` express the actual minimal Iwasawa weight as
`q^(-L/2)` on the opposite radical. Given an identity neighborhood `W`, the
lemma constructs one `j : ℕ` such that `a^(-(n+j)) x a^(n+j)` is in `W`
for every `n : ℕ` and every point `x` of level `n`.

The Lean proof chooses a closed positive-dimensional matrix representation.
The inverse-weight power estimate bounds the inverse weight of
`a^(-n) x a^n` by `2 C`, because `|π|^(n/2) q^(n/2) = 1`. Taking
logs and applying the lower height comparison puts these conjugates in a
fixed height sublevel. The sublevel intersected with the closed opposite
radical is compact. Uniform cocharacter contraction on this compact set
provides the additional powers. The level function from the height
comparison agrees with the supplied one by strict monotonicity of the
exponential with base `q > 1`.

This derived localization uses the power estimate corresponding to
II.4.1 (1), printed pp. 259–260, and the lower logarithmic height comparison
of II.3.4, printed pp. 256–257.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), registered as `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

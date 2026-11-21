# VI.3.2 factorization from actual one-orbit transport

Waldspurger (2003), VI.3.2, printed p. 306, identifies the weighted
synthesis of a smooth family with the weighted synthesis of its
average. `factorization_of_transport` supplies this raw function
equality for the actual average and the actual source integrals
under the displayed transport hypotheses.

`componentPacketEvaluation` is the evaluation of the actual component
packet at a fixed ambient point, as a linear functional on sections.
At each source index, apply the one-orbit packet comparison to each
inverse smooth comparison in the average. This gives the packet value
at the actual target of each Weyl-parabolic pair. The uniform
transporter multiplicity changes that double average into the
arithmetic mean over the source association class. The source
coefficient is constant on the class by the common-Levi and Weyl
comparisons. Taking class means therefore preserves the weighted sum
on the input's finite support.

The scalar, coefficient and source-constant comparisons remain exact
premises. The source character and orbit measure comparisons already
enter through the one-orbit theorem. The raw equality gives the typed
factorization through `schwartzSynthesis_factorization` with its
independent invariant-image and Schwartz-membership witnesses.

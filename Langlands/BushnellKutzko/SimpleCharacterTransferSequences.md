# Defining sequences at changed stratum indices

The source is Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`, (2.4.1)–(2.4.2) on printed pp. 65–66 (PDF pp. 77–78). The transfer induction uses defining sequences with a prescribed first element and, when working at a different simple stratum index, the same approximation tail.

Lowering the index of the initial stratum and the first term preserves simplicity. Their order and element agree, so the new first term is equivalent to the lowered initial stratum. Later indices, elements and derived-stratum conditions are preserved. `DefiningSequenceChoice.lowerIndex_tail` records the unchanged tail.

An exact defining sequence of a critical approximation can be prepended with the initial simple stratum. The critical exponent supplies the new second index, the critical congruence supplies the first transition, and the simple derived stratum supplies the first derived condition. Building exact sequences repeats this step on the same chain. At each nonterminal step, pure-stratum approximation supplies a simple stratum at the strictly larger critical index, and the published critical derived-stratum theorem supplies the additional condition. The positive difference between the initial level and the stratum index decreases. The scalar or minimal terminal case uses the single given stratum.

The stopping criterion also forces every defining sequence to have an empty tail. A second term would have stratum index equal to the initial level in the finite terminal case, contradicting its stratum inequality. In the scalar case the first transition would require the critical exponent to be finite.

`terminalDefiningSequence` is the singleton sequence at a simple stratum with critical exponent `-n` or `-∞`.

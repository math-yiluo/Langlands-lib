# Compact Sobolev implies the actual Whittaker band bound

`cuspWhittakerBandBound_of_compactSobolev` applies the open
`OperatorCompactSobolevStatement` to an actual cuspidal realization with
a supplied unitary central character and actual band-integrability witness.
Its conclusion is `CuspidalWhittakerBandBound` for any standard global
additive character.

For a fixed compact open finite-adelic subgroup and compact adelic set,
the proof first obtains the uniform compact evaluation set from
`exists_isCompact_cuspWhittaker_domination`. It applies Sobolev on that set
and passes the resulting vector-dependent numerical bound through the
compact-domination lemma. The compact evaluation set precedes the
realization, additive character, vector and numerical bound in the
underlying domination theorem.

The norm and derivatives are unchanged: the estimate uses the actual
enveloping action and determinant-band quotient Haar L² norm. This is an
internal deduction. The compact Sobolev statement is motivated by Shalika
(1974), Lemmas 5.6 and 5.7, printed pp.187–188, and is retained as an open
premise, including its norm-comparison obligation. This module supplies
no globalization, functional extension or Whittaker uniqueness.

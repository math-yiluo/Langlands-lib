# Quasi-splitness over Henselian discretely valued fields

`Langlands.GroupScheme.HenselianDiscreteQuasiSplitStatement.{u}` is a
proposition-valued definition, without a proof in this module.

It quantifies over a field `K : Type u` and a valuation
`v : Valuation K (WithZero (Multiplicative ℤ))`. The hypotheses are that
`v` is surjective, its actual valuation subring is Henselian, and the
residue field of that subring is algebraically closed. For every group
scheme `H` over `Spec K`, connected reductivity then implies
`IsQuasiSplit H`.

The codomain and surjectivity supply a nontrivial discrete valuation
with a fixed integer normalization. Henselianity is the existing
`HenselianLocalRing` condition on this valuation ring. Algebraic
closedness concerns the ring's actual `IsLocalRing.ResidueField`, with
its existing quotient-field structure. The conclusion uses the existing
geometric Borel predicate: it supplies an actual field-defined Borel
inclusion which remains Borel over the algebraic closure.

This is the integer-normalized formulation of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Corollary 2.3.8, printed p.81
(PDF p.112). The setup immediately preceding Proposition 2.3.4,
printed p.80 (PDF p.111), is a discretely valued Henselian field with
algebraically closed residue field. Corollary 2.3.7 proves that this field
has dimension at most one, and Theorem 2.3.3(2), printed p.79
(PDF p.110), gives quasi-splitness of connected reductive groups over
such fields. The normalization is an internal interface choice and is
not an additional mathematical conclusion of the source corollary.

No completeness, perfectness of `K`, separability of the completion
over `K`, local compactness, finite residue field, integral model, Borel
descent datum, or pre-existing quasi-splitness is assumed. The source's
argument through the completion and dimension at most one remains a
proof obligation, as does any alternative route to the same conclusion.
Theorem 2.3.3 expressly allows imperfect fields for reductive groups.

The official 2024 corrections, Section 2.6, PDF pp.24–25, add Henselian
and perfect-residue hypotheses for later valued-group statements.
They do not modify the cited Section 2.3 corollary. The residue field
in this statement is algebraically closed and hence perfect.

This generic theorem is a substantial prerequisite of the actual
unramified-field specialization `UnramifiedQuasiSplitStatement`.
That specialization must separately supply the displayed hypotheses
for the published valuation on the actual `UnramifiedClosure F`.

# Actual realization of integer-line MW multisegments

Workers 139 and 963. This is a derived adapter from the integral-line algorithm to the
Library's actual `T.CuspidalDatum`, `T.Segment` and `T.Multisegment`. Its source
convention is Moeglin–Waldspurger (1986), II.1–II.2, printed pp.148–149, and
Badulescu (2014), `1110.5080.tex` lines 91–99 and 116–136: consecutive exponents are twists
by `ν = |det|`, and the parameterization uses Langlands heads of segment heads.
The integer-line specialization with an arbitrary real offset covers one
integral translate inside an arbitrary real cuspidal line.

For arbitrary actual cuspidal datum `ρ` and real offset `x`, the realization of
`[b,e]` is the actual segment of length `e-b+1` based at `ν^(x+b)ρ`. The code
constructs a segment at `ρ` and applies the Library's segment twist. The
`realize_member` and `realize_last` lemmas verify its members and right endpoint.
Mapping over the multiset preserves every occurrence; `realize_card` and
`realize_add` record this explicitly. All constructions allow independent field
universe `uF` and cuspidal-carrier universe `uV`. No unitarity is required.

The support adapter identifies the Library's actual cuspidal content, with
multiplicities, with the image of the combinatorial support under
`z ↦ ν^(x+z)ρ`. Its proof compares the two indexed lists for each segment and
then uses multiset induction. `realize_degree` identifies the actual GL rank
with `weight a * ρ.rank`; it follows by multiset induction and distributivity.
`support_card` counts the combinatorial point occurrences. Together these give
`realize_degree_eq_of_support_eq`, making a supplied support equality an actual
rank equality without assuming MW support preservation.

`langlandsHead_degree` unpacks the published actual Langlands-head relation and
uses `SegmentProductDatum.multisegment_degree`. `langlandsHead_isIrreducible`
unpacks the same relation's strong irreducible-head component. This supplies
the input to the Library's proved irreducibility-to-finite-length interface.
These bookkeeping lemmas are intrinsic to realization and the published
relations. They prove no assertion about `dual`: support preservation and
Aubert correctness remain separate unproved targets.

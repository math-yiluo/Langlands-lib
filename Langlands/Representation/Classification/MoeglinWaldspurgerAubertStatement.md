# Unproved actual Aubert correctness of the MW algorithm

Workers 139 and 963. `AubertCorrectness F T` is an unproved Prop-valued target for the
actual recursive integer-line output. For every actual cuspidal datum `ρ`,
real offset `x`, integer multisegment `a` and common rank `n`, it quantifies
actual smooth complex representations `π` and `πdual` of `GL_n(F)` which are
Langlands heads of the realizations of `a` and `dual a`. It asserts the equality
of their classes under the Library's actual `Aubert.adjustedOperator F T n`
in the exact finite-length Grothendieck group. It is not an abstract
classification package or a statement about formal symbols.

The source convention is Moeglin–Waldspurger, *Sur l'involution de Zelevinski*
(1986), introduction, printed pp.136–138 (the multisegment involution and its
representation comparison), and II.2, printed p.149 (the recursion).
Badulescu, *On p-adic Speh representations* (2014), retained
`1110.5080.tex` lines 72–88 and 116–136, uses the positive irreducible Aubert
involution and parameterizes by Langlands quotients of segment heads. The
Library's support-adjusted operator is the positive irreducible convention;
its alternating-sign version is not substituted here. Badulescu works after
fixing a unitary base for his applications. The target permits any actual
cuspidal base: MW's integral-line construction and comparison do not require
unitarity, and the arbitrary real offset is realized by actual twists.

The head relation includes irreducibility. The realization module's
`langlandsHead_isIrreducible` extracts it, and the proved Library interface
`SmoothRep.hasFiniteLength_of_isIrreducible` supplies each finite-length
witness used explicitly in `GeneralLinear.finiteLengthClass`. No finiteness
premise is omitted or silently assumed.

Both representations already live in the same actual group `GL_n(F)`.
`langlandsHead_degree` shows each realized multisegment has degree `n`, and
`realize_degree` computes that degree as `weight * ρ.rank`. Thus the formulation
avoids a dependent group cast by explicitly quantifying heads at a common rank,
as the mathematical assertion requires. To construct those heads at the input
rank, a subsequent proof can combine support preservation with
`realize_degree_eq_of_support_eq` and the published actual head-existence
interface. This target does not itself prove support preservation or existence.

`UniversalAubertCorrectness` quantifies over all primes, actual p-adic fields
and topological data. The field universe `uF` and cuspidal-carrier universe
`uV` are independent; the actual heads have the Library's carrier universe
`max uF uV`. Neither correctness declaration has a proof in this contribution.

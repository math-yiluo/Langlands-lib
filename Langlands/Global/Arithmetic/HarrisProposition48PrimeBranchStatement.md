# The prime-orbit branch of Proposition 4.8

`Langlands.Global.Harris.Proposition48PrimeBranchStatement` is an unproved
implication for the branch in which the actual double-coset set has
`[D:E]` elements. The parent `Q` is one-place valid, and `D/E` is an
actual Galois cyclic extension of prime degree inside its closure.

For every automorphism representative `a`, the hypothesis supplies an
actual child `R` for `D·a(E')/D`, with its exact raw norm-pulled character,
commuting field maps and inherited auxiliary place. The raw child is
valid at the parent's infinity parity, its rank is the actual Mackey
rank, and its closure degree is smaller. A genuine base character `ν`
and auxiliary character `χs` normalize its parity. The supplied actual
cuspidal realizations `S,T` satisfy `R.IsUntwistedSolution ν S T`:
`S` weakly induces the raw character, `T` weakly induces the norm-twisted
character, and their automorphic functions differ by multiplication by
`ν(det g)`. Both are conjugate self-dual and have an auxiliary
supercuspidal component; regular algebraicity is required of `T`.
The raw `S` is not assigned its corrected infinity parity. Choices need
not descend to double cosets; showing compatibility of representative
choices is part of the branch proof.

Seven foundational statements occur as separate implication premises:

- `Harris1998Theorem12CuspidalStatement` for genuine compatible families;
- `HarrisSupercuspidalLocalComparisonStatement` in arbitrary regular
  algebraic type, with a common coefficient field, embedding and pure
  weight in each comparison;
- `CuspidalSpectralRigidityStatement` and
  `Proposition48IsobaricInvarianceStatement` for multiplicity-preserving
  Galois invariance of the actual isobaric multiset;
- `CyclicRegularInductionStatement` and `CyclicRegularOrbitLiftStatement`
  for Arthur–Clozel induction and its isobaric orbit characterization;
- `CyclicWeakInductionSupercuspidalStatement` for the Henniart–Herb
  consequence at the auxiliary place.

All number fields are small. The local-field universe `uF` and the
local-factor and family-carrier universe `uV` are arbitrary. No theorem
premise is stored in a problem or a transport-data definition.

The conclusion is precisely `Q.HasSolution`: weak induction of the
parent's original character, regular algebraicity, conjugate self-duality
and the auxiliary supercuspidal component. The proof must construct
spectral presentations of the transported raw constituents, the
associated isobaric multiset and its conjugate, and the Euler equality
coming from the restriction of the parent's actual monomial family.
Only then may it apply the invariance input. The proof must also obtain
a cyclic generator, a norm-kernel Hecke character and actual unitary
central characters before using Arthur–Clozel. These are construction
obligations, not extra assumed data.

Local distinctness is another obligation: compare genuinely normalized
regular algebraic constituents using pure monomial families of a common
weight. For rank greater than one use the forward general-coefficient
comparison contrapositively; for rank one use class field theory.
The correcting characters and half-integral weight normalizations must
be transported explicitly. The resulting actual supercuspidal local
conjugates must all be distinct before invoking the Henniart–Herb input.
No supercuspidality of the downstairs output is assumed in these steps.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210,
`harris-1998-local-langlands`, proof of Proposition 4.8, printed
pp.202–203 (one-based PDF pp.26–27), companion
`math_9611226v1.tex` lines 1574–1664: Mackey induction and conditions
(i)–(iii), lines 1574–1614; the general-coefficient Remark,
1616–1628; isobaric invariance, 1630–1644; the prime-orbit case,
1646–1664. The parity issue is the printed p.191 Remark, lines
866–875, with the algebraic normalization on p.195.

This is a derived separation of that branch, including explicit
formalization obligations for the existing realization and parity
interfaces. It proves no foundational theorem and no branch result.
It adds no `n < p` bound or stronger ramified local compatibility, and
changes no published declaration.

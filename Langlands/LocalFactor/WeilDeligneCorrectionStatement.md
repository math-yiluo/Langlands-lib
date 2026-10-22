# Structural statements for the Weil–Deligne quotient correction

Worker 46 authors this theorem-statement family. Its seven components and
`Langlands.LocalFactor.WeilDeligneCorrectionStatement` are definitions
returning `Prop`, not proofs. It consumes Worker 20's actual
`Langlands.LocalFactor.WeilDeligne` quotient construction and Worker 17's
parameter operations, together with Worker 1's explicit
Frobenius-semisimplification relation. Those authors retain construction
authorship. No competing quotient or chosen local-constant system is defined.

## Actual objects and conventions

For an actual pair A=(r,N), a normal subgroup I, and an explicit element
Phi, put J=(ker N)^I and Q=V^I/J. The imported construction supplies
both subspaces, the actual quotient, induced group actions and quotient
maps. It proves the dimension formula, pair-isomorphism and inertia-coset
invariance, descent to actual classes, nonvanishing, and the N=0
normalization. Those construction results are reused rather than submitted
again as new theorem statements.

The constant correction is det(-r(Phi)|Q); the polynomial correction is
det(-X r(Phi)|Q), constructed as the monomial with that constant coefficient
and degree dim Q. The rational correction is its actual image in RatFunc K.
It is the quotient Q, not all of V or just J, that enters these formulas.
The original L-factor remains separately the reciprocal determinant on J.

Coefficient, group and two carrier universes are independent. Most components
allow every coefficient field; the tensor-block calculation requires
characteristic zero. The actual semisimplification relation specializes
coefficients to the complex numbers. No topology on carriers or extra
semisimplicity assumption is introduced.

The statements are algebraic. In an arithmetic specialization, I, Phi and
the norm character must be those of the actual local Weil group, with
geometric Phi of degree +1 and norm q^-1 for q the actual residue cardinality.
No arbitrary number is substituted for that q here. Every identity is
polynomial, rational, or an equality of actual dimensions/determinants;
there is no claim of finite numerical values at a pole.

## The seven components

1. `WDCorrectionSubquotientStatement` gives the Euler polynomial and rational
   product for the actual sequence 0 -> J -> V^I -> Q -> 0 inside a single
   pair, together with det(-Phi|V^I)=det(-Phi|J)det(-Phi|Q). The actual
   subtype equivalence and quotient projection identify this sequence.
   It does not assert that taking invariant monodromy kernels preserves
   an arbitrary short exact sequence of WD pairs.
2. `WDCorrectionDirectSumStatement` gives addition of the quotient dimensions
   and multiplication of the constant, polynomial and rational corrections
   for the actual componentwise sum of two pairs. Both invariants and the
   monodromy kernel commute with this finite direct sum.
3. `WDCorrectionBlockStatement` treats the actual uncentered block
   A tensor S_(n+1). The explicit hypothesis nu|I=1 identifies its fixed
   space with n+1 copies of A^I. Its kernel is the final weight nu^n.
   Its quotient therefore has weights nu^i, 0 <= i < n, each on A^I.
   Writing F=r_A(Phi)|A^I and d=dim A^I, the correction polynomial is
   the product of det(-nu(Phi)^i F) X^d over those n indices.
   The target separately states dimension n*d, constant determinant,
   polynomial and rational formulas. For n=0 the empty products are one
   and the quotient has dimension zero. No characteristic-zero restriction
   is necessary for a single Jordan block.
4. `WDCorrectionPairBlockStatement` treats the actual tensor of the two
   blocks of lengths n+1 and m+1. Let D=(A tensor B)^I, F=Phi|D and
   d=dim D. Invariants are taken after tensoring, not separately.
   The underlying fixed-space weights are nu^(i+j) for 0<=i<=n,
   0<=j<=m. Put P(X) equal to the product of
   det(-nu(Phi)^(i+j) F) X^d over this grid. Its monodromy kernel has
   weights nu^(n+m-j), for 0<=j<min(n+1,m+1); put Q(X) equal to the
   corresponding product of determinant monomials. Characteristic zero
   is explicit for this tensor-kernel calculation. The statement gives
   dimension ((n+1)(m+1)-min(n+1,m+1))*d, proves Q is nonzero as a
   conclusion, and asserts C(X)Q(X)=P(X) and C=P/Q in RatFunc K.
   This retains the missing kernel denominator and does not equate the
   quotient correction with the determinant on the whole tensor space.
   Nonzero norm values and invertible group actions ensure the monomials
   in Q are nonzero, including the d=0 case.
5. `WDCorrectionUnipotentChangeStatement` takes an actual carrier
   equivalence transporting N and every inertia operator, and a unipotent
   U commuting with N, inertia and the original Phi action. The new
   Phi action is conjugate to r(Phi)U. Thus U descends to Q, remains
   unipotent there and has determinant one; the transported quotient
   dimension and determinant, hence its polynomial/rational corrections,
   agree. The given equivalence need not intertwine the entire two
   group actions. This is why this component is not just the already
   proved pair-isomorphism invariance.
6. `WDCorrectionSemisimplificationStatement` consumes
   `Frobenius.IsSemisimplification`. Inertia is degree.ker and Phi has
   degree one. The relation supplies transported N and corrected
   r(g)u^(-degree(g)), with u commuting and unipotent. On inertia the
   action is unchanged; on Phi the correction is u^-1. This yields
   invariance of the actual quotient dimension, determinant, polynomial
   and rational correction. Neither the relation's existence theorem nor
   the desired invariance is assumed in the relation. This is an implication
   for actually related pairs, so no existence hypotheses are smuggled in.
7. `WDCorrectionNoInvariantsStatement` assumes the actual V^I has rank zero
   and concludes that the kernel L-polynomial/L-factor and all quotient
   corrections are one, with zero quotient dimension. This is the algebraic
   bridge needed after a ramification theorem proves the disappearance
   of invariants under a sufficiently ramified twist. It does not assert
   that disappearance without ramification hypotheses.

## Original sources and derived content

Tate, *Number theoretic background* (1979), section 4.1.6, printed page 21
(Corvallis Part II PDF page 30), defines the L-factor on J, conductor
correction dim V^I-dim J, and quotient determinant on Q. Sections
4.1.3--4.1.4 (printed pages 20--21, PDF 29--30) supply the unipotent
semisimplification and special-block conventions. The original pages
were read and the correction formula on page 21 was checked visually.
Registered original `tate-1979-number-theoretic-background`:
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

Deligne, *Les constantes des equations fonctionnelles des fonctions L*
(1973), sections 8.4.1--8.6, internal/PDF pages 68--70 (volume 568--570),
especially (8.5.1) and 8.6(i), supplies the actual correction
r(g)u^(-degree(g)) and unchanged N. These pages were read and page 70
visually checked. Section 8.12, internal/PDF page 72, gives the equivalent
epsilon-zero formulation. Registered original `deligne-1973-local-constants`:
`/home/taskhub/central-library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`,
SHA-256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.

Henniart, *Une caracterisation de la correspondance de Langlands locale
pour GL(n)* (2002), sections 2.1--2.4, printed pages 593--594 (PDF 7--8),
gives direct-sum multiplicativity and the uncentered block/tensor-kernel
weights. Both pages were visually read. Registered original
`henniart-2002-characterization`:
`/home/taskhub/central-library/Henniart--Une caracterisation de la correspondance de Langlands locale pour GL(n)--2002.pdf`,
SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

The determinant factorization, explicit quotient block formulas and
no-invariants consequence here are derived algebraic formulations of
those constructions. They are not presented as additional verbatim
theorems in Henniart. In particular Henniart's arbitrary WD exact-sequence
multiplicativity is for gamma, not for separate L and epsilon; this
family introduces no such separate multiplicativity claim.

The correction alone is not the full epsilon factor. For a fixed Haar
measure and additive character, the latter also needs the actual
nonabelian constant and spectral power with exponent
a(r)+dim(V)n(psi). Tate's conductor-normalized auxiliary power must be
distinguished from that full character-dependent spectral power.
The present family neither supplies nor assumes an epsilon system,
Artin conductor, self-dual measure, reciprocity, or local specialization.

## Published imports and validation

The imported constructions are independently published in Library
`ff093e1033dbbc93548c106d534ab35611d2c54e`. The workspace copies of their
Lean/Markdown pairs were checked byte-for-byte against that Library.
The quotient construction uses the canonical `Euler.Definitions` import;
its mathematical body agrees with the owner draft used during development.
Only this authored statement pair is submitted.

| Lean module | Published source SHA-256 |
| --- | --- |
| `Langlands.LocalFactor.WeilDeligne` | `31df51af3dc4b868c27c857c567f72f54ce9b91392059e856b990d2eb8de1a9c` |
| `Langlands.WeilDeligne.SpecialBlocks` | `1280fb510bf4f1d71c707c3b142b404d1d2914d1aacdeee3dff67e81c6312e07` |
| `Langlands.WeilDeligne.SumsTensor` | `b022cece208c2429280b3485628442f05da9e0097cb1fb558448a36bc6e0c06d` |
| `Langlands.WeilDeligne.FrobeniusStatements` | `1fb0329d6d33b89fec0770e8e97058265c82526e671ccf19b01c8218ee3ae5aa` |

Normal-workspace check `c809ff34-8700-4546-bd91-1a746dc79b3a` on 2026-10-20
compiled this module together with the rank-one and WD Euler statement
modules in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
The build and exact-target inspection completed with zero errors and warnings.
The definition returns `Prop`, retains four independent universes
`uK`, `uG`, `uV`, `uW`, and uses only `propext`, `Classical.choice`,
and `Quot.sound`. The unchanged whole-target fingerprint is
`e500fcf4a7668230fcf3c8df9d4a15a74f1cb8f5a132f6b7993938636e278998`;
the source hash is
`de7328bd719b3863bb595bf74ae959fbb870c3068d507bbe0be4761a87d296ad`.

This check establishes well-formedness, not mathematical acceptance.
Independent semantic review and publication of this statement pair remain
separate; its theorem proofs and the remaining arithmetic families are
separate responsibilities.

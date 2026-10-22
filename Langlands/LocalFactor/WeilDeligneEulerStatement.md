# Euler-factor statements on actual Weil--Deligne kernels

Worker 46 authors this statement family for task
`e534647a-77a5-4c12-91d7-8a00fe104fc4`. Its nine components and closing
`Langlands.LocalFactor.WeilDeligneEulerStatement` are definitions returning
`Prop`; no theorem proof is supplied. The module imports Worker 17's
actual parameter constructions, Worker 20's actual Euler polynomial, and
Worker 1's explicit Frobenius-semisimplification relation.
Those owners retain construction authorship. All imports are published in the
Library. No imported construction is changed by this statement contribution.

## Mathematical content and scope

For a pair `(r,N)` and a specified normal subgroup I, the operator in each
Euler factor acts on the actual nested subspace `(ker N)^I`, via
`inertiaKernelRepresentation I`. The polynomial is `det(1-X*r(Phi))`,
and `rationalFactor` is its inverse in `RatFunc K`. These are not arbitrary
factor symbols or values assigned at a pole. The statement contains no
numeric evaluation at singular spectral values.

The coefficient field, group, and two carrier universes are independent.
The ninth component specializes coefficients to the complex numbers while
retaining the independent group and two carrier universes.
The ambient construction is algebraic: no topology, finite inertia image,
Frobenius semisimplicity, or irreducibility is needed for these identities.
The pair-block calculation requires characteristic zero. Other components
retain arbitrary fields. Block lengths are `n+1` and `m+1`, so positivity
is enforced without discarding any positive length. Weil factors can have
rank zero.

This is a general algebraic part of the requested arithmetic theorem family.
An arithmetic use must supply the actual local Weil group, its inertia and
geometric Frobenius, and the actual norm character. It must instantiate
`nu(Phi)=q^-1` with q the residue-field cardinality. No arbitrary number is
called q in this module, and no local specialization is claimed here.
The existence of an epsilon system, conductor corrections, dual epsilon,
gamma formulas, highly ramified stability, and separate L/epsilon
compatibilities remain distinct obligations.

## Component-to-source correspondence

1. `WDEulerInvarianceStatement` asserts equality of the polynomial and
   rational factor for actual isomorphisms of pairs, including different
   carrier universes. It also compares two representatives Phi and Phi'
   with `Phi' * Phi^-1` in I. The action of I on the actual invariant
   kernel is trivial, so this is the precise algebraic Frobenius-lift
   independence needed by Tate 4.1.6. It is not an assertion that an
   arbitrary element is a Frobenius lift.
2. `WDEulerZeroMonodromyStatement` identifies the factor of the actual
   zero-monodromy embedding with the ordinary invariant-space factor.
   This makes the extension from Tate 3.3.2 to 4.1.6 explicit.
3. `WDEulerDirectSumStatement` asserts the two products for actual
   componentwise sums of pairs. Henniart 2002, section 2.1, uses precisely
   direct sums for L-factor multiplication. There is no arbitrary
   short-exact-sequence assertion: the monodromy-kernel invariant functor
   need not be exact.
4. `WDEulerBlockStatement` asserts that the kernel factor of the actual
   uncentered block `A tensor S_(n+1)` is the invariant factor of A with
   Frobenius multiplied by `nu(Phi)^n`, and asserts the matching dimension.
   The explicit hypothesis that nu is trivial on I is necessary for this
   inertia-space identification. The top-weight direction agrees with
   Tate 4.1.4 and Henniart 2002, section 2.4.
5. `WDEulerPairBlockStatement` applies to the actual tensor product of
   two blocks and uses the operator on `(A tensor B)^I`. It does not
   replace that space by `A^I tensor B^I`. For lengths `n+1,m+1` and
   zero-based index `j : Fin (min (n+1) (m+1))`, the exponent is
   `n+m-j.val`. Substituting the source's one-based index `j+1` in
   `lengthA+lengthB-1-index` gives exactly that exponent. The range
   makes natural-number subtraction nontruncating. Polynomial and
   rational identities are both asserted, together with the kernel
   dimension. These are the algebraic version of Henniart 2.3--2.4;
   they do not assert classification of arbitrary parameters into blocks.
   Characteristic zero is explicit because tensor Jordan-block
   decomposition can fail in small positive characteristic.
6. `WDEulerDualBlockStatement` uses the actual inverse-element dual action
   and negative-transpose monodromy. The dual of `S_(n+1)` has kernel
   weight zero. Consequently its kernel factor is the inertia factor
   of `dual A`, without a norm shift. This is the algebraic consequence
   of the displayed dual-block identity in Henniart 2.3 together with
   the single-block formula in 2.4. No characteristic-zero condition
   is needed for this single Jordan block.
7. `WDEulerDualPairBlockStatement` uses the actual tensor product of the
   two dual blocks. The operator on the right acts on
   `(dual A tensor dual B)^I`. With zero-based j, its exponent is the
   integer `-j`, exactly `1-index` in Henniart 2.4's displayed formula
   for the pair of duals. Negative exponents use integer powers, and
   the base is a nonzero norm-character value. Characteristic zero
   is retained for the tensor Jordan-block calculation. The dimension
   identity is the corresponding algebraic kernel calculation.
8. `WDEulerUnipotentChangeStatement` supplies the precise sufficient
   algebraic invariance used when removing a commuting unipotent
   Frobenius factor. Its actual linear equivalence transports monodromy
   and every inertia action. Its actual endomorphism U is unipotent
   and commutes with N, inertia, and the original Frobenius action.
   The new Frobenius is the conjugate of `r(Phi)*U`. Thus the change
   restricts to the actual invariant kernels, where the characteristic
   polynomial is unchanged. This is the linear-algebra content behind
   Tate 4.1.3--4.1.6. The statement neither chooses a Frobenius
   semisimplification nor assumes factor-invariance in a definition
   of semisimplification.
9. `WDEulerSemisimplificationStatement` consumes Worker 1's actual
   `Frobenius.IsSemisimplification` relation. The supplied integer degree
   has inertia `degree.ker`, and Phi has degree one. The relation supplies
   an actual carrier identification transporting N and a commuting
   unipotent correction u with corrected action `r(g)*u^(-degree(g))`.
   On inertia the correction is the identity, so that identification
   transports the invariant kernels. On Phi the correction is `u^-1`,
   which is still unipotent and commutes with the restricted action.
   The polynomial and rational factor on those actual kernels are
   therefore unchanged. This is the precise application of component 8
   to Deligne (8.5.1), 8.6(i), and Tate 4.1.3--4.1.6.
   The relation contains no factor-invariance clause. Its existence,
   uniqueness, or any of Worker 1's theorem targets are not hypotheses
   of this component. Nor does the component select a semisimplification.
   Since it is an implication for actually related pairs, the finite
   inertia and surjectivity assumptions needed to prove existence are
   unnecessary here. Geometric Frobenius existence and arithmetic
   specialization remain separate obligations.

The dimension identities and the arbitrary-field versions where stated
are derived algebraic formulations of the displayed constructions, not
literal additional claims of the cited articles. Worker 33's separate
generic Euler family concerns arbitrary endomorphisms; this family
concerns the concrete parameter kernels, block constructions and their
inertia actions.

## Original sources

- Pierre Deligne, *Les constantes des equations fonctionnelles des
  fonctions L* (1973), sections 8.4.1--8.6, internal/PDF pages 68--70
  (volume pages 568--570), especially (8.5.1) and 8.6(i).
  These pages were read directly; page 70 was checked visually for
  the negative degree exponent and unchanged N.
  Literature ID `deligne-1973-local-constants`; retained file
  `/home/taskhub/central-library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`;
  SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
- John Tate, *Number theoretic background*, Corvallis Part II (1979),
  section 3.3.2, printed page 14, and sections 4.1.3--4.1.6,
  printed pages 20--21. The supplied PDF has printed page p at PDF p+9.
  Literature ID `tate-1979-number-theoretic-background`; retained file
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`;
  SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- Guy Henniart, *Une caracterisation de la correspondance de Langlands
  locale pour GL(n)* (2002), sections 2.1--2.4, printed pages 593--594,
  PDF pages 7--8, visually checked.
  Literature ID `henniart-2002-characterization`; retained file
  `/home/taskhub/central-library/Henniart--Une caracterisation de la correspondance de Langlands locale pour GL(n)--2002.pdf`;
  SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

The direct originals were read. The companion development note
`NONABELIAN-INTERFACES.md` records the broader factor conventions and
remaining objects; it is not proof or acceptance evidence.

## Validation and import provenance

All imports are published in Library commit
`fe68653a42ed5ae0a2d7f5cef0697a68e8acc978`. The module reuses
`Langlands.LocalFactor.Euler`, `Langlands.WeilDeligne.Kernels`,
`Langlands.WeilDeligne.FrobeniusStatements`,
`Langlands.WeilDeligne.SumsTensor`, `Langlands.WeilDeligne.SpecialBlocks`,
and `Langlands.WeilDeligne.Dual` by their Lean names. The published sum,
special-block and dual sources agree byte for byte with the sources used
in the development checks.

Normal-workspace check `0b87c721-5af3-4d58-9b0b-e8d4e3367fde` on 2026-10-20
completed the Lake build and exact declaration inspection with zero errors
and warnings in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
The complete definition returns `Prop` at four independent universe levels
`uK`, `uG`, `uV`, and `uW`, using only `propext`, `Classical.choice`, and
`Quot.sound`. Its whole-target fingerprint is
`0b848dc50a7fdbd135879912c9213887c529d94ae8755030d00ab00fc20d8201`.
The Lean source hash is
`95e024156958f2350cffee2877908a1a8218e1d2448b9e022d0c9bfd4203beb7`.

Compilation establishes well-formedness, not a proof or independent semantic
acceptance. Each proposition remains a separate proof responsibility after
statement publication.

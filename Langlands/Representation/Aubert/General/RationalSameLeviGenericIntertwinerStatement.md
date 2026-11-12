# Generic nonzero morphisms between inductions sharing a standard Levi

Author: Worker 121.

This module states
`Langlands.Aubert.General.RationalPointFamily.RationalSameLeviGenericNonzeroIntertwinerStatement`.
It provides no proof.

## Exact content

The hypotheses are copied from the unchanged published
`RationalSameLeviGenericInductionIsoStatement.{u,v}`:

- a nonarchimedean local field of any characteristic, a connected reductive
  group, an actual maximal split torus and a generic cocharacter;
- the canonical `pointTopology` on the rational point group, with its
  local compactness, nonarchimedean-group property and Hausdorffness displayed;
- `StandardCocharacterStatement` and closedness of every literal standard
  unipotent subgroup;
- subsets `I,J`, an actual point `g` satisfying
  `x ∈ L_J ↔ g⁻¹ * x * g ∈ L_I`, and connected reductivity of the displayed
  standard Levi scheme;
- an irreducible admissible smooth complex representation `σ` of the literal
  Levi subgroup `L_J`.

The field universe `u` and representation-carrier universe `v` are independent.
There are no splitness, quasisplitness, positive-rank or characteristic-zero
restrictions. No additional topological or representation-theoretic premise
is inserted.

Write `Aχ` for the actual `normalizedInductionFunctor` from `P_J`, applied to
`σ.twist χ`, and `Bχ` for `conjugateInductionFunctor` from `g P_I g⁻¹`, applied
to the same literal twist. The second decomposition has the literal Levi
`L_J`, rather than a separately chosen isomorphic Levi. Both objects and all
normalizations are exactly those in the published isomorphism target.

The polynomial has variables `Fin (rationalImageRank L_J)` and coefficients
in `ℂ`. Its locus is the published `leviUnramifiedPrincipalOpen` in the
coordinates `leviRationalUnramifiedCharacterCoordinates`, for the full rational
norm family. A nonzero polynomial defines a dense nonempty locus by
`dense_leviUnramifiedPrincipalOpen`; rank zero is included.

The conclusion is that one nonzero polynomial `p` exists such that for
every `χ` in its principal open locus there is a morphism `f : Aχ ⟶ Bχ`
with `f ≠ 0`. This is inequality with the categorical zero morphism in
`SmoothRep`. The morphism is complex-linear and equivariant for the actual
rational point group. The choice of `f` can depend on `χ`.

Neither induced object is assumed irreducible. The conclusion supplies no
inverse, rational dependence of the chosen `f`, or identification of the
chosen `f` with an integral operator. Those stronger assertions are not part
of this target. Irreducibility and admissibility of `σ` retain the exact
consumer scope.

## Provenance and outstanding proof

This is an internal consequence target for standard intertwining theory,
chosen to isolate the part needed by the generic-isomorphism proof. It is
not a quotation of a single source statement and is not an external
structural input.

The registered original `waldspurger-2003-plancherel`, J.-L. Waldspurger,
*La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, allows arbitrary characteristic
on printed p.237. Theorem IV.1.1, p.278, gives convergence on a cone and
rational continuation of the standard operator `J_{P'|P}(π ⊗ χ)` for
finite-length admissible `π`. Formula IV.1(10), p.283, says that this
rational operator family is nonzero, using a section supported on the open
cell. In the present scope the inducing representation is irreducible
and admissible, hence of finite length.

To derive the displayed conclusion from that theory one must realize
`P_J` and `g P_I g⁻¹` as actual rational parabolics with their common literal
Levi, match the published normalization and unramified coordinates, and
show that denominators and a nonzero coefficient leave a nonzero principal
open. Multiplication by a Laurent monomial converts its defining Laurent
function to an ordinary polynomial without changing the torus locus.
None of those analytic, algebraic or structural obligations is assumed
as a premise or proved here. The existence of a nonzero convergent
intertwiner at one parameter alone would not prove this statement.

The declaration does not depend on a same-Levi isomorphism theorem,
induced Grothendieck-class equality or equality of composition factors.
A separate proof of generic irreducibility of both induced objects would
turn the nonzero morphism into an isomorphism on the intersection of the
two principal open loci. This final observation describes the intended
consumer and is not a proof of either prerequisite.

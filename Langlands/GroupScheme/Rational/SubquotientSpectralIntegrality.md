# Integral characteristic polynomials of actual subquotients

This derived unit implements the inheritance of spectral integrality under
actual representation subquotients, a step in the composition-factor argument
of Kaletha–Prasad, Lemma 2.2.11 (printed pp.72–73, PDF pp.103–104). Its primary
construction is `Langlands.GroupScheme.MatrixRepresentation.integralCharpolyOfSubquotient`.

Let `k` be any field with `ValuativeRel k`, let `G` be an actual group scheme
over `Spec k`, and let `σ` and `ρ` be actual finite-dimensional matrix
representations. Given the published predicate `IsSubquotientOf σ ρ` and
`ρ.HasIntegralCharacteristicPolynomials`, the construction assigns to each
actual rational point `g` a polynomial over the integer ring of
`ValuativeRel.valuation k`. The returned subtype certifies that the polynomial
is monic, its coefficient map to `k` is exactly the characteristic polynomial
of `σ.rationalMatrix g`, and its natural degree is the dimension of `σ`.
The helper theorem `IsSubquotientOf.hasIntegralCharacteristicPolynomials`
proves the corresponding integral-coefficient predicate directly.

The field universe is arbitrary. Matrix dimensions may be zero, and the field
may have any characteristic or valuation rank, including a trivial valuation.
There are no reductivity, faithfulness, density, topology, local-field or
semisimplicity assumptions in this unit. `IsSubquotientOf` supplies an actual
intermediate representation, an injective constant matrix into `ρ`, and a
surjective constant matrix onto `σ`; its intertwining laws quantify over every
affine algebra test. No additional rational-point intertwining assumption is
introduced.

The implemented proof has the following steps.

1. `isRoot_charpoly_of_injective_intertwiner` sends a nonzero eigenvector
   through the injective matrix. The eigenvector equation gives the ambient
   eigenvalue and hence the characteristic-polynomial root. For
   `isRoot_charpoly_of_surjective_intertwiner`, a linear right inverse makes
   the transpose intertwiner injective; transposition preserves characteristic
   polynomials. These root lemmas allow arbitrary finite index types in
   independent universes.
2. `coeff_vle_one_of_map_roots_subset` transfers integral coefficients between
   monic polynomials when, after mapping to the unvalued algebraic closure,
   every root of the second polynomial is a root of the first. Lift the first
   monic polynomial to the valuation ring. Every root of it in the algebraic
   closure is integral over that ring. The split-factorization criterion
   `Polynomial.isIntegral_coeff_of_factors` makes the second polynomial's
   coefficients integral; injectivity of the field map descends integrality
   to `k`. Integrally closedness of the valuation ring then identifies this
   with the coefficient inequalities `≤ᵥ 1`. Root multiplicities need not be
   compared. No valuation is chosen or extended on the algebraic closure.
3. The matrix coefficient lemmas apply that polynomial result after mapping
   the intertwining matrices to the algebraic closure. Published left/right
   inverse arguments preserve injectivity and surjectivity under this scalar
   extension.
4. `rationalAffinePoint` identifies the base-field affine algebra test with
   the actual rational-point source using a morphism over `Spec k` whose
   underlying scheme map is the identity. `rationalMatrix_eq_affineMatrix`
   combines naturality with the global-section isomorphism of `Spec k`.
   Consequently `Intertwines.rationalMatrix` specializes the all-test
   intertwining law to the actual matrices used in the spectral target.
5. Apply injective inheritance to the intermediate representation and then
   surjective inheritance to `σ`. Lift its resulting integral characteristic
   coefficients to a monic polynomial over the valuation ring, preserving
   the natural degree. Classical choice selects the polynomial together
   with all three certificates.

The source argument passes to irreducible composition factors over an
algebraic closure and uses their eigenvalues. This unit isolates and proves
the inheritance step without requiring irreducibility or a valuation on the
closure; the coefficient formulation is the one in the published spectral
prerequisites. It does not assert existence of composition factors, finiteness
of their common kernel, rational-point density, matrix boundedness, or the
host `ReductiveSpectralBoundednessStatement`.

Sources: Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma
2.2.11 and its proof, printed pp.72–73 / PDF pp.103–104; registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The November 2024 corrections, Section 2.2, PDF p.24, impose Henselianity on
the section and amend Lemma 2.2.5. This elementary inheritance proof does not
use that extension-topology comparison or Henselianity; its weaker hypotheses
are justified by the proof above. Registered corrections source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

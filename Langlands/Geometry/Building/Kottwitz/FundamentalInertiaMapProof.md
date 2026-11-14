# Fundamental-group inertia descent

Worker 269. `fundamentalInertiaMapStatement` proves exactly
`Langlands.Geometry.Building.Kottwitz.FundamentalInertiaMapStatement`.
For every compatible normal tower `k → K → E`, with `E` a separable closure
of `k`, every morphism of connected reductive `k`-groups induces a unique
linear map on inertia coinvariants. The selected map satisfies its
representative law, commutes with the residual `Aut_k(K)` action, and
preserves identities and composition.

The proof implements the quotient argument behind the inertia consequence of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Construction 11.3.1,
Lemma 11.3.6 and §11.5, printed pp. 427–430 / PDF pp. 458–461. The registered
source is `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`)
have Chapter 11 entries starting with §11.7 on PDF page 43 and do not change
these passages. Inertia descent is an explicit consequence of the Galois
functoriality in Lemma 11.3.6, used for the targets in §11.5.

The original-map and comparison obligations are discharged by the Library
theorems `algebraicFundamentalGroupComparison` and
`algebraicFundamentalGroupMap_of_comparison`. The reduction
`fundamentalInertiaMap_of_fundamentalGroup` takes the original functor laws
as a premise; the final theorem supplies the published proof
`algebraicFundamentalGroupFunctor`. Thus the final result has no additional
premises beyond its target.

For an original Galois-equivariant fundamental-group map, the composite with
the target inertia projection is invariant under the source inertia action.
`Representation.Coinvariants.lift` therefore constructs a linear map on inertia
coinvariants. Its value on each representative is the required value, and
surjectivity of the quotient projection proves uniqueness. Existence then
justifies the epsilon-selected `fundamentalInertiaMap`'s representative law.

To establish residual equivariance, the proof lifts an automorphism of `K/k`
to an automorphism of `E/k`, using normality and the restriction-surjectivity
theorem. Every inertia class is represented by an element of the original
fundamental group. On such a representative,
`inertiaGammaRepresentation_restrict` and the representative law reduce the
claim to original Galois equivariance.

Finally, the identity and composition equations are tested on quotient
representatives. The original functor statement gives composition directly.
For the identity, that statement identifies the original identity map with
the comparison of a chosen presentation with itself; the comparison statement
identifies this comparison with the identity linear map. No finiteness,
torsion or local-field premise is used in this quotient argument.

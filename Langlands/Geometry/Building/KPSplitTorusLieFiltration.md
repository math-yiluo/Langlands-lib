# The real-depth Lie filtration of the standard split torus

Let `F` be a nonarchimedean local field, with `[ValuativeRel F]`,
`[TopologicalSpace F]` and `[IsNonarchimedeanLocalField F]`. Let `I` be a
finite type in the same universe as `F`, and take the actual split torus
`T = Gₘ^I` over `F`. There is no characteristic or residue characteristic
restriction. Write `𝒪 = 𝒪[F]`, `𝔪 = 𝓂[F]`, and
`A₀ = IntegralModel.lieLattice (IntegralModel.splitTorusModel 𝒪 F I)`
in the generic Lie space `GenericLie 𝒪 T.toGrp`. This is the image of
Lie of the smooth standard model under the generic-fibre identification,
not a supplied submodule. The building datum `P` is the published
`ParahoricBuildingData.ofTorus` of this group.

## Construction and calculations

The declarations are in `Langlands.Geometry.Building.ParahoricBuildingData`.

- `splitTorusLieFiltration F I` constructs `P.LieFiltrationData`. At
  `r : NNReal` its centralizer input is `𝔪^⌈r⌉₊ • A₀`. Powers of `𝔪`
  decrease and the natural ceiling is monotone. The actual relative roots
  are empty by commutativity and splitness of the chosen subtorus. An
  ordinary affine root would have a relative root as its derivative, so
  there are no affine-root inputs. The centralizer of `P` is the torus
  itself with the identity inclusion.
- `splitTorus_lieFiltration` computes the nonnegative-depth Lie piece
  at every apartment point `x`: it is exactly `𝔪^⌈r⌉₊ • A₀`. The supremum
  of the empty root summands is zero and the differential of the
  centralizer inclusion is the identity. `splitTorus_lieFiltration_zero`
  gives `A₀`, and `splitTorus_lieFiltration_isPeriodic` proves the unit
  shift law from `⌈r + 1⌉₊ = ⌈r⌉₊ + 1`.
- `splitTorus_lieFiltrationReal` computes the extension at every real `r`
  as `π^⌈r⌉ • A₀` for any irreducible `π : 𝒪` (a uniformizer), with an
  integer exponent in `Fˣ` interpreted by scalar multiplication in `F`.
  Put `n = ⌈−r⌉₊`. The shifted nonnegative lattice is
  `π^n • (π^⌈r⌉ • A₀)` since `⌈r + n⌉ = ⌈r⌉ + n` and `𝔪 = (π)`.
  Membership in the real-depth definition tests all scalars in `𝔪^n`.
  Testing the generator `π^n` and cancelling gives one implication;
  every other scalar is a multiple of that generator, giving the converse.
  `splitTorus_lieFiltrationReal_isLattice` proves finite generation over
  `𝒪` and spanning over `F` using smoothness of the standard model and
  preservation of lattices by nonzero scalar multiplication.
- `splitTorus_lieFiltrationPlusReal` computes the strict piece at any
  real `r` as `π^(⌊r⌋ + 1) • A₀`. The depth `s = ⌊r⌋ + 1` is strictly
  above `r`. Every `t` in `(r,s)` has ceiling `s`, and all `t ≥ s`
  give pieces inside the piece at `s` by antitonicity. Thus the strict
  supremum is attained at `s`.
- `splitTorus_lieFiltrationPlusReal_lt_iff` proves that the strict piece
  is properly contained in the non-strict piece exactly when `I` is
  nonempty and `r` is the image of an integer in `ℝ`. At a noninteger
  the exponents coincide. At an integer, strictness reduces by scalar
  cancellation to `𝔪 • A₀ < A₀`. For nonempty `I`, the Library's
  infinitesimal-coordinate equivalence gives a nonzero generic Lie space.
  The lattice spans that space, so it is nonzero. Nakayama's lemma applied
  to the finitely generated `A₀` shows `𝔪 • A₀ ≠ A₀`. For empty `I`, the
  same coordinate equivalence gives a zero Lie space and there are no
  strict inclusions.

## Sources and scope

This is a derived split-torus calculation. Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach` (SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`),
§13.3.1 (printed p. 470 / PDF p. 501) supplies the unit shift, the
extension to real indices, and the strict-depth convention. §13.3.3
(printed pp. 470–471 / PDF pp. 501–502) describes the Lie lattice as the
span of a centralizer lattice and affine-root lattices. In the split-torus
case only the centralizer term remains. The weakly induced torus formula
in §8.5.20 (printed p. 320 / PDF p. 351) specializes with the trivial
extension and ramification degree one to the powers of `𝔪` in the split
torus coordinates. For the source's torus filtration convention, see
Proposition B.10.5 and Corollary B.10.13 (printed pp. 687 and 692 / PDF
pp. 718 and 723): the minimal congruent filtration agrees with the standard
filtration for weakly induced tori, in particular for split tori.

The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections` (SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`),
leave these cited passages unchanged. Their Chapter 8 entries stop in §8.4;
PDF pp. 49–50 give changes to §§13.5, 13.6 and 13.8 and to the definition
and descent discussion in §B.10, not the weakly induced comparison in
B.10.5 and B.10.13.

The calculation uses the actual standard depth-zero model, but **does not
construct or identify** the positive-depth group schemes of §8.5 or their
Lie algebras by a model morphism. It supplies the split-torus case of the
expected lattice formula as an input to the Library Lie-filtration API,
not descent or a group/Lie quotient comparison. The lattice formulas are
for the standard split torus and its chosen building datum; they do not
identify different constructions of a torus model. No external code is
adapted.

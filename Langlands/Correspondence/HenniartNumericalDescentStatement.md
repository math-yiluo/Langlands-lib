# Slope bounds and descent for Henniart's numerical correspondence

Author: Worker 981, Task 7379, revision 3.

This module states three propositions in `Langlands.Henniart` for Option II
of the numerical local Langlands route note. It proves none of them.
The universes for p-adic fields (`uK`), Weil representations (`uW`), and
supercuspidal representations (`uV`) are independent. A positive rank
`n = k + 1` is represented by `k.succPNat`.

## Slope bound under base change

`BaseChangeSlopeStatement.{uK, uV}` assumes the supercuspidal twist Swan
bound. Let `p` be any prime, `S` any cyclic prime-degree step `M/L` of
p-adic fields (`S.base = L`, `S.top = M`), and `Ch` any map with
`Numerical.IsWeakCyclicBaseChange S Ch`. Let `π` be a supercuspidal class of
rank `k + 1` over `L` and let `x` be real. If
`Numerical.HasSupercuspidalSwan S.base π s` and `s ≤ (k + 1)x`, then every
constituent `ρ` of the multiset `Ch k π` has Swan exponent at most
`(ρ.1 + 1) ψ_{M/L}(x)`, where `ρ.1 + 1` is its own rank and
`ψ_{M/L} = S.herbrandPsi` is the Herbrand function. The inequalities are
over the reals. This says that the slope (Swan exponent divided by rank)
of each constituent is at most `ψ_{M/L}(x)`.

The input Swan exponent is witnessed by a finite conductor. On the output
side the statement uses the published `Numerical.supercuspidalSwanExponent`,
which reads the first fixed level with default zero at `⊤` and subtracts the
rank in `ℕ`. It does not add a finiteness hypothesis or assert finiteness as
part of the conclusion. `Ch` records cuspidal support, not a lift on all
irreducible representations; see [weak cyclic base change](HenniartCyclicBaseChange.md).
This is the supercuspidal-input case of route note §6.4, Lemma `lem:slopebc`.
The note uses the fibre description, the conductor identity, and the
supercuspidal consequence of Lemma `lem:level`(ii) to bound the slope.

## Descent through one cyclic step

Write `C(K, x, N)` for `Numerical.CountsAgreeUpToSlope K x N`.
For each rank `k + 1 ≤ N`, natural Swan exponent `s ≤ (k + 1)x`, and
torsion number (unramified-twist stabilizer size) `f`, the two refined
unramified-twist orbit strata have equal extended cardinalities, and the
supercuspidal stratum is finite. See [refined strata](HenniartRefinedStrata.md).

`DescentStepStatement.{uK, uW, uV}` assumes the twist Swan bound and natural
Artin conductor existence. For every prime `p`, step `S : CyclicPrimeStep p`,
and natural bound `N`, take families `φL` and `φM` from irreducible Weil
classes to supercuspidal classes of the same rank over `L` and `M`,
respectively. Each family takes a rank index `k` and a proof `hk : k + 1 ≤ N`.
For every such `k` and `hk`, both maps must be numerical injections:
injective, preserving the conductor whenever the Weil Artin conductor is
given, and compatible with unramified twists. Suppose a common `Ch` satisfies
weak cyclic base change, `IsBaseChangeCompatible S Ch N φL φM`, and
`ReflectsGaloisInvariance S N φM`. Then for every real `x`,
`C(M, ψ_{M/L}(x), N)` implies `C(L, x, N)`.

This is the count implication of route note §6.6, Lemma `lem:step`. The
[injection families and compatibility predicates](HenniartCompatibleInjections.md)
are those of Task 7376, revision 3. The first predicate is (CI1): `Ch` on the
image of a Weil class agrees with applying `φM` to the multiset of
restriction constituents. The second says that if `φM k hk τ` is fixed by
`Gal(M/L)`, then `τ` is fixed under conjugation by `W_L`. This is the part of
(CI2) used in the singleton-support case of `lem:step`, as explained in
Remark `rem:CI2` (§6.5). The remark's way of deriving this reflection from
(CI1) can use ranks above `N`; the statement assumes reflection in ranks up
to `N` instead. Neither family, (CI1), nor reflection requires injections
or injection compatibility in ranks above `N`. The named ambient twist,
Artin, and weak base-change premises keep their published scopes.

## Conditional assembly

`NumericalDescentStatement.{uK, uW, uV}` has exactly these five premises:

1. **(I1)**, [`SupercuspidalStratumUpperBoundStatement`](HenniartGLUpperBoundStatement.md):
   the GL-side refined counts are bounded above by the polar-part counts
   at the residue cardinality of the field. An exact GL-side count is not assumed.
2. **(LD)**, [`LaumonDeligneCountStatement`](HenniartLaumonDeligneStatement.md):
   for every p-adic field `K` and `1 ≤ s < d e_K`, the counts of Weil orbits
   with torsion number one and Swan exponent `s` agree in ranks `d` and
   `d + s`. Here `d` is positive and `e_K` is the absolute ramification index.
3. **(I4)**, [`CompatibleNumericalInjectionsStatement`](HenniartCompatibleInjections.md):
   for every step and bound `N`, if every numerical injection in ranks
   strictly below `N` over every p-adic field is surjective, then there are
   families up to `N` and a common weak `Ch` satisfying the one-step
   compatibility and reflection conditions. This already supplies (I3),
   the existence of weak cyclic base change, by taking `N = 0` where the
   lower-rank premise is vacuous. There is no separate (I3) premise.
4. [`SupercuspidalTwistSwanBoundStatement`](HenniartTwistSwanStatement.md),
   the supercuspidal part of route note Lemma `lem:level`(ii): twisting `π`
   by `χ` composed with the determinant gives Swan exponent at most
   `max(sw(π), n sw(χ))`, with equality if the two entries differ. This is
   the bound used in `lem:slopebc`.
5. [`WeilArtinConductorExistenceStatement`](HenniartRefinedStrata.md):
   every irreducible Weil class has a natural Artin conductor in the
   Library's sense. This integrality input lets the counting argument pass
   from a particular family reaching all classes in range to surjectivity
   of arbitrary numerical injections. More precisely, part (b) of
   `CountingSurjectivityStatement` needs Artin conductor existence to
   obtain equal counts from that family's surjectivity in range. Once the
   counts are available, part (a) applies to any numerical injection
   without a separate integrality hypothesis. Artin conductor existence
   also lets a bijective numerical injection compare the exact conductor strata.

Together the premises imply the following three conclusions:

- `C(K, x, N)` for every prime `p`, every `K : PadicField.{uK} p`, every real
  `x`, and every natural `N`.
- `NumericalSurjectivityStatement`: every numerical injection over every
  p-adic field and in every positive rank is surjective, hence bijective.
- `NumericalOrbitCountStatement`: for each p-adic field, positive rank,
  and natural conductor, the Weil and supercuspidal unramified-twist orbit
  strata are finite and have equal cardinalities. This is an equality by
  conductor, not just by Swan exponent: conductors zero and one give the
  same Swan exponent in rank one. These are the unchanged
  [numerical targets](HenniartNumericalStatement.md).

In the intended proof, (I4)'s lower-rank premise is supplied by induction
on `N`, using the counts for smaller rank bounds and the counting lemma.
The conductor theorem is not a premise: the Library's proved
`Langlands.Conductor.supercuspidalPadicConductorExponent` gives the finite
first fixed level needed to apply the counting lemma to each supercuspidal
class. At rank bound `N`, the proof starts below the absolute ramification
index at the top of a cyclic tower, using (I1), (LD) and the injections at
that field. The one-step statement descends the count equalities. The
counts do not depend on the chosen injections, so (I4) may supply a different
compatible pair for each step. This is the point of `rem:compareH88`(5).
The Lean propositions do not require `x ≥ 0` or `N ≥ 1`: a negative slope
cutoff admits no nonnegative Swan exponent in positive rank, and `N = 0`
admits no positive rank.

## Provenance

These conditional forms are from the route note, with the rank-bounded (I4)
interface and `ReflectsGaloisInvariance` in place of (CI2). They are not the
numbered results as printed in the original literature.

- *The numerical local Langlands correspondence for GL_n: counts on the two
  sides and the recommended route of proof*, 16 November 2026, registered
  as `operator-numerical-llc-route-2026-11-16`. In `numerical-LLC-route.tex`,
  see §6.4, `lem:slopebc` (lines 1136–1148), §6.5, `rem:CI2` (1170–1174),
  and §6.6, `lem:step` (1177–1194), `thm:descent` (1211–1224), and
  `rem:compareH88` (1226–1233). The twist bound is `lem:level`(ii)
  (626–627); `C(L,x,N)` and the counting lemma are in §6.1 (1058–1084).
  Section 7.1, item 7 (1311–1313), groups the three conditional statements.
- Guy Henniart, *La conjecture de Langlands locale numérique pour GL(n)*,
  Ann. Sci. ÉNS (4) 21 (1988), 497–544, registered as `henniart-1988-numerical`.
  The proposition of §6.7 (pp. 519–520, PDF pp. 24–25) bounds the slope
  of cyclic base change by the Herbrand function. It treats all irreducible
  classes and reduces to the supercuspidal case and prime degree. Section
  6.8 (pp. 520–521, PDF pp. 25–26) descends slope-bounded surjectivity through
  cyclic steps using the compatible injections of Théorème 1.9. The note
  replaces Henniart's choice of tower in a `ℤ_p`-extension by a Kummer
  tower and uses the GL-side upper bound from simple types rather than the
  count from Jacquet–Langlands and Koch (`rem:compareH88`). The surjectivity
  conclusion corresponds to the second assertion of Théorème 1.2 (p. 498,
  PDF p. 3). The orbit-count conclusion is the Library's comparison by
  conductor; it does not state the explicit Weil-side formula
  `C_K(n, j) = (q_K − 1) q_K^j` of Théorème 1.3 (same page).

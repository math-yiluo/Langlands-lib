# K-level normality and equivariance from rank-one torus estimates

This internal helper module adapts the Library's `MoyPrasadDoubleRootConjugation`
and the root-classification step of `MoyPrasadCovarianceReduction` to
`B : MaximalUnramified.BuildingData F H`, with `K = UnramifiedClosure F` and
`hZ : IsTorus B.centralizer.Z`. It concerns the actual groups of `KPLocalMoyPrasadGroups`
`B.moyPrasad hZ x r`, with their unchanged torus filtration. All declarations are
at arbitrary universe `u` and for every characteristic of `F`.

This is conditional proof material for clauses 1–2 of
`LocalMoyPrasadGroupPropertiesStatement`, not a proof of that statement. The
hypotheses below are explicit and have not been discharged here.

## Exact inputs

`LocalTorusDoubleRootCommutatorFriendly B hZ` is the pointwise form of the estimate
stated in `KPLocalDoubleRootCommutatorStatement`: for nonidentity opposite root elements with positive sum `d` of
the two ordinary-root valuations, if either input lies in its doubled-root
group, every middle coordinate of the specified opposite-root decomposition
of `u'⁻¹ u u' u⁻¹` belongs to `B.centralizerTorusFiltration hZ (2 * d)`.
The predicate includes both possible doubled inputs. This module uses the
second-input case. It neither proves nor assumes any clause of
`LocalMoyPrasadGroupPropertiesStatement` to obtain it.

`LocalTorusRootCompatible B hZ` is precisely the root compatibility clause of
`QuasiSplitLocalTorusFiltrationStatement`:
the commutator of a torus-image element of depth `r` and a root element of depth
`s` lies in the root block of depth `r+s`. The other input,
`LocalTorusCommutatorFriendly B hZ`, is defined in
`KPLocalMoyPrasadRootConjugation` and is precisely the first clause of
`QuasiSplitLocalTorusFiltrationStatement` at `B,hZ`.

## Implemented proof

1. `double_opposite_central_mem_of_doubleRootCommutatorFriendly`: consider
   `u ∈ U_{a,x,0}` and `v ∈ U_{-2a,x,r}`, with `r>0`, and an exchange
   `v' * j(z) * u' = u * v`. The valuation doubling identity puts `v` in
   `U_{-a,x,r/2}`. If either input is the identity, uniqueness of the opposite
   root / centralizer / root product forces `z=1`. Otherwise the two finite
   ordinary-root values have sum `d≥r/2>0`. Rewrite the exchange as
   `v⁻¹ u v u⁻¹ = (v⁻¹v') * j(z) * (u'u⁻¹)`. The doubled-root predicate puts
   `z` in depth `2d`; antitonicity puts it in depth `r`.
2. `conjugate_double_opposite_mem_moyPrasad_of_doubleRootCommutatorFriendly`
   supplies that central estimate to the already implemented mixed
   coordinates in `KPLocalMoyPrasadMixedConjugation`. Both root blocks and the
   torus image are generators of the same-depth Moy–Prasad subgroup.
3. `conjugate_root_mem_moyPrasad_of_double_opposite_bound` classifies two root
   directions. V3 handles nonopposite directions. Negative proportional roots
   are equal or doubled in one direction, by
   `KPApartmentData.eq_or_double_of_eval_eq_smul`. The required affine-root
   system and derivative identifications come from
   the published `IntegerValuationExtendedAffineRoots`, using `exists_order_eq_one F`; no
   apartment axiom is assumed. The three proportional cases use ordinary
   opposite conjugation, the supplied mixed case, or inclusion of a
   doubled-root depth-zero subgroup into its ordinary-root counterpart.
4. `conjugate_root_mem_moyPrasad_of_torus_commutator_bounds` supplies the mixed
   case and also handles `r=0` by closure of `B.moyPrasad hZ x 0` under
   multiplication and inversion.
5. `localMoyPrasadNormality_of_torus_commutator_bounds` proves clause 1
   conditionally by `localMoyPrasadNormality_of_root_conjugation` in
   `KPLocalMoyPrasadCovariance`. Root compatibility handles conjugating the
   torus image by root generators; V6 makes torus-image generators normalize
   the group, and the root cases handle the remaining generators.
6. `localMoyPrasadEquivariance_of_torus_commutator_bounds` proves both forms of
   clause 2 conditionally. The unconditional theorem
   `B.centralizerTorusImage_isNormalizerStable` (module
   `KPLocalCentralizerFiltrationNormalizerStable`) gives normalizer covariance.
   `localMoyPrasadEquivariance_of_normality` then uses the actual reduced
   building quotient relation and clause 1 to prove building covariance.

## Provenance and limits

The source targets are Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Proposition 7.3.17 (printed p.252, PDF p.283), and Remark 7.6.5 and
(7.6.2) (PDF pp.295–297). The sharper doubled-root estimate is an independent
input motivated by the SU3 computation in the quasi-split proof of
Proposition 7.1.1 (printed pp.239–240, PDF pp.270–271). It is not a separately
numbered claim in that source. The registered 2024 corrections, PDF p.33,
qualify the chapter's apartment-axiom usage. Here the root-system facts needed
by classification are proved in the integer-valuation helper rather than
postulated as apartment axioms.

The module transports the published F-level algebraic proof route to the
integer-valued building data over `K`, whose residue field is infinite, so it
does not instantiate `ParahoricBuildingData` over `K`. It claims neither
unconditional normality nor the full `LocalMoyPrasadGroupPropertiesStatement`:
the three explicit rank-one inputs remain hypotheses here.

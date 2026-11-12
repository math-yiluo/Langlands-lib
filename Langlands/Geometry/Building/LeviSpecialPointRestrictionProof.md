# Proof: affine roots and special points under restriction to a standard Levi

`Langlands.Geometry.Building.leviSpecialPointRestriction` proves exactly
`LeviSpecialPointRestrictionStatement.{u}` at every universe `u`. This is
Kaletha–Prasad §6.7.2 for the actual standard Levi subgroups
`M_J = Standard.leviScheme i ν J` of a connected reductive group over a
nonarchimedean local field, at the same maximal split torus. The proof adds no
premise. In particular, it assumes neither `IsAffineRootSystemWithRankZero` nor
the AS 3 equality of derivative roots for `D.affineRoots` or
`DM.affineRoots`, and it uses no unproved proposition.

## Route

The published modules `Langlands.BruhatTits.SpecialCompact.LeviApartmentRestriction`,
`LeviApartmentProjection`, `LeviAffineRoots` and `LeviSpecialPoint` work with a
cocharacter Levi `j : M → G`. This is the dynamic centralizer of
`ζ ≫ i`, closed in `G`, at the same split torus. For `D` they construct the
restricted class `R = leviRestrictedApartmentData … D`. Its points are the
restrictions `φ_M` of the points `φ` of `D` (KP Lemma 6.7.1). They also
construct the affine surjection `π = leviApartmentAffineProjection … D` from
`D.Apartment` onto `R.Apartment`. The proof reduces the target to these
constructions in four steps.

1. **The given Levi data are the restricted class.**
   `IsLeviRestriction.val_eq_val` shows that two restrictions of the same point
   `x` have equal valuations. On the roots of `(M, S)` they agree by the
   definition of `IsLeviRestriction`. Off the roots both are `⊤` by
   `IsRootDatumValuation.eq_top_of_not_mem_roots`. Apartment data are
   determined by their equipollence class (`KPApartmentData.eq_of_carrier_eq`,
   by cases on the structure). The class is the set of valuations equipollent
   to any one of its points (`KPApartmentData.mem_iff_equipollent`). So two
   apartment data with a common point are equal
   (`KPApartmentData.eq_of_apartment_val_eq`). The premise
   `IsLeviRestriction j x₀ xM₀` and the published
   `isLeviRestriction_leviApartmentProjection` for `π x₀` give `DM = R`
   (`eq_leviRestrictedApartmentData`). After substitution, the same argument
   shows that `IsLeviRestriction j x xM` forces `xM = π x`.
2. **Clauses 1 and 2.** For `ψM` in `Ψ(M, S)`, respectively `Ψ′(M, S)`, take
   `ψ = leviAffineRootPullback … ψM = ψM ∘ π`. The published
   `leviAffineRootPullback_mem_affineRoots` and
   `leviAffineRootPullback_mem_extendedAffineRoots` (module `LeviAffineRoots`)
   put `ψ` in `D.affineRoots`, respectively `D.extendedAffineRoots`. They
   rest on the transport of root groups, filtrations and doubled-root groups
   along the closed inclusion `j`. Since `xM = π x`, the equation
   `ψ x = ψM xM` holds by definition.
3. **Specialness.** For a special point `x` of `D.affineRoots`, the published
   `isSpecialPoint_leviApartmentProjection` (module `LeviSpecialPoint`)
   proves that `π x = xM` is special for `R.affineRoots`.
4. **Vertexhood without AS 3.** The published
   `isSpecialPoint_isVertex_leviApartmentProjection` needs the AS 3 premise
   `derivativeRoots D.affineRoots = range (rootForm i)`, which is not
   available here. The proof uses two new lemmas on any `KPApartmentData` of a
   split torus with finitely many roots instead.
   - `KPApartmentData.exists_affineRoot_linear_eq_smul_rootForm`: every
     root `a` has an ordinary affine root `ψ` with `ψ̇ = c · a` for some real
     `c ≠ 0`. Axiom V 0 (`IsRootDatumValuation.exists_ne_top`) gives
     `u ∈ U_a(k)` with a finite value `t` at a point `x`. The functional with
     derivative `a` and value `t` at `x` is in `Ψ′`
     (`KPApartmentData.affineFunctional_mem_extendedAffineRoots`). Its root
     is `a` by `rootForm_injective_of_split`. The doubling lemma
     `KPApartmentData.exists_two_pow_smul_mem_affineRoots` then produces
     `m` with `2^m ψ ∈ Ψ`. It inducts on an `n` with `2^n a ∉ Φ`. If `ψ ∉ Ψ`,
     then `2a` is a root (`mem_affineRoots_of_not_double_root`), and `2ψ`
     has a filtration jump in direction `2a`
     (`affineRootGroupPlus_double_ne_of_not_mem_affineRoots`, module
     `AffineRootDoubling`). Such an `n` exists
     (`KPApartmentData.exists_two_pow_smul_not_mem_relativeRoots`) because
     the roots are finite (`IsSplitTorus.finite_relativeRoots`). Distinct
     `n` give distinct roots `2^n a`, since
     `rootForm (2^n a) = 2^n · rootForm a` (`rootForm_nsmul`) and
     `rootForm a ≠ 0` (`rootForm_ne_zero_of_split`).
   - `KPApartmentData.isVertex_of_isSpecialPoint_of_rootDirections`: when
     every root direction occurs up to a nonzero factor, a special point
     `x` is a vertex. Let `y` lie in the facet of `x` and let `a` be a root.
     Take `ψ ∈ Ψ` with `ψ̇ = c · a`. Specialness
     (`AffineRootSystem.isSpecialPoint_iff_ker`, with nonconstant roots by
     `affineRoot_linear_ne_zero_of_split`) gives `φ ∈ Ψ` with `φ(x) = 0` and
     `ker φ̇ = ker ψ̇`. Then `φ(y) = 0` by
     `AffineRootSystem.facet_subset_hyperplane`, so
     `c · rootForm a (y -ᵥ x) = 0`. Every root form thus vanishes on
     `y -ᵥ x`, and `eq_zero_of_rootForm_eq_zero` gives `y = x`. This is the
     argument of KP Proposition 1.3.43(3). It also covers relative rank zero,
     where the translation space is trivial.

   The Levi `M` has finitely many roots because it is smooth, hence locally
   of finite type. Applying both lemmas to `R` gives the vertex property of
   `π x`.

The core result is
`Langlands.BruhatTits.SpecialCompact.leviSpecialPointRestriction_of_isLeviRestriction`.
It is stated for any cocharacter Levi in the setting of `LeviSpecialPoint`,
for any `ω` and any Levi data `DM` containing one restriction of a point of `D`.

## Instantiation for the standard Levi

`leviSpecialPointRestriction` introduces the statement's data and the same
instances as the statement (`hG.isAffineHom`, `hi.isSplitSubtorus.mono`,
`(Standard.isClosedSubgroup_leviHom i ν J).isAffineHom`,
`(Standard.isMaximalSplitTorus_leviTorusHom i ν J hi).isSplitSubtorus.mono`).
It obtains `Smooth` and `ConnectedSpace` for `G` from `hG`, and `Smooth` for
`M_J` from `standardLevi_isConnectedReductive` (module
`LeviApartmentComparison`). The published theorem `standardCocharacter`
(`StandardCocharacterStatement`) supplies a cocharacter `ζ` whose dynamic
centralizer is represented by `Standard.leviHom i ν J`
(`Standard.isRepresentedBy_leviHom`). This is the same instantiation as the
published `prescribedLeviSpecialVertex`. The core result then applies with
`hS = hi.isSplitSubtorus.1`, `hcomp = Standard.leviTorusHom_comp i ν J` and
`hjc = Standard.isClosedSubgroup_leviHom i ν J`.

## Library results used

- `Langlands.BruhatTits.SpecialCompact.LeviApartmentRestriction`:
  `leviRestrictedApartmentData`, `leviApartmentProjection`,
  `isLeviRestriction_leviApartmentProjection`.
- `Langlands.BruhatTits.SpecialCompact.LeviApartmentProjection`:
  `leviApartmentAffineProjection`.
- `Langlands.BruhatTits.SpecialCompact.LeviAffineRoots`:
  `leviAffineRootPullback`, `leviAffineRootPullback_mem_affineRoots`,
  `leviAffineRootPullback_mem_extendedAffineRoots`.
- `Langlands.BruhatTits.SpecialCompact.LeviSpecialPoint`:
  `isSpecialPoint_leviApartmentProjection`, `rootForm_injective_of_split`,
  `rootForm_ne_zero_of_split`, `affineRoot_linear_ne_zero_of_split`.
- `Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison`:
  `standardLevi_isConnectedReductive`.
- `Langlands.GroupScheme.Rational.StandardCocharacterProof`:
  `standardCocharacter`. `Langlands.GroupScheme.Rational.StandardRepresentability`:
  `Standard.isRepresentedBy_leviHom`, `Standard.isClosedSubgroup_leviHom`.
  `Langlands.Geometry.Building.SpecialCompactLevi`:
  `Standard.leviTorusHom_comp`, `Standard.isMaximalSplitTorus_leviTorusHom`.
- `Langlands.Geometry.Building.KPApartment`:
  `KPApartmentData.mem_iff_equipollent`, `KPApartmentData.Apartment.ext`,
  `IsRootDatumValuation.exists_ne_top`, `KPApartmentData.affineFunctional_linear`.
  `Langlands.Geometry.Building.RootDatumValuation`:
  `IsRootDatumValuation.eq_top_of_not_mem_roots`.
- `Langlands.Geometry.Building.ChamberFiltration`:
  `KPApartmentData.affineFunctional_mem_extendedAffineRoots`.
- `Langlands.Geometry.Building.AffineRootDoubling`:
  `KPApartmentData.mem_affineRoots_of_not_double_root`,
  `KPApartmentData.affineRootGroupPlus_double_ne_of_not_mem_affineRoots`.
- `Langlands.Geometry.Building.ChamberPositiveCollection`: `rootForm_nsmul`.
- `Langlands.GroupScheme.Rational.RootSupportFiniteness`:
  `IsSplitTorus.finite_relativeRoots`.
- `Langlands.Geometry.Building.ActualAffineRootArrangement`:
  `eq_zero_of_rootForm_eq_zero`.
- `Langlands.Geometry.Building.AffineRootSystem`:
  `AffineRootSystem.isSpecialPoint_iff_ker`,
  `AffineRootSystem.facet_subset_hyperplane`, `AffineRootSystem.mem_facet_self`.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
  It is used for §6.7 and Lemma 6.7.1 (printed p.233 / PDF p.264), §6.7.2
  (printed pp.233–234 / PDF pp.264–265) and Proposition 1.3.43(3) (printed
  p.30 / PDF p.61). KP derive specialness of the image from the preimage
  description of the hyperplanes, and vertexhood from Proposition
  1.3.43(3). The Lean proof follows the same two steps. For the second step
  it shows directly that the needed root directions occur, using V 0 and
  doubling, because the affine-root-system axioms of `DM.affineRoots` are not
  available as premises.
- Kaletha–Prasad, *Corrections and additions* (1 November 2024), registered
  as `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`. None of
  its corrections concerns §6.7.

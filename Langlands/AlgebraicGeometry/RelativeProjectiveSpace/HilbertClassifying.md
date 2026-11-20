# A classifying scheme for flat projective families with finitely many points

This module packages the published Hilbert scheme of `ℙ^m_ℤ`
(`HilbertSchemeUniversalFamilyStatement`, proved by
`HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily`) in the presentation of the
Library's `RelativeProjectiveSpace`, and adds finitely many integral projective points.
All schemes lie in one universe `u`.

## Declarations

- `RelativeProjectiveSpace.isoPullbackSpec m s`: for `s : T ⟶ Spec (ULift ℤ)`, the
  isomorphism `RelativeProjectiveSpace T m ≅ pullback (projectiveSpaceToSpec (ULift ℤ) m) s`
  (both are fibre products over the terminal scheme); `map_isoPullbackSpec_hom` is its
  compatibility with change of base.
- `comap_isoPullbackSpec_subschemeι_toBase`, `comap_isoPullbackSpec_iff`: an ideal sheaf
  `J` on the fibre product and its transport `J.comap (isoPullbackSpec m s).hom` to relative
  projective space have isomorphic closed subschemes over `T`; flatness and local finite
  presentation transfer.
- `RelativeProjectiveSpace.iterate m H k`: `k` successive relative projective `m`-spaces
  over `H`, with `iterateToBase`, `iterateCoord` (the `k` integral coordinates),
  `iterateLift`, and `iterateLift_toBase`, `iterateLift_coord`, `iterate_hom_ext`: a
  morphism `T ⟶ iterate m H k` is the same as a morphism `T ⟶ H` and `k` morphisms
  `T ⟶ ProjectiveSpace (ULift ℤ) m`.
- Instances: relative projective space and its iterates over a locally noetherian scheme are
  locally noetherian (the structure morphism is proper, hence locally of finite type).
- `exists_relativeProjectiveFamily_classifying m R` (for a finite type `R`): there are a
  locally noetherian scheme `S`, an ideal sheaf `IS` on `RelativeProjectiveSpace S m` whose
  closed subscheme is flat and locally of finite presentation over `S`, and points
  `σS r : S ⟶ ProjectiveSpace (ULift ℤ) m` (`r : R`), such that for every scheme `T`, every
  ideal sheaf `I` on `RelativeProjectiveSpace T m` with flat, locally finitely presented
  closed subscheme and all points `σ : R → (T ⟶ ProjectiveSpace (ULift ℤ) m)` there is a
  unique `t : T ⟶ S` with `IS.comap (map m t) = I` and `t ≫ σS r = σ r` for all `r`.

## Proof

`ℙ^m_ℤ` is H-projective (identity embedding), so
`exists_closedImmersionBySections_iff_isHProjective` supplies the invertible module required
by the Hilbert theorem; flatness and local finite presentation of `projectiveSpaceToSpec`
are published instances. The Hilbert scheme `H` is locally of finite presentation over the
noetherian `Spec (ULift ℤ)`, hence locally noetherian. Take `S = iterate m H |R|` (through
`Fintype.equivFin R`), `IS` the transported universal ideal sheaf `W` pulled back to `S`, and
`σS` the coordinates. Existence and uniqueness of `t` come from the Hilbert universal
property for the `H`-component (after transport through `isoPullbackSpec`) and from
`iterate_hom_ext` for the coordinates. Flatness of `IS` is the Hilbert theorem's flatness
of every classified family.

## Provenance

Internal packaging of the published Hilbert scheme (Grothendieck, FGA; Mumford–Fogarty–
Kirwan, GIT §0.5(c), "closed subschemes with k sections"). Used in Task 7811's reduction
(`FrameChartRepresentabilityReduction`), where `R` is the set of level coefficient tuples.

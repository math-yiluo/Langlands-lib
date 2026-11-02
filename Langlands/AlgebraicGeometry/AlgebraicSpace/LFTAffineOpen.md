# Affine open subfunctors represented by schemes locally of finite type

Internal infrastructure. It lets the group-space proof show that the glued scheme is locally
of finite type without descending local finite type along etale covers.

- `IsLFTAffineOpen A`: an open subfunctor represented by an affine scheme locally of finite
  type over the base.
- `RelLFT f`: relative local finite type of a presheaf map.
- `locallyOfFiniteType_of_relLFT`: a relatively locally finitely typed map between
  represented functors comes from a scheme morphism locally of finite type, by Yoneda. So
  local finite type passes from the target scheme to the source scheme. Representing schemes
  are unique up to isomorphism, so this applies to any choice.
- `relLFT_of_isIso`, `relLFT_of_isOpenImmersion`, `RelLFT.comp`, `relLFT_schemeYoneda_map`,
  `relLFT_mapRight` and `relLFT_fromPreimage` (restriction to preimage subfunctors, via the
  pullback square `isPullback_fromPreimage`). `isOpenImmersion_homOfLe`: the inclusion of a
  smaller open subfunctor is a relative open immersion.
- `IsLFTAffineOpen.of_relLFT`: an affine open with a relatively locally finitely typed map to
  an LFT-affine open is LFT-affine.
- Closure under the constructions of the group-space argument: `isLFTAffineOpen_range`,
  `IsLFTAffineOpen.preimage_iso`, `IsLFTAffineOpen.preimage_mapRight` (for `ρ` affine and
  locally of finite type), `isLFTAffineOpen_iInf` and `IsLFTAffineOpen.iInf_preimage_iso`
  (nonempty finite intersections, given a closed diagonal). These extend Worker 1150's
  `IsAffineOpen` lemmas.

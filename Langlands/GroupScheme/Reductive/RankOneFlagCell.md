# The open cell through a fixed point of a homogeneous space

Internal helper module of the Task 7586 proof of
`Langlands.GroupScheme.RankOneCentralCoverStatement`. It works over a field `k`. A group scheme
`G` over `Spec k` acts on a scheme `X` over `Spec k` by `a : SchemeAction G X`, and
`x : Spec k ⟶ X` is a rational point. Nothing here is specific to reductive groups.

## Generic lemmas

- `cellOrbit a x iM` is the orbit map of `x` restricted along a subgroup `iM : M ⟶ G`,
  i.e. `m ↦ m · x`.
- `tripleCell_comp_orbitMap`: if `x` is fixed (on all tests) by subgroups `iZ` and `iU`, then on
  the triple product `M × Z × U` the orbit map composed with
  `Dynamic.tripleCellMultiplication iM iZ iU`, `(m, z, v) ↦ m z v`, is the first projection
  followed by `cellOrbit`. This is `(m z v) · x = m · (z · (v · x)) = m · x`.
- `range_fst_comp`: the first projection of the triple product has a section, so composing with
  it does not change images.
- `gmOrbit_opposite`: the `Gm`-orbit along the opposite cocharacter
  `Dynamic.oppositeCocharacter χ` is the orbit along `χ` precomposed with inversion on `Gm`.
- `restrict_restrict_act`, `isFixed_restrict_restrict_iff`, `gmOrbit_restrict_restrict` and
  `isGmOrbitExtension_restrict_restrict_iff`: restricting an action along `g` and then along `f`
  acts like restricting along `f ≫ g`. These are point formulas; the two actions are not claimed
  to be definitionally equal.
- `evalZero_eq_of_isFixed`: for a separated target, an orbit extension of a fixed point takes the
  point itself as its value at `0`. The constant map is an extension, and extensions are unique
  (`SchemeAction.IsGmOrbitExtension.unique`).

## Cell data

`Cell a x` bundles:
- a cocharacter `χ : Gm ⟶ G`;
- closed subgroups `iM`, `iZ`, `iU` representing `U(-χ)` (`Dynamic.unipotent` of
  `Dynamic.oppositeCocharacter χ`), the centralizer `Z(χ)` and `U(χ)`;
- the facts that `x` is fixed by `iZ` and by `iU`;
- the fact that the triple cell multiplication is an open immersion.

For a cell `C`:
- `C.opens` is the image of `cellOrbit a x C.iM`. When the orbit map of `x` is flat and locally
  of finite presentation, it is open: by `tripleCell_comp_orbitMap` it is also the image of the
  open triple cell under a flat, locally finitely presented map (`UniversallyOpen.of_flat`).
- `C.scheme`, `C.incl` and `C.lift` are the open subscheme, its open immersion into `X`, and the
  factorization of morphisms whose image lies in it.
- `C.orbitLift` and `C.cellLift` are the factorizations of `cellOrbit` and of the triple-cell
  orbit map through `C.scheme`, with `cellLift_eq : cellLift = fst ≫ orbitLift`.
- `cellLift` is flat, quasi-compact (when the triple cell multiplication and the orbit map are)
  and surjective. Flatness and quasi-compactness are base change along the open immersion
  (`IsOpenImmersion.isPullback_lift_id`).
- `act_eq_of_mem_centralizer` and `exists_conj_of_mem_centralizer`: centralizer points fix `x`
  and normalize `U(-χ)`. The latter uses `Dynamic.centralizer_le_precomp`,
  `Dynamic.centralizer_le_parabolic` and `Dynamic.conj_mem_unipotent`.
- `isGmStable`: the open cell is stable, in the all-test sense `SchemeAction.IsGmStable`, under
  every cocharacter `ψ` whose range centralizes `χ`. For a test point `z` of the cell, the proof
  pulls back along the surjective `cellLift`. There `z` lifts to the triple cell, and
  `ψ(s) · (m z' v) · x = (ψ(s) m ψ(s)⁻¹) · x` lies in the image of `U(-χ)`. Surjectivity of the
  pullback projection then gives the image condition for `z` itself.
- `exists_limit`: every point `m · x` of the cell flows to `x` along the opposite cocharacter.
  The extension is `e(s) = e_m(s) · x`, where `e_m` is the identity-valued extension of the
  conjugation orbit of `m ∈ U(-χ)` (definition of `Dynamic.unipotent`). Points of `χ` fix `x`.
- `exists_chevalleyMap`: for a unipotent first factor, a morphism `ρ : C.scheme ⟶ V` to an
  affine scheme, such that points of `U(-χ)` with equal images under `ρ` have equal images in
  the cell. Construction:
  - `Q` is the stabilizer of `x` in `U(-χ)`, a closed subgroup by
    `SchemeAction.exists_isClosedSubgroup_stabilizer`; it is unipotent by
    `unipotentClosedSubgroup`.
  - `Chevalley.exists_affine_vector_orbit` gives an affine vector orbit map
    `r : U(-χ) ⟶ V` whose fibres are exactly the `Q`-cosets.
  - `fst ≫ r` on the triple cell equalizes the kernel pair of `cellLift`
    (`orbitLift_eq_iff`), so it descends along the fpqc map `cellLift` by `EffectiveEpi.desc`.

  This is how the intersection `Q` of `U(-χ)` with the stabilizer is handled: only its exact
  coset fibres enter, through Chevalley's theorem for the closed subgroup scheme `Q`. No
  smoothness, reducedness or normality of `Q` is used.
- Over an algebraically closed field:
  - `exists_orbitLift_eq`: every rational point of the cell is `m · x` for a rational `m`
    (`exists_rationalPoint_lift_of_mem_range`).
  - `exists_chevalleyMap_injective`: `ρ` is injective on rational points.
  - `exists_lift_of_mem`: a rational point of `X` in the cell factors through it.
  - `mem_opens_x`: `x` lies in the cell.
  - `eq_of_limit` (two limits): if a rational point `y` of the cell also flows to `x` along `χ`,
    then `y = x`. The orbit of `y` extends at `0` along `-χ` (`exists_limit`) and along `χ` (the
    hypothesis). Both extensions lift into the stable open cell (`SchemeAction.gmOrbitOpenLift`).
    After composing with `ρ`, the two-sided constancy lemma
    `TwoSidedConstancy.evalZero_eq_of_twoSided` shows `ρ(x) = ρ(y)`. Injectivity gives `x = y`.
  - `eq_of_isFixed`: a rational point of the cell fixed by the opposite cocharacter is `x`.
  - `mem_opens_of_limit`: if the extended orbit of a rational point under a cocharacter
    centralizing `χ` takes a value in the cell at `0`, the point itself lies in the cell.

## Provenance

Internal. The cell and limit arguments follow the Białynicki-Birula style limit arguments already
in the Library (`Dynamic/SchemeActionLimit`, `Dynamic/BruhatCellLimit`). The Chevalley map is the
classical device of Chevalley's theorem on quotients, applied only to obtain a map to an affine
scheme with prescribed fibres. All steps are proved in Lean from the named Library results and
the Task 7586 helper modules `Dynamic/TwoSidedConstancy` and `Dynamic/GmOrbitInversion`.

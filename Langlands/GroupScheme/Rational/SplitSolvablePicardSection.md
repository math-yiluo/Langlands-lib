# Sections of split-solvable series quotients over Picard-trivial bases

Author: Worker 755.

This module proves, over a field `k`, that every quotient map `q : H ⟶ V` in
a split-solvable series (`SplitSolvable.HasSeries`, module
[`SplitSolvable`](../SplitSolvable.md)) has a section as a morphism of
schemes over `Spec k`. It is a helper for
[`SplitSolvableSectionsProof`](../SplitSolvableSectionsProof.md) (through
[`SplitSolvableTorusDomination`](SplitSolvableTorusDomination.md)); it
contains no definition from the literature and one internal predicate,
`SplitSolvablePicard.PicCocyclesVanish`.

The idea: a torsor under a group with a split-solvable series, over an
affine base whose ring of global functions has trivial Picard group, is
trivial; the quotient map `q` is such a torsor over `V`, and the coordinate
rings `k[t]` of `G_a` and `k[t, t⁻¹]` of `G_m` have trivial Picard group.
Torsors are handled through the Library's `Cocycle` (module
[`TorsorCocycle`](../TorsorCocycle.md)): a cocycle of `G` on a cover
`U` is a natural family `ξ(a, b)` of points of `G`, for pairs of points of
`U` over the same test scheme, with `ξ(a, c) = ξ(a, b) ξ(b, c)`; it is
trivial (`IsTrivial`) when `ξ(a, b) = f(a) f(b)⁻¹` for a point `f` of `G`
over `U`.

## Picard groups

- `subsingleton_pic_of_ringEquiv_of_subsingleton`: a commutative ring
  isomorphic to one with trivial Picard group has trivial Picard group
  (functoriality `CommRing.Pic.mapRingHom` applied to `e⁻¹ ∘ e = id`).
- `subsingleton_pic_of_scheme_iso`: the same for the global functions of
  isomorphic schemes.
- `subsingleton_pic_Γ_Spec`: `Γ(Spec A)` has trivial Picard group if `A`
  does (via `Scheme.ΓSpecIso`).

## Split-torus cocycles over Picard-trivial affine bases

`Cocycle.isTrivial_split_of_isAffine_of_pic_trivial`: let `S` be an affine
scheme with `Pic Γ(S)` trivial, `U` an affine, flat, surjective scheme over
`S`, and `ξ` a cocycle of the split torus `splitTorus S I` (`I` finite) on
`U`. Then `ξ` is trivial. Proof: each coordinate `i ∈ I` gives a unit
cocycle (`Cocycle.unitCoordinate`), natural and multiplicative, for the
composite `U → S ≅ Spec Γ(S)`. The Library's
`Langlands.Scheme.Modules.unitCoboundaryOfPicTrivial` writes each as a
coboundary of a unit on `U`; these units assemble into a point `f` of the
split torus over `U` (`splitTorus.pointsEquiv`) with `ξ(a, b) = f(a) f(b)⁻¹`.

## Picard-trivial cocycle vanishing

Let `R` be a commutative ring and `H` a group scheme over `Spec R`.

- `SplitSolvablePicard.PicCocyclesVanish H` (internal predicate): for every
  scheme `T` over `Spec R` with `T` affine and `Pic Γ(T)` trivial, and every
  affine, flat, surjective `U` over `T`, every cocycle of the base change
  of `H` to `T` on `U` is trivial. It is the Library's `CocyclesVanish`
  (module [`SplitUnipotentAffineTorsorProof`](../SplitUnipotentAffineTorsorProof.md))
  restricted to Picard-trivial affine bases;
  `PicCocyclesVanish.of_cocyclesVanish` records the implication.
- `picCocyclesVanish_of_isVectorGroup`: one-dimensional vector groups
  satisfy it (the Library's `Cocycle.isTrivial_of_isVectorGroupOfDimension_one`).
- `picCocyclesVanish_of_isSplitTorus`: split tori satisfy it. Transport the
  cocycle along `V ≅ G_m^I` and its base change
  (`splitTorus.baseChangeIso`), apply the previous section, and pull the
  trivialization back with `Cocycle.IsTrivial.of_map_retract`.

### One step of a series

Fix `j : K ⟶ H` with `j.hom.hom` a monomorphism and `q : H ⟶ V` with
`range (kernelι q) = range j`.

- `SplitSolvablePicard.exists_section`: if `H.X.left` and `V.X.left` are
  affine, `Pic Γ(V.X.left)` is trivial, `q` is flat and surjective on
  schemes, and `PicCocyclesVanish K`, then there is `σ : V.X ⟶ H.X` over
  `Spec R` with `σ ≫ q.hom.hom = 𝟙 V.X`. Proof: regard `H.X` as a cover
  `U'` of `V.X` through `q`. The identity of `H.X` gives a point `F` of the
  base change of `H` to `V.X` over `U'`; its coboundary takes values in the
  kernel of `q` (since `a ≫ F ≫ q` does not depend on `a`), hence lifts to a
  cocycle of the base change of `K` (`baseChange_exists_comp_eq`). That
  cocycle is trivial by `PicCocyclesVanish K` with `T = V.X`, giving a point
  `J` with the same coboundary as `F` and `J ≫ q = 1`. Then `J⁻¹ F` is
  constant on fibres of the effective epimorphism `U' → V.X`, so it
  descends (`exists_section_of_forall_eq`) to a section `s` of the base
  change; composing with the first projection gives `σ`, and
  `σ ≫ q = 𝟙` is checked after cancelling the epimorphism `q`.
- `SplitSolvablePicard.picCocyclesVanish_of_section`: given such a scheme
  section `σ`, `PicCocyclesVanish V` and `PicCocyclesVanish K` imply
  `PicCocyclesVanish H`. A cocycle `ξ` of `H` maps to a trivial cocycle of
  `V`, trivialized by `f₀`; lift `f₀` through `σ` to `f₁`; the twisted
  cocycle `f₁(a)⁻¹ ξ(a, b) f₁(b)` lies in the kernel, so it lifts to a
  cocycle of `K`, which is trivial; hence `ξ` is trivial
  (`Cocycle.IsTrivial.of_lift`, `Cocycle.IsTrivial.of_twist`).

## Over a field

Let `k` be a field and `V` a group scheme over `Spec k` with
`SplitSolvable.IsElementaryQuotient V` (a one-dimensional vector group, or
isomorphic to `G_m`).

- `subsingleton_pic_of_isVectorGroup`, `subsingleton_pic_of_iso_gm`,
  `subsingleton_pic_of_elementary`: `Pic Γ(V.X.left)` is trivial. For a
  vector group, `V` is isomorphic to `Spec k[t]` (`vectorCoordinatesIso`)
  and triviality of `Pic (MvPolynomial (Fin 1) k)` is found by instance
  inference;
  for `G_m`, `V` is isomorphic to the diagonalizable group with coordinate
  ring `k[ℤ] = k[t, t⁻¹]` and the Library's
  `IntLatticeAlgebra.subsingleton_pic` applies.
- `isAffineHom_of_elementary`: `V` is affine over `k`.
- `picCocyclesVanish_of_elementary`: `PicCocyclesVanish V`.
- `exists_section_of_step`: in a series step `j : N ⟶ H`, `q : H ⟶ V`
  (closed subgroup, fppf quotient by `range j`, elementary `V`, `H` affine
  over `k`), `PicCocyclesVanish N` gives a scheme section of `q`.
- `picCocyclesVanish_of_hasSeries`: by induction on `n`, every `H` affine
  over `k` with `SplitSolvable.HasSeries n H` satisfies
  `PicCocyclesVanish`. Length zero: `H` is trivial
  (`cocyclesVanish_of_range_id_eq_bot`). Successor: the kernel `N` has a
  shorter series and is affine (closed in `H`); combine the step section
  with `picCocyclesVanish_of_section`.
- `exists_section_of_hasSeries`: every quotient map `q : H ⟶ V` of a series
  step whose kernel `N` has a series (in particular every step of a
  split-solvable series) has `σ : V.X ⟶ H.X` with
  `σ ≫ q.hom.hom = 𝟙 V.X`.

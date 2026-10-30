# Fibrewise detection of isogenies between smooth proper group schemes

This module proves `Langlands.GroupScheme.FiberwiseIsogenyStatement` as the
theorem `Langlands.GroupScheme.fiberwiseIsogeny`. For a scheme `S`, group
schemes `G H` over `S` whose structure maps are smooth and proper, and a
homomorphism `f : G ⟶ H`: if, for every point `s : S`, the pullback of `f`
along `Spec κ(s) ⟶ S` (computed by `(Over.pullback (S.fromSpecResidueField s)).mapGrp`)
is an isogeny, i.e. finite, flat and surjective, then `f` is an isogeny.

The criterion is derived, not a verbatim statement from a source. Its
motivation is Milne, *Abelian Varieties*, Section 20, Proposition 20.7. The
proof follows the component route in the statement's Markdown, using
Stacks Project tags 01K1 (fibre topology), 01W6 (properness), 02LS (finite =
proper + quasi-finite) and 039E (fibrewise flatness).

Throughout, `S` is a scheme, `X Y : Over S`, `f : X ⟶ Y`, and for a point
`s : S` the fibre map is the actual scheme morphism
`((Over.pullback (S.fromSpecResidueField s)).map f).left`. This is a map
`pullback X.hom ι_s ⟶ pullback Y.hom ι_s`, where `ι_s = S.fromSpecResidueField s`.
The group structure is never used. Every component lemma is stated for a
general morphism in `Over S`.

## Points of residue-field fibres

- `fiberMap_fst`: the fibre map followed by the first projection to `Y`
  equals the first projection to `X` followed by `f.left` (this is
  `pullback.lift_fst`).
- `exists_fst_eq`: a point `x` of `X` with `X.hom x = s` is the image of a
  point of the fibre `pullback X.hom ι_s`. This uses Mathlib's
  `Scheme.Pullback.range_fst` (the range of a first projection is the preimage
  of the range of the second map) and `Scheme.range_fromSpecResidueField`
  (the range of `ι_s` is `{s}`); compare Stacks tag 01K1.
- `fst_injective`: the first projection `pullback X.hom ι_s ⟶ X` is injective,
  since it is a topological embedding (Mathlib's `Scheme.Hom.isEmbedding`,
  available because it is a base change of the preimmersion `ι_s`).

The proof never assumes that an arbitrary fibre product of schemes is a fibre
product of point sets. It uses only these two facts about residue-field fibres.

## Components

- `surjective_of_fiber`: if every fibre map is surjective, `f.left` is
  surjective. Given `y`, lift it to `y'` in the fibre over `Y.hom y`, choose
  `x'` with `f_s x' = y'`, and push `x'` to `X` using `fiberMap_fst`.
- `finite_preimage_singleton_of_fiber`: if every fibre map has finite point
  preimages, so does `f.left`. Take `y` with lift `y'`. Every `x` with
  `f x = y` lies over the same point of `S` (by `Over.w f`), so it lifts to
  some `x'`. Injectivity of the projection to `Y` then gives `f_s x' = y'`.
  Hence `f⁻¹{y}` lies inside the image of the finite set `f_s⁻¹{y'}`.
- `isFinite_of_fiber`: if `X.hom` is proper, `Y.hom` is separated, and every
  fibre map is finite, then `f.left` is finite. Properness of `f.left` follows
  from `IsProper.of_comp` applied to `f.left ≫ Y.hom = X.hom` (Stacks 01W6).
  Finite fibre maps have finite point preimages
  (`Scheme.Hom.finite_preimage_singleton`), so `f.left` has finite point
  preimages. It is therefore locally quasi-finite by
  `LocallyQuasiFinite.of_finite_preimage_singleton`, which needs the finite
  type that properness supplies. Finally,
  `IsFinite.iff_isProper_and_locallyQuasiFinite` (Stacks 02LS) gives
  finiteness.

## Main theorem

`fiberwiseIsogeny : FiberwiseIsogenyStatement` introduces `S`, `G`, `H`, the
smoothness and properness instances, `f`, and the fibrewise hypothesis `hf`.
The underlying scheme map of `(Over.pullback ι_s).mapGrp.map f` is, by
definition, the fibre map of `f.hom.hom : G.X ⟶ H.X` above. So the three
parts of `IsIsogeny` for each fibre are read off directly from `hf s`. The
three parts of `IsIsogeny f` are then proved as follows:

- finiteness by `isFinite_of_fiber f.hom.hom`. `G.X.hom` is proper, and
  `H.X.hom` is proper and hence separated;
- flatness by the published theorem
  `Langlands.AlgebraicGeometry.fiberwiseFlatness`, which proves
  `FiberwiseFlatnessStatement` (Stacks tag 039E, first assertion). It is
  applied to `f.hom.hom` in `Over S`. Its hypotheses are flatness and local
  finite presentation of `G.X.hom` and local finite type of `H.X.hom`. Mathlib
  instances derive all three from smoothness;
- surjectivity by `surjective_of_fiber f.hom.hom`.

No hypotheses are added beyond those of the target statement.

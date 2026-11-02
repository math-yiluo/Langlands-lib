# The Deligne torus is reductive: proof

Authors: Worker 207 (Lean proof and Markdown, shared as this task's draft) and Worker 254
(recheck and submission).

This module proves `Langlands.Shimura.DeligneTorus.ReductiveStatement` from
`Langlands.Shimura.Unitary.DeligneReductiveStatement`. It says that the real Deligne group scheme
`groupScheme` is a connected reductive group over `ℝ` (`IsConnectedReductive`) and a reductive
group scheme over `Spec ℝ` (`IsReductive`). The final theorem is `reductiveStatement`. It uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

All declarations are in the namespace `Langlands.Shimura.DeligneTorus`. The proof uses the
split-torus results of `Langlands.GroupScheme.Torus.SplitReductiveProof`
(`IsSplitTorus.connectedSpace`, `IsSplitTorus.hasTrivialUnipotentRadical`,
`IsSplitTorus.isPseudoReductive`). It also uses the published facts that the Deligne torus is
smooth (`smooth_groupScheme`, from `Langlands.Shimura.Unitary.DeligneNonSplitProof`) and that its
complex base change is a split torus (`isSplitTorus_complexGroupScheme`).

## Geometric base changes are split

- `exists_factor_complexBaseMap Ω b`: let `Ω` be an algebraically closed field and
  `b : Spec Ω → Spec ℝ` a morphism. Then `b = c ≫ complexBaseMap` for some
  `c : Spec Ω → Spec ℂ`. Every morphism of affine schemes is `Spec` of a ring map
  (`Spec.map_surjective`). That ring map makes `Ω` an `ℝ`-algebra. `ℂ` is algebraic over `ℝ`, so
  `IsAlgClosed.lift` gives an `ℝ`-algebra map `ℂ → Ω`, and `c` is its spectrum.
- `isSplitTorus_baseChange Ω b`: the base change of `groupScheme` along such a `b` is a split
  torus. Write `b = c ≫ complexBaseMap`. Base change along a composite is base change along
  `complexBaseMap` followed by base change along `c`, up to isomorphism (`Over.pullbackComp`,
  `Functor.mapGrpNatIso`, `Functor.mapGrpCompIso`). The first base change is `complexGroupScheme`,
  a split torus. Split tori stay split under base change (`IsSplitTorus.baseChange`), and the
  property moves along isomorphisms (`IsSplitTorus.of_iso`).

## Affine and connected

- `isAffineHom_groupScheme`: the structure map is `Spec` of the algebra map
  `ℝ → CoordinateRing`, so it is affine.
- `connectedSpace_groupScheme`: the scheme `complexGroupScheme` is a pullback of `groupScheme`
  along `complexBaseMap`. It is connected, because it is a split torus over the field `ℂ`. The
  map `complexBaseMap` is surjective (first component of the published `complexBaseMap_fpqc`), so the first
  projection of the pullback is surjective. A continuous surjection maps a connected space onto a
  connected space, so `groupScheme` is connected.

## Reductivity

- `isConnectedReductive_groupScheme`: smoothness and the two lemmas above. The geometric
  condition holds because the base change along `toAlgebraicClosure ℝ` is a split torus over an
  algebraically closed field (`isSplitTorus_baseChange`), so it has trivial unipotent radical.
- `isReductive_groupScheme`: smoothness and affineness. For each point `s`, the geometric fibre
  is the base change along `geometricPoint _ s`. It is a split torus over an algebraically closed
  field, hence pseudo-reductive.
- `reductiveStatement` combines the two.

## Relation to the literature

The statement's Markdown cites Milne's Proposition 21.60 (over a perfect field, reductive means
the radical is a torus). This proof does not use the radical. It follows the second route
recorded there: `𝕊_ℂ ≅ 𝔾_m × 𝔾_m` is split, every algebraically closed field over `ℝ` contains a
copy of `ℂ`, and split tori over algebraically closed fields are reductive.

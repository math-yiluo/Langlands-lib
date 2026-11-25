# Reduction of the torsion-closed immersion lemma to the group-algebra models

This module is an internal step of the proof of
`Langlands.GroupScheme.MultiplicativeTypeTorsionDeterminationStatement`. It reduces the
torsion-closed immersion lemma `TorsionClosedImmersionIsIso` of [`Assembly`](Assembly.md)
(every torsion-closed immersion into a group of multiplicative type is an isomorphism) to
its core case for the affine group-algebra models `D(Λ) = Spec R[Λ]` over affine bases, and
records the resulting implication from the core case to the target statement. All
declarations are in the namespace `Langlands.GroupScheme.TorsionDetermination`; `PointLifts`,
`IsTorsionClosed` and the descent results are in [`Descent`](Descent.md).

## Propositions introduced

Two `Prop`-valued abbreviations name the intermediate cases. They are hypotheses of the
theorems below, not claims proved here.

- `SplitAffineCase.{u}`: for every commutative ring `R : CommRingCat.{u}`, every finitely
  generated abelian group `Λ : Type u`, every scheme `Z` and every immersion
  `j : Z ⟶ (diagonalizable (Spec R) Λ).X.left` with
  `IsTorsionClosed (diagonalizable (Spec R) Λ) j`, the morphism `j` is an isomorphism. Here
  `RelativeMultiplicativeType.diagonalizable S Λ` is the published diagonalizable group
  `D_S(Λ)`, the base change of `D(Λ)` from `Spec ℤ`.
- `DiagonalizableCoreCase.{u}`: for every `R : CommRingCat.{u}`, every `Λ : Type u` with
  `[AddCommGroup Λ] [AddGroup.FG Λ]`, every object `Z` of `Over (Spec R)` and every morphism
  `i : Z ⟶ (Diagonalizable.groupScheme R Λ).X` over `Spec R` with `IsImmersion i.left`: if
  for every `T : Over (Spec R)` and all points `x y : T ⟶ (Diagonalizable.groupScheme R Λ).X`
  that factor through `i` (`∃ a, a ≫ i = x`) the product `x * y` factors through `i`, and
  every point `x` with `x ^ n = 1` for some `n > 0` factors through `i`, then `i.left` is an
  isomorphism. Here `Diagonalizable.groupScheme R Λ` is the published group-algebra model
  `Spec R[Λ]` over `Spec R` (a commutative group scheme; `.X` is its underlying object of
  `Over (Spec R)`). This is the form of the core case proved by
  `isIso_left_of_diagonalizable` in [`Diagonalizable`](Diagonalizable.md).

## Results

- `lifts_id_of_iso` and `isIso_of_iso`: if `e : D ≅ G` and every torsion-closed immersion
  into `D` is an isomorphism, then for a torsion-closed immersion `j` into `G` the identity
  point of `G` lifts through `j`, and so `j` is an isomorphism. Proof: the pullback of `j`
  along `e.hom` is a torsion-closed immersion into `D` (`IsTorsionClosed.pullback`), hence an
  isomorphism; then `lifts_id_of_pullback_iso` and `isIso_of_lifts_id`.
- `lifts_iff_exists_overHom`: viewing a scheme `Z` with `j : Z ⟶ X.left` as an object
  `Over.mk (j ≫ X.hom)` of `Over S`, with `Over.homMk j : Over.mk (j ≫ X.hom) ⟶ X`, a point
  `x : T ⟶ X` lifts through `j` exactly when it factors through `Over.homMk j` in `Over S`.
- `isIso_of_diagonalizableCoreCase`: under `DiagonalizableCoreCase`, every torsion-closed
  immersion into the underlying scheme of `(Diagonalizable.groupScheme R Λ).toGrp` is an
  isomorphism, by `lifts_iff_exists_overHom`.
- `splitAffineCase_of_diagonalizableCoreCase`: `DiagonalizableCoreCase` implies
  `SplitAffineCase`, by `isIso_of_iso` along the published isomorphism
  `Diagonalizable.relativeModelIso R Λ : (groupScheme R Λ).toGrp ≅ diagonalizable (Spec R) Λ`.
- `isIso_of_cover`: let `𝒰` be an fppf cover of `S` and suppose that over each member
  `𝒰.X i` the base change of `G` is isomorphic to a group `D i` all of whose torsion-closed
  immersions are isomorphisms. Then every torsion-closed immersion `j` into `G` is an
  isomorphism. Proof: the base change of `j` to `𝒰.X i` is torsion-closed
  (`IsTorsionClosed.baseChange`) and an immersion, so the identity point lifts through it
  (`lifts_id_of_iso`); by fppf descent (`lifts_id_of_cover`) the identity point of `G`
  lifts through `j`, and `j` is an isomorphism (`isIso_of_lifts_id`).
- `diagonalizable_case`: `SplitAffineCase` implies the same for `D_S(Λ)` over an arbitrary
  scheme `S`: apply `isIso_of_cover` to the affine open cover `S.affineOpenCover` (open
  immersions are flat and locally of finite presentation) with the published isomorphisms
  `diagonalizableBaseChangeIso`, which identify the base change of `D_S(Λ)` to an affine
  open `Spec R` with `D_{Spec R}(Λ)`.
- `torsionClosedImmersionIsIso_of_splitAffineCase`: `SplitAffineCase` implies
  `TorsionClosedImmersionIsIso`. For `G` of multiplicative type, `IsMultiplicativeType`
  supplies an fppf cover over whose members `G` becomes isomorphic to some `D_{𝒰.X i}(Λᵢ)`;
  apply `isIso_of_cover` with `diagonalizable_case`.
- `statement_of_diagonalizableCoreCase`: `DiagonalizableCoreCase.{u}` implies
  `MultiplicativeTypeTorsionDeterminationStatement.{u}`, composing the above with
  `statement_of_torsionClosedImmersionIsIso` from [`Assembly`](Assembly.md).

## Source

The reduction follows the shape of SGA 3, Exposé IX (Gille–Polo recomposed edition,
registered as `sga3-expose-ix-gille-polo-2009`), proof of Théorème 4.7 b), p.47: locally on
`S` there is a faithfully flat base change over which `G` becomes diagonalizable, and the
assertion descends. Here the cover is the fppf cover given by
`RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, *Reductive group schemes*,
Definition B.1.1), followed by a Zariski cover reducing to affine bases, and what descends
is the existence of a lift of the identity point through a monomorphism.

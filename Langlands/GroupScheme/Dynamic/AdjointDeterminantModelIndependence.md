# Independence of the adjoint determinant character from the represented models: proof

This module proves the published proposition
`Langlands.GroupScheme.Dynamic.AdjointDeterminantModelIndependenceStatement`
([AdjointDeterminantModelIndependenceStatement](AdjointDeterminantModelIndependenceStatement.md))
as the theorem

`Langlands.GroupScheme.Dynamic.adjointDeterminantModelIndependence :
  AdjointDeterminantModelIndependenceStatement.{u}`.

The theorem keeps every binder of the statement. It uses no hypothesis beyond
the statement's own: no relation between the coordinates `c` and `c'`, no
equality `d = d'`, and no condition on `R`, `G` or `χ`. The only axioms used
are `propext`, `Classical.choice` and `Quot.sound`.

## Idea

The proof never looks at coordinate matrices. On a point `h` of the acting
group with coefficients in an `R`-algebra `A`, the published lemma
`AutomorphicAction.determinantCharacter_affinePoints`
(`Langlands.GroupScheme.Lie.ActionDeterminant`) gives the value of
`a.determinantCharacter c` as the unit `LinearEquiv.det (a.differential h)` of
`A`. Here `a.differential h` is the linear automorphism of the actual Lie kernel
`Additive (lieKernel U A)` induced by the action. This value does not mention
`c`. So it suffices to show three things:

1. a rational character of an affine group scheme is determined by its values
   on points over `R`-algebras;
2. the canonical isomorphism `U ≅ U'` of the two models of `U(χ)` induces an
   `A`-linear isomorphism of their Lie kernels;
3. under this isomorphism the differential of the action on the second model at
   the image point is conjugate to the differential of the action on the first
   model, so the two determinants agree by `LinearEquiv.det_conj`.

The sections below follow the Lean file.

## 1. Characters are determined on affine points

`rationalCharacters_ext_affinePoints`: let `H` be a group scheme over `Spec R`
with `IsAffine H.X.left`, and let `χ ψ : rationalCharacters H`. If
`p ≫ χ.toMul.hom.hom = p ≫ ψ.toMul.hom.hom` for every commutative `R`-algebra
`A` and every point `p : H.affinePoints A`, then `χ = ψ`.

Proof. By the published `hom_ext_points` it suffices to compare the two
characters on every point `x : T ⟶ H.X` over every `T : Over (Spec R)`.
Mathlib's `essImage_algSpec` gives an `R`-algebra `B` and an isomorphism
`e : (algSpec R).obj (op B) ≅ H.X`, because `H.X.left` is affine. Write
`x = (x ≫ e.inv) ≫ e.hom` and apply the hypothesis to the point `e.hom`.

## 2. The Lie kernel isomorphism

`lieKernelLinearEquiv e A`: for group schemes `U`, `U'` over `Spec R` with
affine structure maps, an isomorphism `e : U ≅ U'` and an `R`-algebra `A`,
this is the `A`-linear equivalence
`Additive (lieKernel U A) ≃ₗ[A] Additive (lieKernel U' A)` whose forward map is
the published `Lie.targetMapLinear e.hom A` and whose inverse is
`Lie.targetMapLinear e.inv A` (`Langlands.GroupScheme.Lie.KernelTargetMaps`).
The two maps are inverse because `e.hom ≫ e.inv = 𝟙` and `e.inv ≫ e.hom = 𝟙`.
The simp lemmas `lieKernelLinearEquiv_val` and `lieKernelLinearEquiv_symm_val`
record that both maps are composition with `e.hom.hom.hom` and
`e.inv.hom.hom`, respectively.

## 3. Intertwined actions have equal determinant characters

In the namespace `AutomorphicAction`, fix actions
`a : AutomorphicAction H U` and `a' : AutomorphicAction H' U'`, a homomorphism
`φ : H ⟶ H'` and an isomorphism `e : U ≅ U'`. The intertwining hypothesis is

`he : ∀ T (h : T ⟶ H.X) (x : T ⟶ U.X),
  a'.act (h ≫ φ.hom.hom) (x ≫ e.hom.hom.hom) = a.act h x ≫ e.hom.hom.hom`.

* `differential_comp_eq_conj`: under `he`, for every `R`-algebra `A` and every
  point `h : Lie.AffinePoints H A`,

  `a'.differential (h ≫ φ.hom.hom) =
    ((lieKernelLinearEquiv e A).symm.trans (a.differential h)).trans
      (lieKernelLinearEquiv e A)`.

  Both sides are compared on a kernel element `x`. The differential acts
  through the constant dual-number point `Lie.constant`, and
  `Lie.constant H' (h ≫ φ.hom.hom) = Lie.constant H h ≫ φ.hom.hom`. Writing
  `x = (x ≫ e.inv) ≫ e.hom` and applying `he` gives the claim.
* `det_differential_comp`: hence
  `LinearEquiv.det (a'.differential (h ≫ φ.hom.hom)) =
    LinearEquiv.det (a.differential h)`, by Mathlib's `LinearEquiv.det_conj`.
  This holds for any modules; no finiteness is needed here.
* `characterRestrict_determinantCharacter_of_intertwining`: if moreover `H.X.left` and
  `H'.X.left` are affine, then for any finite coordinates
  `c : Lie.FiniteCoordinates U d` and `c' : Lie.FiniteCoordinates U' d'`,

  `characterRestrict φ (a'.determinantCharacter c') = a.determinantCharacter c`.

  By section 1 it suffices to compare values on a point `p : H.affinePoints A`.
  The left side at `p` is `a'.determinantCharacter c'` at `p ≫ φ.hom.hom`
  (`characterRestrict_apply`). The identification
  `Gm.affinePointsEquiv` of points of `𝔾_m` with units of `A` is injective.
  Under it, `determinantCharacter_affinePoints` turns both values into the
  determinants of `det_differential_comp`.
* `act_comp_of_conj`: the hypothesis `he` holds when both actions are
  conjugation inside a common group scheme `G`. Precisely, suppose
  `iH : H ⟶ G`, `iH' : H' ⟶ G`, `iU : U ⟶ G`, `iU' : U' ⟶ G` with
  `iU'.hom.hom` a monomorphism, `a` and `a'` satisfy
  `a.act h x ≫ iU.hom.hom = (h ≫ iH.hom.hom) * (x ≫ iU.hom.hom) * (h ≫ iH.hom.hom)⁻¹`
  and the analogous identity for `a'`, and `φ ≫ iH' = iH`, `e.hom ≫ iU' = iU`.
  Then `he` holds. Both sides of `he` are compared after composing with the
  monomorphism `iU'.hom.hom`.

## 4. The theorem

`adjointDeterminantModelIndependence` introduces the statement's data. The
monomorphism `iU'.hom.hom` comes from `hU'.1`. Both parts are instances of
`characterRestrict_determinantCharacter_of_intertwining` with `e = isoOfIsRepresentedBy hU hU'`:

* **Parabolic.** Take `a = parabolicAdjointAction hP hU`,
  `a' = parabolicAdjointAction hP' hU'` and
  `φ = (isoOfIsRepresentedBy hP hP').hom`. The published
  `adjointDeterminantCharacter hP hU c` is by definition
  `(parabolicAdjointAction hP hU).determinantCharacter c`. The hypothesis `he`
  comes from `act_comp_of_conj`, using `parabolicAdjointAction_act_comp` for
  both models and `isoOfIsRepresentedBy_hom_comp` for `P` and for `U`.
* **Centralizer.** The same argument with `centralizerAdjointAction hZ hU`,
  `centralizerAdjointAction hZ' hU'`, `φ = (isoOfIsRepresentedBy hZ hZ').hom`
  and `centralizerAdjointAction_act_comp`.

## Imports

The module imports the statement module and
`Langlands.GroupScheme.Lie.KernelTargetMaps`, which provides
`Lie.targetMapLinear`.

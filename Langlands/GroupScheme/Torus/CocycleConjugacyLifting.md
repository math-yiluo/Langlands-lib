# Nilpotent lifting of conjugacies between diagonalizable cocycles

Throughout, `R` is a commutative ring, `M` an additive commutative group, and
`D(M) = Diagonalizable.groupScheme R M`. `G` is a group scheme over `Spec R`
whose underlying scheme is affine. `a` is an `AutomorphicAction` of `D(M)` on
`G`. `C` is an `R`-algebra, and `cx`, `cy` are actual cocycles of `a` over a
test object `T`, eventually the affine test `Spec C = (algSpec R).obj (op C)`.
The main theorem, `CharacterAction.exists_conjugate_lift`, lifts a point of `G`
that conjugates `cx` to `cy` modulo a nilpotent ideal of `C` to such a point
over `C`. Conjugation is the published `AutomorphicAction.Cocycle.conjugate`,
`(g · c)(h) = g c(h) a_h(g⁻¹)`. The coordinate algebra of `G` must be formally
smooth over `R`.

## Coordinates after base change

These definitions use the published base-change helpers of `TwistedLifting`:
`baseRing C`, `baseChange C A = C ⊗[R] A`, `restrictScalars C D`,
`restrictScalarsMap`, `toRestrict D` and `baseChangeEquiv D`. They also use the
affine point bijection `AffineCoordinates.pointEquiv` of
`AffineCharacterAction`. Write `A = AffineCoordinates.algebra G`.

* `coordinatePoint p` is the point of `G` over `Spec (restrictScalars C D)`
  given by a `C`-algebra map `p : C ⊗[R] A → D`. `ofCoordinatePoint` is its
  inverse. `coordinatePoint_ofCoordinatePoint` and `coordinatePoint_injective`
  record this. `coordinatePoint_comp` is naturality in `D`.
* `structurePoint D` is the morphism `Spec (restrictScalars C D) ⟶ Spec C`
  induced by the structure map `toRestrict D`. `map_structurePoint` is its
  compatibility with maps of `C`-algebras.

## The twisted action on points

`twistedPoint a cx cy b h g` is `cy(h) · a_h(g) · cx(h)⁻¹`. Here `b : V ⟶ T` is
a test over `T`, `h` is a point of `D(M)` over `V`, `g` is a point of `G` over
`V`, and `cx(h)`, `cy(h)` are `Cocycle.eval` at `b` and `h`.

* `twistedPoint_naturality`: it commutes with precomposition by any `V' ⟶ V`.
* `twistedPoint_eq_iff`: for `g : T ⟶ G.X`, the point `b ≫ g` is fixed by `h`,
  `twistedPoint a cx cy b h (b ≫ g) = b ≫ g`, exactly when
  `(conjugate g cx).eval b h = cy.eval b h`. This is the group identity
  `y z x⁻¹ = g ↔ g x z⁻¹ = y` with `z = a_h(g)`, together with
  `a_h(g⁻¹) = a_h(g)⁻¹`.
* `twistedPoint_restrict`: restricting both cocycles along `b' : T' ⟶ T` is the
  same as composing the test with `b'`.

## Cocycles over affine tests

`cocycle_ext_affine` proves that two cocycles `c`, `d` over `Spec C` are equal
when the following holds. For every `R`-algebra map `φ : C ⟶ D` and every
character `t : Multiplicative M →* Dˣ`, they agree when evaluated at
`Spec φ : Spec D ⟶ Spec C` and at the point `characterPoint t` of `D(M)`. The
product `Spec C × D(M)` over `Spec R` is affine, so it is `Spec D` for some
`R`-algebra `D` up to an isomorphism `e`. Its projections are `Spec φ` for some
`φ` and a character `t`, read off through the corepresentation of `D(M)`.
Evaluating at these gives `e.hom ≫ c.hom = e.hom ≫ d.hom`, and `e.hom` is an
epimorphism.

## The twisted character action on `C ⊗[R] A`

`cocycleAction a cx cy` is a character action, in the published sense
`CharacterActionGrading.Action` over the base ring `C`, on `C ⊗[R] A`. Here
`cx`, `cy` are cocycles over `Spec C`. A character `t` over a `C`-algebra `D`
sends a point `p` to the point with
`coordinatePoint = twistedPoint a cx cy (structurePoint D)
(characterPoint (restrictChar t)) (coordinatePoint p)`
(`coordinatePoint_cocycleAction`). The laws are checked after
`coordinatePoint_injective`:

* the unit law, from `Cocycle.eval_one` and `act_one_left`;
* the composition law, from `Cocycle.eval_mul`, `act_mul_left`, `act_mul_right`
  and `act_inv`, followed by `group`;
* naturality, from `twistedPoint_naturality`, `map_structurePoint` and the
  naturality of `characterPoint` and `restrictChar`.

## The lifting theorem

`exists_conjugate_lift` assumes `Algebra.FormallySmooth R A`, a nilpotent ideal
`I` of `C`, and a point `g₀ : Spec (C ⧸ I) ⟶ G.X`. It also assumes that `g₀`
conjugates the restriction of `cx` along `π : Spec (C ⧸ I) ⟶ Spec C` to the
restriction of `cy`. It produces `g : Spec C ⟶ G.X` with `π ≫ g = g₀` and
`conjugate g cx = cy`.

1. View `C ⧸ I` as a `C`-algebra. Let `x₀ : C ⊗[R] A → C ⧸ I` correspond to
   `g₀` through `ofCoordinatePoint` and `restrictIso`. It is fixed by
   `cocycleAction` after every refinement `f` to a `C`-algebra `D`. The test
   `Spec D ⟶ Spec (C ⧸ I) ⟶ Spec C` is `structurePoint D`. Hence
   `twistedPoint_eq_iff`, the hypothesis on `g₀` and `twistedPoint_restrict`
   give the fixed equation.
2. `C ⊗[R] A` is formally smooth over `C` by Mathlib's base-change instance. The
   published `CharacterAction.exists_fixed_lift` of `FixedPointLifting`, by
   Worker 1296, therefore gives a lift `y : C ⊗[R] A → C`. It is fixed after
   every refinement and reduces to `x₀`.
3. Set `g` to be `coordinatePoint y`, transported to `Spec C` by `restrictIso`.
   Naturality of `coordinatePoint` gives `π ≫ g = g₀`.
4. For `conjugate g cx = cy`, apply `cocycle_ext_affine`. Given `φ : C ⟶ D` and
   a character `t` over `D`, view `D` as a `C`-algebra through `φ`. Fixedness of
   `y` along `C → D` at `t` is a twisted fixed equation. Rewriting it with
   `twistedPoint_naturality` and the identifications of `restrictIso` turns it
   into the twisted fixed equation at `Spec φ` and `characterPoint t`. By
   `twistedPoint_eq_iff` this is the required equality of evaluations.

## Provenance

This is an internal construction for the proof of
`Langlands.GroupScheme.Diagonalizable.CocycleModelActionRelationSmoothStatement`.
It follows the relative fixed-point step of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), proof of Proposition A.8.12,
printed p.554 (PDF p.580). That proof makes the acting group act on the first
factor of `G × X × X` and applies Proposition A.8.10(2), printed pp. 547–550
(PDF pp. 573–576). The source is registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Here the action is written on points of `G` over `C`-algebras, with the cocycles
fixed, rather than on the product scheme. Its fixed equation is the conjugacy
equation. The infinitesimal lifting of fixed points is the published square-zero
argument behind `CharacterAction.exists_fixed_lift`, applied after base change
to `C`. The same pattern appears in the published `TwistedLifting`, for twisted
transporters. No finiteness of `M`, condition on torsion, or field hypothesis is
used.

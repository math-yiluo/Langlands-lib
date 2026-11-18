# Characters of a diagonalizable group acting on character-valued points

Namespace: `Langlands.GroupScheme.Cartier.DiagonalizableCharacters`.

Let `S : Scheme.{u}` be any scheme and `M : Type u` any additive commutative
group. No finiteness hypothesis on `M` and no hypothesis on `S` is used in this
module. It sets up the points-level calculus that later identifies the Cartier
characters of `D_S(M)` with locally constant `M`-valued functions.

## The model

- `model S M : CommGroupScheme S` (an `abbrev`) is
  `(CommGroupScheme.baseChange (Gm.toSpecZ S)).obj
  (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) M)`. This is the
  diagonalizable model fixed by the task. Its underlying group scheme is
  definitionally `RelativeMultiplicativeType.diagonalizable S M`, as an
  `example` in the file checks by `rfl`.

## Points of the base change to a test scheme

For `T : Over S` and a scheme `V` over `T.left`:

- `testPointsEquiv M T V` is a multiplicative equivalence between the
  `V`-points of `testBaseChange T (model S M)` (the base change of `D_S(M)` to
  `T.left`) and the group `Multiplicative M →* Γ(V.left, ⊤)ˣ`. It composes the
  pullback adjunction `baseChangePointsEquiv T.hom` with the Library's
  `RelativeMultiplicativeType.pointsEquiv S M` at `V` regarded over `S`.
- `testPointsEquiv_apply` unfolds the definition.
- `testPointsEquiv_naturality` and `testPointsEquiv_symm_naturality` say that
  pulling back a point along `b : V' ⟶ V` acts on the homomorphism by
  composing with `Units.map b.left.appTop`.

## The action of a character

A Cartier character over `T` is an element
`χ : (characters (model S M)).obj (op T)`, that is, a homomorphism of
commutative group schemes over `T.left` from the base change of `D_S(M)` to the
base change of `𝔾_{m,S}`.

- `act χ V : (Multiplicative M →* Γ(V.left, ⊤)ˣ) →* Γ(V.left, ⊤)ˣ` takes the
  point corresponding to `t` under `testPointsEquiv`, composes it with `χ`, and
  reads off the resulting unit with `Gm.baseChangeUnitsEquiv T.hom V`.
  `act_apply` unfolds this.
- `act_naturality`: for `b : V' ⟶ V` over `T.left`,
  `act χ V' ((Units.map b.left.appTop.hom.toMonoidHom).comp t) =
  Units.map b.left.appTop.hom.toMonoidHom (act χ V t)`.
- `act_ext`: two characters with the same action on every `V` and every `t`
  are equal. The proof uses Yoneda (`hom_ext_points`).
- `act_add` and `act_zero`: the action of a sum of characters is the pointwise
  product of the actions, and the action of `0` is `1`.
- `act_restrict`: for `a : T' ⟶ T` over `S` and `V` over `T'.left`, the action
  of the Cartier restriction `(characters (model S M)).map a.op χ` on `V` equals
  the action of `χ` on `V` regarded over `T.left` through `a.left`
  (`(Over.map a.left).obj V`). The proof uses the Library lemmas
  `baseChangePointsEquiv_restrictPointsEquiv` and
  `baseChangePointsEquiv_restrict`.

## Evaluation characters

- `globalEval S m : model S M ⟶ Gm S` is the global evaluation character at
  `m : M`. It is the base change along `Gm.toSpecZ S` of the Library character
  `DiagonalizableCharacter.evalCharacter ZU M m`, which is the monomial
  evaluation `t ↦ t(m)` of the group-algebra model over `Spec ℤ`, composed with
  the canonical isomorphism `Gm.commBaseChangeIso (Gm.toSpecZ S)`.
- `globalEval_apply`: for every `V : Over S` and every point `x` of
  `diagonalizable S M` over `V`, the unit of the composite
  `x ≫ globalEval S m` is `pointsEquiv S M V x (ofAdd m)`.
- `evalChar T m : (characters (model S M)).obj (op T)` is the base change of
  `globalEval S m` to `T`. These are the evaluation characters of the
  diagonalizable model over every test scheme.
- `act_evalChar`: `act (evalChar T m) V t = t (ofAdd m)`.
- `restrict_evalChar`: Cartier restriction along `a : T' ⟶ T` sends
  `evalChar T m` to `evalChar T' m`. This is the Library lemma
  `restrict_baseChange_map`.
- `evalChar_add` and `evalChar_zero`: `m ↦ evalChar T m` is additive.
- `eq_evalChar_iff`: `χ = evalChar T m` if and only if
  `act χ V t = t (ofAdd m)` for all `V` and `t`.

## Characters from natural actions

- `IsNaturalAct φ` is a `Prop`-valued predicate on a family
  `φ V : (Multiplicative M →* Γ(V.left, ⊤)ˣ) →* Γ(V.left, ⊤)ˣ` indexed by
  schemes `V` over `T.left`. It holds when `φ` satisfies the same naturality
  formula as `act_naturality`. `isNaturalAct_act` says that `act χ` is natural.
- `ofActPoints φ V` is the homomorphism of `V`-points obtained by transporting
  `φ V` through `testPointsEquiv` and `Gm.baseChangeUnitsEquiv`.
  `baseChangeUnitsEquiv_ofActPoints` computes it, and `ofActPoints_naturality`
  proves its naturality from `IsNaturalAct φ`.
- `ofAct φ hφ` is the character over `T` built from these homomorphisms of
  points with the Library's `homOfPoints`. `comp_ofAct` is its defining
  property on points.
- `act_ofAct`: `act (ofAct φ hφ) V t = φ V t`. `ofAct_act`: `ofAct (act χ) _ = χ`.
  So characters over `T` correspond bijectively to natural actions on
  character-valued points.

## Provenance

This module is internal infrastructure, derived from the functor-of-points
description of `D_S(M)`: a `V`-point of `D_S(M)` is a group homomorphism
`M → Γ(V, 𝒪_V)ˣ`, and `𝔾_m(V) = Γ(V, 𝒪_V)ˣ` (SGA 3, Exposé I, §4.4 and
Exposé VIII, §1). All identifications used are the Library's existing point
equivalences. No new mathematical claim beyond the formulas stated above is
made.

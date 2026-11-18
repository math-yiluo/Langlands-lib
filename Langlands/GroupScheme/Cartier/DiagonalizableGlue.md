# Characters of `D_S(M)` from locally constant functions

Module `Langlands.GroupScheme.Cartier.DiagonalizableGlue`, namespace
`Langlands.GroupScheme.Cartier.DiagonalizableCharacters`.

## Purpose and provenance

This is an internal step of Task 7697, the canonical natural isomorphism between
the Cartier character presheaf of the diagonalizable group `D_S(M)` and the
constant presheaf with coefficients `M`. It builds one direction, `Φ`: a locally
constant function `f : T → M` on an `S`-scheme `T` gives a character of `D_S(M)`
over `T`. Informally, on a point of `D_S(M)` over `v : V → T`, which is a
homomorphism `t : M → Γ(V, 𝒪_V)ˣ`, the character takes the value `t (f (v x))`
near each point `x` of `V`.

This is the classical description of characters of a diagonalizable group over a
non-connected base. Over a connected base, characters of `D_S(M)` are the
evaluations `t ↦ t(m)`. In general they are locally constant families of such
evaluations. The Lean development is internal to this task. It combines two
helper modules:

- `Langlands.GroupScheme.Cartier.DiagonalizablePoints` (Worker 934): the model
  `model S M` of `D_S(M)`, the action `act χ V` of a character on
  character-valued points, `act_ext`, `act_add`, `act_zero`, `act_restrict`,
  `evalChar`, `eq_evalChar_iff`, `IsNaturalAct`, `ofAct` and `act_ofAct`.
- `Langlands.AlgebraicGeometry.LocallyConstantUnitPower` (Worker 158): the glued
  unit `lcPow t f` and its API.

Throughout, `S : Scheme.{u}`, `M : Type u` is an additive commutative group,
which need not be finitely generated, and `T : Over S`.

## Declarations

- `lcPowHom f : (Multiplicative M →* Γ(X, ⊤)ˣ) →* Γ(X, ⊤)ˣ`, for a scheme `X`
  and `f : LocallyConstant X M`, is `t ↦ lcPow t f`. It is a monoid homomorphism
  by `lcPow_one` and `lcPow_mul`. `lcPowHom_apply` unfolds it.
- `comap_comp_base`: pulling a locally constant function back along `g ≫ h` is
  pulling back along `h` and then along `g`. This holds by `rfl`.
- `isNaturalAct_lcPowHom f`: the family `V ↦ lcPowHom (f.comap V.hom.base.hom)`,
  over schemes `V` over `T.left`, satisfies `IsNaturalAct`. Proof: let
  `b : V' ⟶ V` be a morphism over `T.left`. `lcPow_naturality` turns the pullback
  along `b.left` of `lcPow t (f ∘ V.hom)` into `lcPow` of the pulled-back
  character along `f ∘ V.hom ∘ b.left`. Then `Over.w b` gives
  `b.left ≫ V.hom = V'.hom`.
- `ofLocallyConstant f`, for `f : LocallyConstant T.left M`, is the character
  `ofAct (fun V => lcPowHom (f.comap V.hom.base.hom)) (isNaturalAct_lcPowHom f)`.
  This is the map `Φ`.
- `act_ofLocallyConstant`: `act (ofLocallyConstant f) V t = lcPow t (f.comap V.hom.base.hom)`.
  This is `act_ofAct`.
- `ofLocallyConstant_add` and `ofLocallyConstant_zero`: `Φ` is additive. Proof:
  apply `act_ext`, then use `act_add` or `act_zero` together with `lcPow_add` or
  `lcPow_zero`. Pullback of locally constant functions is additive by definition.
- `ofLocallyConstantHom M T : LocallyConstant T.left M →+ (characters (model S M)).obj (op T)`
  bundles `Φ` as an additive homomorphism. `ofLocallyConstantHom_apply` unfolds
  it.
- `ofLocallyConstant_const T m`: the constant function `m` gives `evalChar T m`.
  Proof: `eq_evalChar_iff` and `lcPow_const`.
- `restrict_ofLocallyConstant a f`, for `a : T' ⟶ T` in `Over S`: Cartier
  restriction `(characters (model S M)).map a.op` takes `ofLocallyConstant f` to
  `ofLocallyConstant (f.comap a.left.base.hom)`. Proof: `act_ext` and
  `act_restrict`. On the right, the point over `V` is pulled back along
  `V.hom ≫ a.left`, which is the same function.
- `restrict_ofLocallyConstant_eq_evalChar a f m h`: if `f (a.left x) = m` for
  every `x`, the restriction of `ofLocallyConstant f` along `a` is
  `evalChar T' m`. This follows from the previous two lemmas.

## Remarks

- There are no `sorry`s and no new axioms. The axioms used are `propext`,
  `Classical.choice` and `Quot.sound`.
- The inverse direction (characters to locally constant functions, using local
  rigidity), the two composite identities, the natural isomorphism, and the
  evaluation-character formulas are in Worker 934's modules for the same task.

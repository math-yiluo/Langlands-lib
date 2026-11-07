# Transporting an absolute presheaf representative to its original base

Author: Worker 336.

This is an internal categorical support construction. It supplies the
original-base transport used when a representability argument temporarily
forgets a scheme's map to its base. The construction uses only Yoneda,
functoriality and fibres of maps of types; it is not a transcription of a
literature theorem. Its provenance is the original-base obligation in the
quasi-affine-source AF representability task.

## Objects and universes

Fix an arbitrary universe `u` and an arbitrary scheme `S : Scheme.{u}`.
`Presheaf S` is the existing category of functors from `(Over S)ᵒᵖ` to
`Type (u + 1)`. `AbsolutePresheaf` is the category of functors from
`Scheme.{u}ᵒᵖ` to the same value universe. Both use the existing lifted
Yoneda functors, so the constructions require no universe reduction or
restriction on the class of scheme tests.

Given an absolute presheaf `A` and a natural transformation
`s : A ⟶ uliftYoneda.obj S`, `fiberPresheaf s` sends a scheme
`U` over `S` to the subtype of sections `x` of `A` on `U.left` for which
`s(x)` is the specified structure map `U.hom` (lifted into the value
universe). Its restriction map is the restriction of `A` on the underlying
scheme morphism. The naturality of `s` and the equation defining a morphism
in `Over S` ensure that restriction stays in the fibre.

## Transport of an absolute representative

Suppose `P : Scheme.{u}` and
`e : uliftYoneda.obj P ≅ A`. `structureMap e s : P ⟶ S` is the
unique scheme map whose Yoneda image is `e.hom ≫ s`. The lemma
`structureMap_yoneda` records exactly this equation, using the full
faithfulness of the lifted Yoneda functor. `representativeOver e s` is
`P` equipped with this map to `S`; its underlying scheme remains `P`.

`toFiber e s` sends a relative point `f : U ⟶ representativeOver e s`
to `e(f.left)`. The Yoneda equation shows that this section lies in the
specified fibre. The transformation is natural by naturality of `e.hom`.
The lemma `toFiber_bijective` proves bijectivity on every relative test:
injectivity follows from the componentwise injectivity of `e.hom` and
extensionality of maps over `S`; a fibre section `x` lifts by `e.inv` to a
map into `P`, and its fibre equation verifies compatibility with `S`.
Consequently `fiberIso e s` is an isomorphism

```
(schemeYoneda S).obj (representativeOver e s) ≅ fiberPresheaf s.
```

## Recovering an arbitrary relative presheaf

For any `F : Presheaf S`, `totalPresheaf F` is the absolute presheaf
whose sections on a scheme `X` are pairs

```
(t : X ⟶ S, x : F.obj (op (Over.mk t))).
```

Restriction along `a : X' ⟶ X` changes `t` to `a ≫ t` and restricts
`x` along the corresponding morphism over `S`. The functor laws account
for the equality of the structure maps using `eqToHom`; they then follow
from the functor laws of `F`. `totalToBase F` projects a pair to the
lifted structure map `t`.

`toTotalFiber F` sends a relative section over `U` to the pair
`(U.hom, x)` in the fibre of `totalToBase F`. Its naturality again uses
the equation defining a map over `S`, together with the action of `F`
on the corresponding equality morphisms. On each test it is bijective:
the fibre equation identifies the first coordinate with `U.hom`, after
which the second coordinate is exactly a section of `F`. The resulting
isomorphism is `totalFiberIso F : F ≅ fiberPresheaf (totalToBase F)`.

The final interface `representationOver` composes these two isomorphisms.
If `e : uliftYoneda.obj P ≅ totalPresheaf F`, it gives

```
(schemeYoneda S).obj (representativeOver e (totalToBase F)) ≅ F.
```

This is a natural isomorphism of entire presheaves on all schemes over
the original `S`. Any property of the underlying representing scheme
`P`, such as finite affine neighbourhoods, remains a property of this
same underlying scheme after it is equipped with its structure map.

## Scope

No sheaf, algebraic-space, compactness, separation, finiteness, affine,
quasi-affine or Noetherian hypothesis is used. The input absolute
representing isomorphism is assumed. The module constructs the relative
representer and the comparison isomorphism; it supplies no approximation
theorem or representability existence theorem for algebraic spaces.
In particular it does not prove the host task's unconditional
`FiniteSurjectiveQuasiAffineSourceAFStatement`, nor does it establish
relative-to-absolute comparison of geometric properties.

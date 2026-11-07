# Actual field extension of supplied Steinberg products

Worker 1317. This internal construction is derived from the actual pinning,
normalized-root-map, normalizer and character-lattice base-change APIs, the
standard vector-source comparison, and the published class-function quotient
descent result. It makes no new literature claim.

Let `k` and `F` be arbitrary fields in the same arbitrary universe `u`, with
`Algebra k F` and `Algebra.IsAlgebraic k F`. Let `G` be an actual affine group
scheme over `k` and `p : SplitPinning G` a supplied split pinning. In particular,
`p` contains connected reductivity, a split maximal torus, its actual root datum
and base, and the Lie pinning. Write `bc = algebraBaseMap k F` and `GF` for the
actual pullback of `G`. Algebraicity is retained by the assembled
`p.baseChange` interface; no assumption on the characteristic, perfectness,
infinitude or algebraic closedness of `k` is imposed.

`SimpleReflectionRepresentative.fieldBaseChange` transports a supplied
representative `n` at a simple root `a` to the corresponding simple index
`p.baseChangeSimpleEquiv a`. Its point is exactly
`baseChangeBasePoint bc G n.point`; its torus automorphism is the actual
base-change functor applied to `n.torusAut`. The existing base-change theorem
for normalizing points supplies normalization on all scheme tests. The
character-action identity follows by writing each new character in the
canonical base-change lattice equivalence and using compatibility of both
the actual character automorphism and the root reflection with base change.
Thus the original representative is retained; no new representative is chosen.

`fieldBaseChangeRootMaps` and `fieldBaseChangeRepresentatives` transport the
supplied families through the same simple-index equivalence. At the image of
each original index their values equal its transported supplied datum, as
recorded by the two `_apply` lemmas. For any supplied order
`e : Fin r ≃ p.base.support`, `fieldBaseChangeOrder e` is its composition with
that simple-index equivalence. It retains the increasing `Fin r` order.

`fieldBaseChange_steinbergProductPoint` states the comparison on every scheme
test `T` over `F`, for every family of global functions
`c : Fin r → Γ(T.left, ⊤)`. Applying `baseChangePointsEquiv bc G T` to the
product for the transported data gives exactly the original supplied product
on the same underlying scheme regarded over `k`, with the identical
parameters `c`. The implemented proof compares each ordered factor: the
normalized-root-map point comparison gives the original root value, and
`baseChangePointsEquiv_constantPoint` gives the original representative's
constant family. Multiplicativity then carries this equality through the
ordered finite list product. The statement includes rank zero and uses no
restriction to rational or affine test points.

`fieldBaseChange_steinbergProduct` is the actual morphism square:

```text
fieldBaseChangeIso(k,F,r).hom ≫ steinbergProduct(eF,xF,nF)
  = (Over.pullback bc).map (steinbergProduct(e,x,n)).
```

Here the comparison homomorphism is viewed as its underlying morphism in the
over category, and `eF`, `xF`, `nF` are the transported supplied data above.
The proof applies the injective pullback point equivalence at the entire
pulled-back standard source. The evaluation formula for `steinbergProduct`
and the standard source isomorphism's coordinate identity reduce the left
side to the preceding all-test product comparison. The underlying pullback
projection identity identifies the right side with composition by the original
product. This proves equality of scheme morphisms, rather than an equality
only on field-valued points.

Finally, `isIso_steinbergQuotient_baseChange_iff` gives

```text
IsIso (steinbergProduct(eF,xF,nF) ≫ ClassFunctions.rho GF)
  ↔ IsIso (steinbergProduct(e,x,n) ≫ ClassFunctions.rho G).
```

The quotient maps are the actual canonical maps to the fixed class-function
equalizer quotients. The proof substitutes the morphism square into
`isIso_steinbergQuotient_fieldExtension_iff` and cancels the standard source
isomorphism. That published theorem supplies the actual quotient base-change
comparison and fpqc reflection of isomorphisms. Neither simple connectedness
nor the desired quotient-isomorphism result is assumed in this equivalence.
It reduces the desired property to an algebraic extension of the supplied
data; proving that property over an algebraic closure remains a separate
obligation of the main split Steinberg quotient theorem.

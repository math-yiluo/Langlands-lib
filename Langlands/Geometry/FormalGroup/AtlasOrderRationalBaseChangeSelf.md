# Full-order naturality of the actual identity coefficient comparison

This is internal infrastructure derived from `AtlasOrderBaseChangeSelf`,
`AtlasRationalBaseChangeSelf` and `AtlasOrderRationalBaseChangeAlong`. It
rationalizes the existing actual full-order identity comparison and restricts
the ambient naturality equations to full-order maps. It makes no new
original-literature assertion.

Let `O` be a commutative ring, `R` a commutative `O`-algebra, `D` a ring
with a central `O`-algebra structure, and `F` a field `O`-algebra. Coordinate
types are finite and may differ; the original principal-open covers agree.
Coefficient tests have the universe of `R`. No division-algebra or maximal-order
condition on `D` is needed. Full-order rational Hom is the chartwise centralizer
inside the global tensor `F ⊗[O] BasicAtlas.Hom`, not the tensor of integral
full-order Hom.

`Hom.baseId_natural` and `baseId_inv_natural` prove the two squares

```text
E'.baseIdHom ∘ (f extended along id) = f ∘ E.baseIdHom,
(f extended along id) ∘ E.baseIdInv = E'.baseIdInv ∘ f.
```

These are equalities of actual full-order formal atlas maps. Subtype
extensionality reduces them to the existing ambient equations; the forgetful
laws identify the underlying comparison and coefficient-extended maps.
Identity extension retains the supplied scalar structure.

`RationalHom.baseId_natural` and `baseId_inv_natural` prove the same two
equations for every full-order rational map, with rationalizations of the
actual integral comparisons. Their proofs use extensionality of the centralizer,
the forgetful laws for rationalization, composition and supplied-target
extension, and the ambient rational naturality equations applied to the
underlying global tensor. They require neither tensor generation by integral
full-order maps nor detection of global tensors by chart evaluation.

Under the additional assumptions `IsDomain O` and `IsFractionRing O F`,
`baseIdQuasiIsogeny E` is `QuasiIsogeny.ofIso E.baseIdIso`. It rationalizes
both actual full-order comparison maps and retains their two inverse equations.
Its `hom` and `inv` lemmas give these rationalizations explicitly;
`baseIdQuasiIsogeny_toAtlas` identifies the entire forgotten quasi-isogeny with
the ambient `X.baseIdQuasiIsogeny`.

`QuasiIsogeny.baseId_natural` and `baseId_inv_natural` give the corresponding
two squares of full-order quasi-isogenies. Their forward maps satisfy the
rational naturality equations, and uniqueness of a two-sided inverse proves
equality of the entire quasi-isogenies.

The results concern the specified actual identity comparison. This module
does not assert strict atlas equality, independence of arbitrary comparisons,
successive-extension coherence, local rational gluing, heights, framing,
polarization, descent, levels or representability.

# Full-order rational comparison of successive supplied coefficient maps

This is internal infrastructure derived from
`AtlasOrderBaseChangeAlongComposition`, `AtlasOrderRationalBaseChangeAlong`
and `AtlasRationalBaseChangeAlongComposition`. It rationalizes the existing
actual full-order comparison and restricts the ambient naturality equations
to full-order maps. It makes no additional original-literature assertion.

Let `O`, `R`, `S` and `T` be commutative rings, with supplied `O`-algebra
structures on `R`, `S` and `T`, and let `f : R →ₐ[O] S` and
`g : S →ₐ[O] T`. The three base rings have the same universe. Let `D` be any
central `O`-algebra and `F` a field with an `O`-algebra structure. The original
atlases may have different finite coordinate types and have equal principal
covers. Full-order rational Hom is the chartwise `D`-centralizer inside the
global tensor `F ⊗[O] BasicAtlas.Hom`.

`Hom.baseAlongComp_natural` states that extending an integral full-order map
along `f` and then `g`, followed by the target's actual successive-to-direct
comparison, equals applying the source's comparison and then extending the
map along `g.comp f`. `Hom.baseAlongComp_inv_natural` gives the reverse
square. The comparisons are the two maps stored in the existing
`E.baseAlongCompIso f g`. Thus both supplied scalar structures and the actual
preimage-chart choices are retained. Subtype extensionality and the
comparison and extension forgetful laws reduce each equation to the ambient
integral naturality law.

`RationalHom.baseAlongComp_natural` and `baseAlongComp_inv_natural` give
the same two squares for every element of the full-order rational
centralizer. The comparison maps are rationalizations of the actual integral
maps. Extensionality reduces both equations to underlying global tensors;
the forgetful laws for composition, rationalization, comparison and
supplied-target extension give the ambient rational equations. The proof
requires neither generation of the rational centralizer by integral
full-order maps nor injectivity of chart evaluation.

For quasi-isogenies assume additionally that `O` is a domain and `F` is its
fraction field. `OrderAction.baseAlongCompQuasiIsogeny E f g` is
`QuasiIsogeny.ofIso (E.baseAlongCompIso f g)`. It retains rationalizations of
both actual integral maps and both inverse equations. The `_hom` and `_inv`
lemmas expose these maps. `baseAlongCompQuasiIsogeny_toAtlas` identifies the
entire forgotten quasi-isogeny with `X.baseAlongCompQuasiIsogeny f g`,
using equality of forward maps and uniqueness of the stored two-sided
inverse.

`QuasiIsogeny.baseAlongComp_natural` and `baseAlongComp_inv_natural`
give the two squares for whole full-order quasi-isogenies. Both follow by
forward-map extensionality and the corresponding rational naturality law.

These results concern the specified actual two-map comparison. They do not
assert strict equality of atlases, independence of arbitrary comparison
witnesses, three-map or identity-unit coherence, local rational gluing,
heights, framing, polarization, descent, levels or representability.

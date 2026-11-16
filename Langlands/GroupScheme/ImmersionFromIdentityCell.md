# Immersions from a closed inverse image of an identity neighbourhood

This is an internal geometric construction for the reductive monomorphism
proof. It is derived from group-object identities, openness of smooth
morphisms, stability of closed immersions under base change, and the Library's
fpqc finiteness descent together with Mathlib's implication from fpqc to fppf
descent. It asserts no separate translation from external literature.

For group objects `H`, `G` in a cartesian monoidal category and a monoid
homomorphism `f : H ⟶ G`, `translate f j` is the map
`H × V → G`, `(h, v) ↦ f(h) j(v)`, for any map `j : V ⟶ G`.
If a square with maps `i : D ⟶ H` and `k : D ⟶ V` over `f` and `j`
is cartesian and `k` is monic, `isPullback_translate` proves that

```text
H × D ---- (h,d) ↦ h i(d) ----> H
  |                              |
id × k                           f
  |                              |
  v                              v
H × V -------- translate ------> G
```

is cartesian. For compatible test maps `b : T ⟶ H` and
`(x, v) : T ⟶ H × V`, the original square lifts `(x⁻¹ b, v)` to
`d : T ⟶ D`. The new lift is `(x, d)`. Monicity of `k` and the two
product projections give uniqueness. The proof uses the actual morphisms,
not only geometric points.

Now let `S` be any scheme in any universe, let `H` and `G` be group schemes
over `S`, and let `f : H ⟶ G` be a homomorphism. Suppose the structure map
of `H` is smooth and the underlying scheme map of `j : V ⟶ G.X` is an open
immersion. `smooth_translate` proves that `translate f.hom.hom j` is smooth:
it factors through `id × j`, the left shear `(h,g) ↦ (h,f(h)g)`, and the
projection `H × G → G`. These maps are respectively an open immersion, an
isomorphism, and a base change of the smooth structure map of `H`.

`saturation f j` is the open subset of `G` given by the actual topological
image of this smooth translation family. If a section
`e : 𝟙_ (Over S) ⟶ V` satisfies `e ≫ j = 1`, then
`range_subset_saturation` proves that this open contains the image of `f`.
Indeed, the map `h ↦ (h,e)` followed by the translation family is `f`.
Here `1` denotes the identity section as a point of the target group object.

The main result `isImmersion_of_isPullback` assumes in addition that
`f.hom.hom` is monic in `Over S`, that the square with `i`, `k`, `f`, `j`
is cartesian in `Over S`, and that `k.left` is a closed immersion. Under
the same identity-section hypothesis on `e`, it proves
`IsImmersion f.hom.hom.left`, the ordinary locally closed immersion of
schemes. No affineness, connectedness, finiteness, or smoothness hypothesis
on `G` is needed.

The proof restricts the target to the open `W = saturation f j`. Both `f`
and the translation family factor through `W`. The latter factor is a
smooth surjection: its smoothness follows from an open-base-change square,
and surjectivity follows from the definition of `W`. The translated
cartesian square remains cartesian over `W`, since `W → G` is monic.
Its projection `id × k` is closed, hence finite. Finiteness descends along
the smooth surjection using the imported fpqc finiteness theorem and fppf
descent. The factor of `f` into `W` remains monic, so it is a finite
monomorphism and hence a closed immersion. Composition with the open
immersion `W → G` proves the claimed immersion.

This module does not prove that `f` is closed in all of `G`. Its application
to dynamic triple cells still requires a closed centralizer restriction and
the cartesian cell comparison; the reductive host theorem remains separate.

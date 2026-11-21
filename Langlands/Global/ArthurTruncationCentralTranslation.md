# Central translations commute with Arthur truncation

`Langlands.Global.ArthurTruncation.TruncationCentralTranslationStatement`
concerns the pointwise operator `truncation` on the full adelic group. Use
its usual data: a connected reductive group `G` over a number field, a maximal
split torus `i : T ⟶ G`, a cocharacter `ν`, reflection data, a compact Iwasawa
subgroup for the standard representative indexed by `∅` (the minimal
parabolic for generic `ν`), and the bijective character
comparison used to define the height. Supply any split torus `A` with a map
`f : A ⟶ T` for which the composite with `i` is central. For every adelic
point of `A`, write `z` for its image in `G(𝔸)`. Then for any complex function
`φ`, truncation parameter, and adelic argument `x`,

\[
  \Lambda^T\bigl[g\mapsto\phi(gz)\bigr](x)= (\Lambda^T\phi)(xz).
\]

This requires neither additional regularity of the truncation parameter nor
analytic conditions on `φ`. It is an identity of the Library's total integral
and sum formulas, not an assertion of their convergence or of measurability.

## Provenance and implemented proof

Derived from the definition of truncation in E. Lapid, *On Arthur's
asymptotic inner product formula of truncated Eisenstein series*, Clay Math.
Proc. 13 (2011), pp. 309–331, §2, p. 312, and used in the central Fourier step
in §8, p. 328. These are PDF pp. 321 and 337 in
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`.

1. `height_splitCentral_mem_rootAnnihilator`: the height of an adelic point
   of `T` is its logarithmic character functional in real cocharacter
   coordinates. The proof factors `T` through the minimal parabolic, uses
   the formula for the Iwasawa height on its parabolic factor, and compares
   character evaluations by bijective restriction to `T` and naturality of
   `characterLog`. The simple relative roots restrict to zero along the
   central split torus, so they annihilate the height of `z`.
2. Left multiplication by a point from the minimal parabolic adds its
   logarithmic height. Since `z` is central, the same formula applies to
   right multiplication by `z`. For each standard parabolic, the full
   fundamental weights that define its cutoff vanish on the common
   simple-root annihilator (`weight_eq_zero_of_mem_rootAnnihilator`). Thus
   the cutoff is unchanged by right multiplication by `z`.
3. The constant term of the right translate at `g` is the constant term of
   `φ` at `gz`: their integrands are equal by associativity. The two sums over
   parabolics and rational cosets therefore agree term by term.

The module proves the commutation used before passing to the norm-one slices.
It does not construct a split component, prove a norm-one decay estimate or
an orthogonal projection formula, or carry out the Fourier transform.

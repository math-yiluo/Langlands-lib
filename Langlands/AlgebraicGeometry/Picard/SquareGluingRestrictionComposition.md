# Composition of restriction of actual Picard square gluing data

This internal construction concerns actual line bundles and their invertible
arrows. Let two pairs of commuting faces give morphisms of scheme spans
from a span `S₀ → S₁, S₀ → S₂` to a span `T₀ → T₁, T₀ → T₂`, and then to a
span `Y₀ → Y₁, Y₀ → Y₂`. Write the maps from `T` to `Y` as `g₀, g₁, g₂`
and those from `S` to `T` as `h₀, h₁, h₂`. The parameters `k₁, k₂` are the
first pair of face equations, `l₁, l₂` the second pair, and `m₁, m₂` the
composite face equations. The latter may be supplied by associativity and the
first two pairs of equations.

The definition `pullbackComp` is a natural isomorphism from successive
`SquareGluingRestriction.pullback` along `g` and then `h` to restriction
along the composites `hᵢ ≫ gᵢ`. Its two component isomorphisms at a gluing
datum `D` are the ordinary Picard pullback composition comparisons at
`D.left` and `D.right`. The underlying overlap arrow of the datum is preserved
through these comparisons, rather than replaced by any chosen trivialization.

The helper `square_paste` states that the ordinary square comparison for a
composite face agrees with the square comparisons of its two constituent faces
through the ordinary pullback composition comparisons. Its proof forgets to
modules, expands square comparisons through composite comparisons, and uses
three instances of associativity of module pullback composition. A private
`compIso_assoc` helper is exactly the published `compHom_assoc` written for
the homs of the composite isomorphisms. The
`pullbackComp` construction uses this helper on both legs. After cancelling the
second leg's invertible comparisons, the comma compatibility is the naturality
of the overlap pullback composition comparison on `D.hom`. Naturality of the
resulting comma isomorphism follows from naturality of the two leg comparisons.

The construction imposes no cartesian, affine, field, flatness, or nilpotence
condition. It is coherence infrastructure; it does not establish global
effectivity or full faithfulness. Its provenance is internal, from the ordinary
pullback composition laws and the existing actual Picard restriction functor.

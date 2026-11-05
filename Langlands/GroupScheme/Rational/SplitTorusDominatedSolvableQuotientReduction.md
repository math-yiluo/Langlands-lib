# Reducing split-torus-dominated quotient existence to the absolute case

Worker 1485 combines the actual split-target descent construction with Worker
1376's full-kernel descent. This is an internal derived construction from those
APIs and the existing field-extension and geometric-connectedness theorems.
No external assertion is transcribed.

For arbitrary fields `k` and `K` in any common universe `u`, let `G` be a
reduced affine actual group scheme over `k` with
`HasPointedSplitTorusDomination G`. Suppose a supplied map `q : G_K → D` is
the represented fppf quotient by a supplied closed inclusion `i : U → G_K`,
where `U` is smooth, connected and unipotent, and `D` is a split torus over
`K`. `HasPointedSplitTorusDomination.descendSplitTorusQuotient` returns:

- Actual split-target descent data `r`, consisting of a split torus over `k`,
  a homomorphism from `G` to it, and an actual target isomorphism over `K`
  recovering `q`, with its morphism compatibility equation.
- `TorusQuotientKernelDescent r.hom i q`, which retains an actual source
  isomorphism `(kernel r.hom)_K ≅ U` commuting with the inclusions, an actual
  target recovery isomorphism and projection equation, the ground-field
  torus and fppf quotient predicates, and
  `LeviSubgroup.IsGeometricUnipotentRadical (kernelι r.hom)`.

The constructor first descends the supplied split target and map using
`descendSplitTorusHom`. It then passes the resulting map, target recovery
isomorphism and recovery equality to `torusQuotientKernelDescent`. Both
isomorphisms concern actual group schemes. The latter theorem establishes
the complete geometric radical predicate, including the actual
algebraic-closure comparison.

`splitTorusDominatedSolvableQuotient_of_solvableTorusQuotient` proves the
published `SplitTorusDominatedSolvableQuotientStatement` from an explicit
premise `SolvableTorusQuotientStatement`, at the same arbitrary universe `u`.
For each smooth connected affine solvable `H` over any field `k` with pointed
split-torus domination, geometric integrality supplies reducedness. The
proof extends `H` to `AlgebraicClosure k`. Smoothness and affineness are
preserved by pullback, connectedness follows from geometric connectedness
of the original finite-type connected group, and solvability follows from
the existing unconditional field-extension theorem.

The supplied absolute quotient statement produces a split-torus quotient
of this actual extended group with a closed smooth connected unipotent
full kernel. The first constructor descends it. The proof uses the
canonical full kernel of the descended map as its ground-field `U` and
extracts closedness, smoothness, connectedness and unipotence from the
geometric radical predicate. The descended fppf quotient and split target
supply the remaining fields of the published quotient statement.

The absolute quotient theorem remains an explicit premise; this unit does
not prove it. It introduces no restriction on characteristic, perfection,
infinitude, or the extension in the first construction. It neither supplies
ground-field split unipotence of the kernel nor proves the unconditional
torus-generated split geometric radical theorem. The existing predicates
and statement declarations remain unchanged.

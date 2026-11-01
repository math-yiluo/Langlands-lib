# Lifting covering open scheme charts across arbitrary thickenings

Worker 336 proves
`Langlands.AlgebraicGeometry.AlgebraicSpace.openFamilyLifting.{u}` with exactly
the type of the published `OpenFamilyLiftingStatement.{u}`. Worker 133
contributed to the interface and the parent proof decomposition. The statement
and its entire import closure remain unchanged.

The proof applies `OpenSubfunctorLifting.openFamilyLifting`. That module
constructs the largest subfunctor of the target whose inverse image is the
image of each given open chart. It proves that subfunctor is a sheaf and is
representable by open immersions on every scheme test. Pulling back an atlas
then makes it an actual algebraic space. Monicity of the unrestricted
thickening proves the prescribed pullback square, and base change proves
that the actual chart map is a thickening. Finally the proof transports the
point coverage of represented open pullbacks across the homeomorphism of a
scheme thickening, constructs actual open covers, and puts those covers in
the required image sieve. This proves local surjectivity of the coproduct
of the lifted inclusions. The paired `OpenSubfunctorLifting.md` explains all
of these steps and the supporting categorical constructions.

The original source is Stacks Project Tag 05ZP in Section 76.9, retained as
`05ZJ.html` and `05ZJ.txt` in
`/home/taskhub/pilot/literature/Stacks Project - Closed immersions and thickenings of schemes and algebraic spaces (HTML snapshot 2026-11-01)`.
It is registered as `stacks-algebraic-space-thickenings-2026-11-01`, directory
SHA-256 `ccb6ba86c00dce19994e249af819e4ed6aa7958b0fff47061565d127630d29da`.
The source's single-open lifting and base-change results motivate the
internal family formulation. The Lean proof uses universal image and
represented scheme tests directly, and does not require the source's
etale-equivalence argument as an input.

The result retains arbitrary universe `u`, every base scheme, actual
algebraic spaces and their actual morphism, every unrestricted thickening,
the original chart index type, genuine presheaf pullbacks and local coverage.
It assumes no finite-order bound, affineness, finiteness, separation,
noetherianity or prior target scheme representation. The lifted witnesses
are algebraic spaces; their affineness and the final schemeness theorem
require the separately owned finite-surjective affine-descent result.

The dependency on `SliceOpenGluing` uses its lifted-Yoneda monomorphism
helpers. That helper's Markdown and header preserve the Anthropic/NYLL source
attribution and original notices. The proof unit does not include the private
conditional parent assembly.

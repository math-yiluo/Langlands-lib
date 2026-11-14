# Quasi-affineness of supplied universal maximal-torus moduli

Worker 586.

`Langlands.GroupScheme.MaximalTorusModuliQuasiAffineStatement.{u}` is a
statement-only, `Prop`-valued definition. It isolates the quasi-affineness
requirement of [`MaximalTorusSchemeStatement`](MaximalTorusSchemeStatement.md).
It proves neither statement and introduces no axioms.

For every scheme `S : Scheme.{u}` and reductive group scheme `G` over `S`,
suppose an `S`-scheme `M`, a commutative group scheme `K` over `M`, and a map
`j : K.toGrp ⟶ G_M` are supplied. The hypotheses say that `K` is a relative
torus, `j` is a closed subgroup maximal on every residue-field fibre, and every
closed fibrewise maximal relative torus over every `S`-scheme is the evaluation
of `j` at a unique parameter morphism. These are exactly the universal-family
conditions of `MaximalTorusSchemeStatement`, including its image-based equality
on all test schemes and its universe convention. The conclusion asks that the
preimage under `M.hom` of each affine open in `S` be a quasi-affine scheme.
Neither smoothness nor surjectivity of `M.hom` is assumed or concluded here.
There is no existence assertion for `M` or `j` in this statement.

The provenance is a derived conditional form of Brian Conrad, *Reductive group
schemes* (2014), Theorem 3.2.6, first assertion, printed/PDF p.94. The registered
source is `conrad-2014-reductive-group-schemes`, retained as
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
That assertion supplies a smooth, surjective, quasi-affine scheme representing
the functor of maximal tori, under a hypothesis satisfied by reductive groups.
Any supplied universal maximal-torus family represents that same functor:
maximality is preserved by arbitrary base change, and universality gives the
bijection on parameter maps. Uniqueness of a representing scheme then
transports the source's quasi-affineness to the supplied `M`. This paragraph
explains the mathematical derivation of the statement, not an implemented
Lean proof. The imported statement's Markdown explains the residue-fibre
convention and the characterization of quasi-affine morphisms used here.

This conditional geometry assertion is a prerequisite for Task 6257. Its role
is to separate quasi-affineness from the construction of a smooth, surjective
universal maximal-torus family by restriction of the existing smooth moduli
of all closed torus subgroups. It does not weaken the unchanged main target
or discharge that target's existence and universality obligations.

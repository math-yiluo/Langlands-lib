# Integer torsion of commutative group schemes

For every scheme `S`, commutative group object `G : Grp (Over S)`, and integer
`n`, `Langlands.GroupScheme.torsion G n` is defined to be
`kernel (multiplication G n)`. Its homomorphism `torsionι G n` is the kernel
inclusion. This construction imposes no positivity, invertibility, smoothness,
properness or finiteness hypothesis.

The construction is derived by composing the published definitions in
`Kernel` and `Multiplication`. Their original source is Edixhoven–van der
Geer–Moonen, *Abelian Varieties*, preliminary chapters, the paragraph defining
integer multiplication on printed p.30 (PDF p.34), and Definition (3.13) and
its continuation on printed pp.36–37 (PDF pp.40–41). The former defines the
map by `x ↦ x^n` for every integer; the latter constructs kernels by the fibre
product with the target unit and identifies their functors of points. Combining
these two definitions gives the integer torsion construction here over an
arbitrary base. This source rationale does not use a theorem about finiteness.

`torsion_isPullback_scheme` exhibits the actual square of schemes with
horizontal maps the torsion inclusion and the unit section, and vertical maps
the torsion structure map and integer multiplication. The torsion group scheme
inherits commutativity. Its inclusion is monomorphic; it is a closed immersion
under the explicit hypothesis that `G` is separated over `S`. These facts are
specializations of the published kernel results.

For every test scheme `T : Over S`, `torsionPoints G n T` is the actual
`MonoidHom.ker` of the map on groups of sections induced by multiplication.
`mem_torsionPoints` proves that its elements are exactly the sections `x` with
`x^n = 1`, with multiplicative notation for the group law. In additive notation
this is `n • x = 0`. `torsionPointsEquiv` is a multiplicative equivalence from
the group of `T`-points of the torsion scheme to this subgroup. Its forward map
is composition with the inclusion. `torsionPointsRestrict` is precomposition
along any map `T' → T`, and `torsionPointsEquiv_naturality` proves compatibility
with this restriction. These declarations specialize the kernel equivalence
and its naturality and use the published pointwise multiplication formula.

`existsUnique_torsion_lift_iff` states the same representation property as a
unique-factorization criterion: a section of `G` factors uniquely through the
torsion inclusion if and only if its integer power is the unit. The proof uses
the inverse of `torsionPointsEquiv` for existence and its injectivity for
uniqueness. This includes zero and negative integers.

This focused unit supplies the torsion object and its pointwise description.
Base-change comparison, specialization to the parent's abelian-scheme bundle,
and the separate finite étale statement are subsequent obligations.

# Semi-invariant linear forms not vanishing on a flag orbit point

`Langlands.GroupScheme.FlagCoreDualLineStatement` is an internal interface
statement for the covering step of
`Langlands.GroupScheme.FlagInvariantAffineOpenCoverStatement`.

## Statement

Let `k` be an algebraically closed field and `G` a smooth connected affine group
over `k`, with a maximal torus `t : T → G`. Let `i : U → G` be a homomorphism
whose range lies in every Borel subgroup containing the range of `t`. Let
`b : B → G` be a Borel subgroup, and let `ρ` be a matrix representation of `G` on
`k^(n+1)` with a coordinate index `j`. Assume:

- on every test scheme `Z`, a point `x : Z → G` lies in the range of `b` exactly
  when `ρ(x) e_j = c e_j` for some unit `c` of `Γ(Z, O_Z)`;
- the vectors `ρ(g) e_j`, for `g` a rational point of `G`, span `k^(n+1)`.

Then for every rational point `g` of `G` there is a row vector `w` with
`w · ρ(g) e_j ≠ 0` and, for every rational point `x` of `U`,
`w ρ(i x) = c w` for some `c ∈ kˣ`.

Matrices of rational points are `MatrixRepresentation.rationalMatrix`; `w ᵥ* M`
is the row vector `w M` and `⬝ᵥ` the dot product.

## Provenance

This is an internal, derived statement; nothing in this module proves it. It
isolates the representation-theoretic step in the proof of Milne, *Algebraic
Groups* (2017), source ID `milne-2017-algebraic-groups`, Theorem 17.65 (printed
pp. 373-374). Milne embeds `G/B` nondegenerately in `P(V)` through a line whose
stabilizer is `B`, and shows that the open cell is the complement of the
hyperplane of a linear form whose line is fixed by `I_u(T)`.

Here the rational points of the orbit of `[e_j]` in `P^n`, a model of `G/B`, are
the lines `[ρ(g) e_j]`. The spanning hypothesis is Milne's nondegeneracy. The
conclusion asks for a `U`-semi-invariant linear form that does not vanish at a
given point. A chart lemma then turns such a form into an invariant affine open
neighbourhood of that point in the actual quotient. Spanning is needed because
`w` is built in the dual of the whole coordinate space. Any Chevalley
representation can be replaced by one with this property, which is a separate
lemma and not part of this statement.

# Geometric compact support from bounded Iwasawa ratios

Authors: Worker 467 and Worker 358. The Lean proposition retains Worker 358's
shared interface. This module states an internal geometric implication; it does
not prove that implication or the full JPSS gauge lemma.

For a prime `p`, a p-adic field `F` in arbitrary universe `uF`, supplied
`T : F.TopologicalData`, and arbitrary natural numbers `n,j,k`, put
`r = n + (j + k + 1)`. The actual matrix in `GL_(r+1)(F)` is

```text
             [ g   0      0    ]
M(g,x)   =   [ x   I_j    0    ],
             [ 0   0    I_(k+1)]
```

where `g` is in `GL_(n+1)(F)` and `x` has `j` rows and `n+1` columns.
The existing `unequalRankMatrix` and its `unequalRankMatrix_val` formula
implement these blocks; `x` is not multiplied by `g`.

For each real `R > 0`, `UnequalRankIwasawaSupportStatement F T n j k` asserts
the existence of a compact set `C` in the actual rectangular matrix space.
This single set is chosen before `g`, `x`, and all factors `u,a,κ`.
If `M(g,x) = u * diagonalUnits a * κ`, where `u` is upper unipotent,
`κ` belongs to the image of the integral general linear group for the
valuation supplied by `T`, and

```text
T.normalizedAbs (a_i / a_(i+1)) ≤ R       for every adjacent index i,
```

then `x ∈ C`. The diagonal entries are arbitrary field units, not just
powers of a chosen uniformizer. Both `κ` and `κ⁻¹` have integral entries,
as characterized by `Conductor.mem_integralSubgroup`.
The local instances inside the proposition are precisely `T.topology`,
`T.valuativeRel`, and `T.localField`; compactness uses the resulting finite
product topology on the matrix space. There is no identification of `T`
with canonical topological data.

All zero parameter cases are included. When `j=0`, the rectangular space
has a single element, and one may take its singleton. When `n=0`, `g` has
rank one and the rectangular space still has one column. When `k=0`,
the trailing block is still `I_1`. Thus even at `n=j=k=0` the ambient
matrix has rank two, and there is always a final identity row. No
positivity hypothesis on `n`, `j`, or `k` is added.

## Original source and specialization

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464: §2.4(3), printed p.387; Lemma 2.6 and its proof, pp.389–390;
and the unequal-rank compact-support application on p.393.
The registered source is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
These pages were read visually. No registered source erratum file was
found in the workspace, project, or published `notes/errata` locations
checked for this contribution.

In §2.4(3), the source's smaller rank `t` is our `n+1`, and its larger rank
is our `r+1`; its rectangular variable has `j` rows and `t` columns,
with trailing identity of size `k+1`. In Lemma 2.6, use source parameters
`j₁=n+1`, source `k=j`, and `j₂=k`, and specialize the lower diagonal
factor `g₂` to `I_k`. Its distinguished scalar `1` together with this
`I_k` is exactly our trailing `I_(k+1)`. The displayed matrix forces
the source's `x` to have source `k` rows and `j₁` columns. The printed
label `M(j₁ × k,F)` reverses those dimensions; this proposition follows
the displayed block and §2.4(3), using `Matrix (Fin j) (Fin (n+1)) F.Carrier`.

The full Lemma 2.6 starts with a gauge and also supplies a dominating
gauge. Its proof on p.390 first obtains a bound on adjacent diagonal
ratios from gauge nonvanishing, and then deduces boundedness of `x`
using exterior powers of final rows. This internal proposition isolates
that latter geometric implication and makes the root bound an explicit
premise for every `R>0`. It includes no Whittaker function, gauge,
central character, measure, or representation. It supplies neither
the preceding root-support estimate nor the additional gauge-majorant
conclusion. Publication of this Prop definition proves neither one,
nor the final Whittaker compact-support assertion.

## Independent check of the proposed proof route

The following ordinary mathematical argument checks the scope of the
proposed specialization. It is not a Lean proof in this module.
Write `m=r+1`, let `|·|` denote `T.normalizedAbs`, and let `D_s(A)`
be the maximum absolute value of all minors formed from the final `s`
rows of an `m` by `m` matrix `A` and any `s` columns, for `1≤s≤m`.
These are the coordinates of the wedge of the final rows.

Right multiplication by an integral invertible matrix preserves `D_s`.
Cauchy–Binet and the non-Archimedean inequality give one inequality
because all its minors are integral; applying the same argument to its
integral inverse gives the reverse inequality. Left multiplication by
an upper unipotent matrix preserves the wedge of the final `s` rows:
those rows mix only among themselves, with determinant one. Consequently,
for the factorization in the statement, with indices `0,…,m-1`,

```text
D_s(M(g,x)) = product of |a_q| over m-s ≤ q < m.
```

The final row of `M(g,x)` is the final standard basis row, so `D_1=1`
and hence `|a_(m-1)|=1`. Put `B₀=max(1,R)`. The adjacent-ratio
assumptions imply successively `|a_q|≤B₀^(m-1-q)`, and therefore
`D_s(M(g,x))≤B₀^(s(s-1)/2)`. This argument uses arbitrary diagonal
units and does not use the entries or determinant of `g`.

For an entry `x_(t,c)` with `0≤t<j`, take the suffix of rows starting
with the ambient row `n+1+t`, of length `s=j+k+1-t`. Select column `c`
of the first block and the identity columns corresponding to every
strictly later row. The resulting determinant is `x_(t,c)` up to sign:
its first row has no entry in those selected identity columns, while
the later rows give an identity matrix there. Thus every entry of `x`
is bounded by its corresponding `D_s`, uniformly in `g` and the factors.
For example `B=B₀^(m(m-1)/2)` is a common bound.
Finite products of the compact field balls `{z : |z|≤B}` give a
compact rectangular set `C`. Replacing `R` by `max(1,R)` in these
estimates covers `0<R<1` without changing any premise of the statement.
The empty-row case was addressed separately above.

The formal successor must implement the minor or exterior-power
invariance, this entry extraction, and compactness in the supplied
topology before claiming the geometric theorem. Worker 358 retains
the final assembly with the separate Whittaker root-support estimate.

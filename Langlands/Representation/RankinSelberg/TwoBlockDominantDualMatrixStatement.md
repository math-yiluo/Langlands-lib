# The actual reversed-dual matrices in JPSS Section 4.10

`Langlands.RankinSelberg.TwoBlockDominantDualMatrixStatement.{uF}` is a
closed proposition stating three identities in the actual group
`GeneralLinear (r+1) K`. It uses the unchanged published constructions in
`TwoBlockDominantRectangularData` and `Langlands.Group.GL.Maps`. This pair
states the algebraic comparison; a proof of the proposition is a separate
obligation.

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
Convolutions* (1983), Section 4.10, printed pp.418–420, especially formulas
(2) and (3) on p.419 and the displayed Weyl identity on p.420. Its registered
ID is `jpss-1983-rankin-selberg`, and the retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The hash was verified and all three original page images were read; these
are PDF pages 53–55, counted from one. The registered entry has no errata
pointer, and the checked project errata locations and registered index
provide no JPSS-1983-specific correction.

The paper's ranks and the Lean indices correspond as follows:

| Source notation | Actual size in this statement |
| --- | --- |
| `t` | `N=t+1` |
| `r` | `R=r+1` |
| `t₁` | `a=m 0+1` |
| `t₂` | `b=m 1+1` |
| `r-t` | `c=j+k+1` |

Here the letters on the right use the Lean variables. The quantified
equalities are `h : ∑ i, (m i+1)=t+1` and `hr : r=t+(j+k+1)`, so
`N=a+b` and `R=N+c`. In particular `R>N` follows from the separator
of size one. The statement quantifies over every field `K : Type uF`,
every natural `t,r,j,k`, every family `m : Fin 2 → ℕ`, and both
equalities. No extra positivity condition is imposed on `j,k` or on
`m 0,m 1`: empty rectangles and blocks of size one are included.
Extension from the paper's local field to an arbitrary field is derived
algebraic support and needs no topology.

Within the proposition, `mD i=m i.rev` reverses the entire dependent
family, `hD=TwoBlockLowerUnipotentQuotient.reverse_sum h` proves its
sum equality, and `hrD : r=t+(k+j+1)` is derived from `hr` by natural
number arithmetic. These are specified rank transports, with no new
independent equality hypotheses. The original order of the five blocks
is `(a,k,1,j,b)`, and the reversed order is `(b,j,1,k,a)`.

All Weyl representatives are the existing unsigned anti-diagonal
permutation matrices `GeneralLinear.weylLong`. The first conjunct is
precisely

```text
blockWeyl hD hrD * append hr w_N * rightWeyl hr
  = w_R * blockWeyl h hr.
```

The reversed block-Weyl factor uses the exchanged indices `j,k`. In
ordinary matrix notation the equality is

```text
diag(w_b,w_(c+a)) * diag(w_N,w_c)
  = w_R * diag(w_a,w_(c+b)).
```

This is the displayed identity on printed p.420, with the source ranks
translated by the table above. In Lean, `append hr w_N=diag(w_N,I_c)`
and `rightWeyl hr=diag(I_N,w_c)` retain their existing transports
to `GeneralLinear R K`; their product supplies the second factor
in that source display.

For every source pair `xD : Matrix (Fin b) (Fin j) K` and
`yD : Matrix (Fin k) (Fin a) K`, the proposition defines exactly

```text
x i l = -yD l.rev i.rev,    x : Matrix (Fin a) (Fin k) K,
y i l = -xD l.rev i.rev,    y : Matrix (Fin j) (Fin b) K.
```

Its second identity, writing `it_R=GeneralLinear.inverseTranspose R K`,
is

```text
w_R * it_R (rectangleUnipotent hD hrD xD yD) * w_R
  = rectangleUnipotent h hr x y.
```

The signed coordinate exchange is derived algebraic support for comparing
the displayed rectangle matrices. Inverse transpose negates and
transposes the two nonidentity rectangles, and long-Weyl conjugation
reverses both finite indices and exchanges their positions. The singleton
separates their supports. Both negative signs and both finite-index
reversals appear explicitly in the proposition. These formulas use only
the published matrix types and finite indices; no coordinate-equivalence
or Haar helper is imported.

The third identity is quantified over every actual `g : GeneralLinear N K`.
With `Tg=w_N * GeneralLinear.inverseTranspose N K g`, it states

```text
w_R * it_R (reversedMatrix h hr Tg xD yD)
  = matrix h hr g x y.
```

The existing definitions expand to

```text
matrix h hr g x y
  = w_R * rectangleUnipotent h hr x y * blockWeyl h hr * append hr g,
reversedMatrix h hr Tg xD yD
  = matrix hD hrD Tg xD yD * rightWeyl hr.
```

Thus the explicit final right factor `diag(I_N,w_c)` of 4.10(3) on
p.419 remains part of the comparison. The complete matrix packaging is
derived algebraic support, designed from inverse transpose's
multiplicativity and involutivity, its action on Weyl representatives,
commutation of `diag(g,I_c)` with `diag(I_N,w_c)`, and the first two
identities. None of these three claimed identities is a premise of the
closed proposition.

On p.419 the source illustrates the preceding integral derivation with
`k=0`, while its displayed block matrices retain the complementary `j,k`
notation. The algebraic statement here keeps arbitrary complementary
`j,k`, with `j+k+1=c`; it imposes neither `k=0` nor `j=0`. Every
matrix equality is pointwise for all source rectangles and all `g`,
with no quotient or almost-everywhere qualification.

Worker 1198 authored this statement and documentation using Worker 484's
supplied signed-coordinate and full-matrix design. The latter design,
its arbitrary-field scope and its packaging as a single closed proposition
are derived support for the source comparison. This pair supplies no
proof of these identities and asserts no dual-section realization,
scalar-kernel comparison, measure transport, convergence, Laurent
identity, continuation or gamma/L-factor comparison.

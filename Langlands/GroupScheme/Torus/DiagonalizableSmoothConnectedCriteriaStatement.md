# Smoothness and connectedness of diagonalizable groups: statement

Worker 3483.

`Langlands.GroupScheme.DiagonalizableSmoothConnectedCriteriaStatement.{u}` is a
proposition definition. This module does not prove it.

## The statement

Let `k` be a field in the universe `u` and let `p` be its characteristic
exponent, `ExpChar k p`: `p = 1` if `k` has characteristic zero and `p` is the
characteristic otherwise. Let `Λ` be an abelian group in the universe `u` that is
finitely generated, `AddGroup.FG Λ`. Write `D(Λ)` for the Library's
diagonalizable group `Diagonalizable.groupScheme (CommRingCat.of k) Λ`
(`Torus/Diagonalizable`). Its underlying scheme `D(Λ).X.left` is the spectrum
of the group algebra `k[Λ]` (`AddMonoidAlgebra k Λ`), and `D(Λ).X.hom` is its
structure morphism to `Spec k`. The statement asserts the conjunction of:

1. `ConnectedSpace D(Λ).X.left ↔ ∀ x : Λ, IsOfFinAddOrder x → ∃ n : ℕ, p ^ n • x = 0`;
2. `Smooth D(Λ).X.hom ↔ ∀ x : Λ, p • x = 0 → x = 0`;
3. `Smooth D(Λ).X.hom ∧ ConnectedSpace D(Λ).X.left ↔ Module.Free ℤ Λ`.

In words: `D(Λ)` is connected if and only if every torsion element of `Λ` is
killed by a power of `p`; `D(Λ)` is smooth over `k` if and only if no nonzero
element of `Λ` is killed by `p`; and `D(Λ)` is smooth and connected if and only
if `Λ` is a free abelian group.

`Smooth` is Mathlib's smooth morphism of schemes, `ConnectedSpace` refers to the
Zariski topology of the underlying scheme, `IsOfFinAddOrder x` says that `x` has
finite additive order, and `Module.Free ℤ Λ` says that `Λ` has a `ℤ`-basis.

When `p = 1` the right side of part 1 says that `Λ` is torsion-free (`1 ^ n • x = x`)
and the right side of part 2 always holds. So in characteristic zero every `D(Λ)`
is smooth, and it is connected exactly when `Λ` is torsion-free.

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (2017), source ID `milne-2017-algebraic-groups`.

The group `M` is finitely generated throughout §12.b, whose opening reads
(printed p.230, PDF p.246):

> Let M be a finitely generated commutative abstract group (written
> multiplicatively), and let k[M] be the k-vector space with basis M.

Proposition 12.3 (printed p.231, PDF p.247) defines `D(M)`:

> For every finitely generated commutative group M, the functor
> D(M) : R ⇝ Hom(M, R^×) (homomorphisms of groups) is represented by the
> algebraic group Spm(k[M]).

Remark 12.5 (printed p.232, PDF p.248) is the statement formalized here:

> Let p be the characteristic exponent of k. Then:
> D(M) is connected ⟺ the only torsion in M is p-torsion
> D(M) is smooth ⟺ M has no p-torsion
> D(M) is smooth and connected ⟺ M is free.
> For example, D(Z) = G_m, which is connected and smooth, and D(Z/nZ) = μ_n,
> which is connected and nonsmooth if n is a power of p, and is étale and
> nonconnected if n is relatively prime to p.

## Correspondence with the source

- Milne's `M`, written multiplicatively, is the additive group `Λ`, and
  `AddGroup.FG Λ` is the finite generation fixed at the start of §12.b. The
  Library's `Diagonalizable.groupScheme (CommRingCat.of k) Λ` is `Spec k[Λ]`
  with points `Hom(Λ, Γ(T, 𝒪_T)^×)` over every test scheme `T`, which is
  Milne's `D(M)` from Proposition 12.3. Requiring `Λ` to lie in the universe of
  `k` loses nothing, since every finitely generated abelian group has an
  isomorphic copy there.
- "The only torsion in `M` is `p`-torsion" is read as: every element of finite
  order has order a power of `p`, i.e. `∃ n, p ^ n • x = 0`. This is the reading
  the remark's example requires: `μ_n` with `n` a power of `p` is connected even
  when `n` is a higher power of `p`, so "`p`-torsion" here means `p`-power
  torsion, not only elements killed by `p` itself.
- "`M` has no `p`-torsion" is written `p • x = 0 → x = 0`. An abelian group has
  a nonzero element of `p`-power order if and only if it has a nonzero element
  killed by `p`, so the two readings of "`p`-torsion" agree here.
- "`M` is free" is `Module.Free ℤ Λ`; since `Λ` is finitely generated, it is
  then free of finite rank.
- Milne calls an algebraic scheme smooth when it is smooth after passing to the
  algebraic closure (printed p.13, PDF p.29), and A.56 (printed p.579,
  PDF p.595) characterizes this as surjectivity of `X(R) → X(R/I)` for every
  square-zero ideal `I`. For a scheme of finite type over `k`, such as `D(Λ)`
  with `Λ` finitely generated, this is formal smoothness of the structure
  morphism together with finite presentation, which is Mathlib's `Smooth`.
- Milne's `Spm(k[M])` and Mathlib's `Spec k[Λ]` have the same connectedness:
  both are connected exactly when `k[Λ]` has no idempotents other than `0` and
  `1`.

The statement formalizes the three equivalences of Remark 12.5 only. The
remark's examples and the further identifications of `D(M)°`, `D(M)_red` and
`D(M)°_red` with `D` of quotients of `M` are not part of it.

## Finite generation is needed

`Diagonalizable.groupScheme` is defined for every abelian group `Λ`. For `Λ`
free of countably infinite rank, `k[Λ]` is not finitely generated over `k`, so
`D(Λ)` is not locally of finite presentation and hence not smooth, although `Λ`
is free. The hypothesis `AddGroup.FG Λ` excludes this case, as Milne's standing
assumption does.

## Relation to other Library results

- Part 3 follows from published Library results. A private check compiled
  both directions in Lean against the Library:
  - forward: `Diagonalizable.free_of_smooth_connected`
    (`Torus/SmoothConnectedKernelCocharacters`) states, with the same Lean
    expressions, that for a field `k` and finitely generated `Λ`, smoothness
    and connectedness of `D(Λ)` imply `Module.Free ℤ Λ`;
  - reverse: if `Λ` is free, a `ℤ`-basis `b` of `Λ`
    (`Module.Free.chooseBasis`, finite since `Λ` is finitely generated) gives
    `Diagonalizable.isSplitTorus (CommRingCat.of k) b.equivFun.toAddEquiv`
    (`Torus/Diagonalizable`), and `IsSplitTorus.smooth` (`Torus/Split`) and
    `IsSplitTorus.connectedSpace` (`Torus/SplitReductiveProof`) then give
    smoothness and connectedness of `D(Λ)`.
- Parts 1 and 2 have no Lean declaration in the Library that was found by
  searching for `Smooth` and `ConnectedSpace` of `Diagonalizable.groupScheme`.
  Results a proof can build on include `smooth_gm` and `smooth_pi`
  (`GroupScheme/SmoothProducts`: `𝔾_m` and finite products of smooth group
  schemes are smooth), `muFiniteEtale` (`GroupScheme/MuFiniteEtaleProof`:
  `μ_n` is finite étale for positive `n` invertible on the base), and the instance
  `Diagonalizable.locallyOfFiniteType` (`Torus/DiagonalizableGeometry`:
  `LocallyOfFiniteType D(Λ).X.hom` for finitely generated `Λ`, over any base
  ring).

The published family-2 ledger (`notes/group-schemes/ledger-family-2-tori.md`,
row D5) lists these criteria as an open target; this module supplies the
statement.

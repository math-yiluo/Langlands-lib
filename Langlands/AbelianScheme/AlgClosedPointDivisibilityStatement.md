# Divisibility of geometric points of abelian schemes

`Langlands.AbelianScheme.AlgClosedPointDivisibilityStatement` is a proposition
target. Take a scheme `S`, an abelian scheme `B : AbelianScheme S`, an
algebraically closed field `K` with a morphism `s : Spec K ⟶ S`, and a natural
number `m` with `(m : K) ≠ 0`. The target says that every point
`y : Over.mk s ⟶ B.X` has an `m`-th root: some point
`x : Over.mk s ⟶ B.X` satisfies `x ^ m = y`.

Here `Over.mk s ⟶ B.X` is the set of `S`-morphisms from `Spec K`, viewed over
`S` through `s`, to the actual abelian scheme `B.X`. These are the `K`-points of
`B` lying over `s`. The power `x ^ m` is computed in Mathlib's group structure
on morphisms into a group object, which `open scoped CategoryTheory.MonObj`
makes available. That group structure multiplies points using the group law of
`B`, so `x ^ m` is the image of `x` under multiplication by `m` on `B`, written
multiplicatively. Every object is imported: `AbelianScheme` from
`Langlands.AbelianScheme.Basic`, and the field, scheme and group-object
structures from Mathlib. The statement introduces no data.

## Source correspondence and derived scope

The source is J. S. Milne, *Abelian Varieties*. This is the 1986 *Arithmetic
Geometry* article in the author's corrected version of January 2, 2022,
registered as `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
In this copy the author's page numbers equal the one-based PDF page numbers.

- Section 8, opening paragraph, p.12, calls a homomorphism of abelian varieties
  an isogeny when it is surjective and its kernel is finite.
- Theorem 8.2, p.13: for an abelian variety `A` of dimension `g` and an integer
  `n > 0`, `n_A : A → A` is an isogeny of degree `n^(2g)`. It is étale exactly
  when the characteristic of the field does not divide `n`.
- Remark 8.4, p.14, works over a separably closed field and describes `T_l A`
  as sequences of points `a_1, a_2, ...` with `l a_1 = 0` and
  `l a_n = a_(n-1)`. Divisibility of points by `l` is what makes every finite
  level of such sequences reachable; this is the downstream use of the target.
- Section 20, opening definition, p.42: an abelian scheme is a proper smooth
  group scheme with connected geometric fibres, and its geometric fibres are
  abelian varieties. Proposition 20.7, p.44: multiplication by `n` on an
  abelian scheme is flat, surjective and finite.

The provenance is **derived**. Milne states surjectivity of `n_A` as a morphism
of schemes. The target is the consequence for `K`-points over an algebraically
closed field. The fibre `B_s = B ×_S Spec K` is an abelian variety over `K`. A
point `y` over `s` is a `K`-rational point of `B_s`. Multiplication by `m` is a
surjective morphism of `K`-schemes of finite type, so the fibre of `[m]` over
`y` is a nonempty `K`-scheme of finite type. It therefore has a closed point,
whose residue field is finite over `K` and hence equal to `K`. That point is a
`K`-point `x` with `m x = y`. Points of `B` over `s` correspond to `K`-points of
`B_s` by the universal property of the fibre product. This argument is a proof
obligation, not part of the present file.

The hypothesis `(m : K) ≠ 0` is stronger than Milne's `n > 0`: it also excludes
multiples of the characteristic of `K`. It is the case needed downstream, for
`m` a prime different from the characteristic, where `[m]` is moreover étale.
The target makes no assumption on `S` beyond being a scheme, on the relative
dimension of `B`, or on other points of `S`. It asserts nothing about the
number of roots or the structure of the torsion subgroup.

## Formal status

The Lean declaration is a `Prop`-valued `def`, not a theorem or an assumption.
Its proof is a separate obligation, assigned after this statement is accepted
and published.

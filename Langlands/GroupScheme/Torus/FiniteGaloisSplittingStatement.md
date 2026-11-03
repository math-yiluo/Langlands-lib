# Statement: every torus over a field splits over a finite Galois extension

Author: Worker 770.

This module states that every torus over a field, in the sense of the Library
definition `IsTorus`, becomes a split torus after base change to a finite
Galois extension of the base field. It only defines the proposition and proves
nothing. The declaration is a `Prop`-valued `def` in the namespace
`Langlands.GroupScheme`, with one universe parameter `u`.

## Lean statement

```lean
def TorusFiniteGaloisSplittingStatement : Prop :=
  ∀ (k : Type u) [Field k] (T : GroupScheme (Spec (CommRingCat.of k))), IsTorus T →
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧ IsGalois k K ∧
      IsSplitTorus ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
```

- `k` is an arbitrary field in an arbitrary universe `u`. The statement makes
  no assumption that `k` is perfect, infinite or of characteristic zero.
- `T` is an actual group scheme over `Spec k`. The only hypothesis on it is
  the existing `IsTorus T` (module `Langlands.GroupScheme.Torus.Lattice`):
  there are a field `K₀ : Type u` and an algebra `k → K₀` such that the base
  change of `T` along `Spec K₀ → Spec k` is a split torus. `IsTorus` puts no
  condition on `K₀` (it may be infinite or inseparable over `k`). It also does
  not assume that `T` is affine or of finite type.
- The conclusion gives a field `K : Type u`, in the same universe as `k`, and an
  algebra `k → K`. `FiniteDimensional k K` says that `K` is a finite extension.
  Mathlib's `IsGalois k K` says that it is separable and normal. Together the
  two conjuncts say that `K / k` is a finite Galois extension.
- `GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))` is
  the published base-change functor along `Spec K → Spec k` (module
  `Langlands.AbelianScheme.GroupScheme`). It is the actual scheme pullback
  `(Over.pullback _).mapGrp` with its induced group law. The same morphism is
  used in `IsTorus`.
- `IsSplitTorus` (module `Langlands.GroupScheme.Torus.Split`) asks for a finite
  type `I : Type u` and an isomorphism of group schemes over `Spec K` from the
  base change onto `splitTorus (Spec K) I`, the product of copies of `𝔾_m`
  indexed by `I`. So the conclusion is an actual isomorphism of group schemes
  with a finite product of copies of `𝔾_m`. It is not just an identification of
  character lattices and not a statement about rational points.
- The empty index type is allowed in both `IsTorus` and `IsSplitTorus`. So the
  rank-zero torus, the trivial group scheme, is covered; there `K = k` works.

No separable-closure form is part of this target. Its conclusion is the finite
Galois form directly, with no extra premise. The separable-closure form
corresponds to Milne 12.18(d): `T` becomes split over `SeparableClosure k`. It
is equivalent in content and is not stated here. A proof that wants it as an
intermediate step must prove it, or state it as its own target.

## Sources

- Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`:
  - Definition 1.1 (printed p.6, PDF p.22): an algebraic group over `k` is a
    group object in algebraic `k`-schemes, i.e. `k`-schemes of finite type.
  - Chapter 12 opening (printed p.230, PDF p.246): "Recall that all algebraic
    groups are affine over a base field k."
  - Definition 12.14 (printed p.236, PDF p.252): "An algebraic group over k is
    a torus if it becomes isomorphic to a finite product of copies of Gm over
    some field containing k. A torus over k is split if it is isomorphic to a
    product of copies of Gm over k." The next paragraph says that the split
    tori are the smooth connected diagonalizable algebraic groups.
  - Definition 12.17 (p.236): multiplicative type means diagonalizable over
    some field containing `k`. Theorem 12.18 (printed p.237, PDF p.253): (a)
    multiplicative type is equivalent to (d) diagonalizable over `k_s`.
  - Corollary 12.19 (printed p.238, PDF p.254): "If an algebraic group over k
    becomes diagonalizable over some extension of k, then it becomes
    diagonalizable over a finite separable extension of k."
  - The official errata (source ID
    `milne-2017-algebraic-groups-errata-2026-11-02`) list only 12.41 (p.244)
    and 12.57 (p.249) in Chapter 12. Neither affects 1.1 or 12.14–12.19.
- SGA 3, Exposés IX and X (Gille–Polo recomposed edition, version of
  8 November 2009). Source IDs `sga3-expose-ix-gille-polo-2009` and
  `sga3-expose-x-gille-polo-2009`. "Margin" below means the original
  LNM 152 page numbers printed in the margin.
  - IX Definition 1.3 (recomposed p.32, margin p.39): `G` is a torus if it is
    locally isomorphic, for the fpqc topology, to `𝔾_m^r` with `r ≥ 0`.
  - IX Definition 1.1 (p.31, margin p.37): multiplicative type means fpqc
    locally diagonalizable.
  - IX Remark 1.5 a)–b) (p.33): both notions are stable under base change, and
    they descend along fpqc base changes.
  - X Proposition 1.4 (recomposed p.64, margin p.79): "Soient k un corps, H un
    groupe de type multiplicatif et de type fini sur k, alors H est isotrivial,
    i.e. il existe une extension finie séparable k′ de k qui déploie H." That
    is, over a field, every group of multiplicative type and of finite type is
    split (made diagonalizable) by a finite separable extension.

## How the theorem applies to `IsTorus`

`IsTorus T` supplies only some splitting field `K₀`, and it assumes neither
affineness nor finite type of `T`. The sources apply as follows. This outline
is for the separate proof task; this module proves none of it.

1. `Spec K₀ → Spec k` is faithfully flat and quasi-compact. So `IsTorus T` is
   exactly an fpqc trivialization `T_{K₀} ≅ 𝔾_m^r` with one cover. Hence `T`
   is a torus in the sense of SGA 3 IX 1.3 over `S = Spec k`, and it is of
   multiplicative type by IX 1.1.
2. `T_{K₀}` is affine and of finite type over `K₀`. By fpqc descent of these
   properties, `T` is affine and of finite type over `k`. Then `T` is an
   algebraic group in Milne's sense (Definition 1.1 and the Chapter 12
   convention) and a torus by Milne 12.14. The descent fact is standard and is
   not one of the cited numbered results.
3. SGA 3 X 1.4, or Milne 12.19 via 12.18(d), gives a finite separable
   extension `k'` with `T_{k'}` diagonalizable. A diagonalizable torus is
   split. Over a field containing both `k'` and `K₀` it is isomorphic to
   `𝔾_m^r`, so it is smooth and connected, and Milne p.236 (after 12.14) applies.
   Alternatively, its type is `ℤ^r`, because the type of a diagonalizable group
   does not change under field extension (SGA 3 IX 1.4 and 1.4.1 b)). So
   `IsSplitTorus` holds over `k'`.
4. Let `K` be a Galois closure of `k'` over `k`, chosen inside an algebraic
   closure of `k` so that `K : Type u`. `K / k` is finite Galois. By
   `IsSplitTorus.baseChange` (module `Langlands.GroupScheme.Torus.Split`) and
   the composition of base changes, the base change of `T` to `K` is split.

## Provenance and scope

The statement is Milne 12.19 and SGA 3 X 1.4 for tori, in the Library's
vocabulary. Two changes are derived and need no new idea. The finite separable
extension is enlarged to its Galois closure, which preserves splitting. The
conclusion is the existing scheme-level `IsSplitTorus`, not "diagonalizable".

This proposition is a missing prerequisite for Galois descent of tori,
requested for the algebraic-groups programme. Only the statement is defined
here. The proof is a separate obligation.

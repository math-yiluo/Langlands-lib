# Positive-multiple descent of ample Mumford presentations over algebraically closed fields

`Langlands.AbelianScheme.PolarizedFiniteLevel.AlgebraicallyClosedFieldPolarizationDivisionStatement`
is a proposition in an arbitrary universe `u`. It is a statement target, not a
proof: the module states it and does not prove it.

## Statement

It quantifies the named prerequisite package `P : Prerequisites.{u}`, a field
`K : Type u` with `IsAlgClosed K`, an actual abelian scheme
`A : AbelianScheme (Spec (CommRingCat.of K))`, dual witnesses
`W : DualWitness A` (the published `DualWitness` of `PolarizedFiniteLevel`),
an actual homomorphism `mu : A ⟶ W.dual P` to the constructed dual and a
natural number `n` with `0 < n`. It asserts the implication

```
HasAmpleMumfordPresentation P.preservation P.square A W.hasDual
    (groupHom (n • mu)).hom.hom →
HasAmpleMumfordPresentation P.preservation P.square A W.hasDual
    (groupHom mu).hom.hom
```

- `n • mu` is the natural-number multiple in the additive group of
  abelian-scheme homomorphisms `A ⟶ W.dual P` (the `AddCommGroup` instance of
  `Langlands.AbelianScheme.Basic`, transported from commutative group
  schemes). Its underlying morphism is `mu` followed by multiplication by `n`
  on the dual.
- `(groupHom f).hom.hom : A.X ⟶ dualScheme A W.hasDual` is the underlying
  morphism over `Spec K` of a homomorphism `f`; the constructed dual
  `W.dual P` has the chosen dual scheme `dualScheme A W.hasDual` as its
  underlying object.
- `HasAmpleMumfordPresentation preservation square A hA f`
  (`Langlands/AlgebraicGeometry/Picard/AmpleMumfordBaseChange.lean`) says that
  there are an ample line bundle `L` on `A`, an inverse of `e^*L` (with `e` the
  unit section) and an inverse of the normalized bundle, each with its
  evaluation isomorphism, such that `f` equals the Mumford map
  `mumfordSchemeMapOfLineBundle` of these data, the classifier of the
  normalized Mumford family of `L`.

Both presentations are over `K` itself: the conclusion asks for an ample line
bundle on `A`, not on a base change of `A` to an extension field. No isogeny
condition, level structure, restriction on the characteristic of `K` or other
hypothesis on `mu` is imposed.

The published polarization predicate `AbelianScheme.IsPolarization`
(`Langlands/AlgebraicGeometry/Picard/RelativePolarization.lean`), through
`HasFieldAmpleMumfordPresentation`, asks at each geometric point for an ample
Mumford presentation of the fibre map after some extension of the field. A
presentation over `K` itself gives one after the identity extension. The
statement therefore supplies the geometric-fibre condition for `mu` once it is
known for a positive multiple `n • mu`. The published
`PolarizationDoublingDivisionStatement` concludes only for `2 • mu`, so it
does not give this.

## Provenance

The statement is derived from B. Edixhoven, G. van der Geer and B. Moonen,
*Abelian Varieties*, preliminary version of the first chapters (PDF of
8 February 2012), registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`. The
inputs are Propositions (11.2) and (11.4) and Corollary (11.5) (printed
pp. 159–160, PDF pp. 163–164), Corollary (7.22) (printed p. 106, PDF p. 110)
and (7.26) (printed p. 107, PDF p. 111). Write
`X = A`, `k = K` and `λ = mu`, and let `φ_L : X → X^t` be the map attached to
a line bundle `L`.

1. By the premise, `nλ = φ_L` for an ample line bundle `L` on `X`. Every map
   `φ_L` is symmetric ((7.26)), so `nλ` is symmetric.
2. Dualization is additive, so `λ^t ∘ κ - λ` (with `κ` the biduality map) is
   killed by composition with multiplication `[n]` on `X`. For `n ≠ 0`, `[n]`
   is an isogeny, in particular faithfully flat, hence an epimorphism. So `λ`
   is symmetric.
3. By (11.2), (a) implies (b), a symmetric `λ` equals `φ_B` for a line bundle
   `B` over an algebraic closure of `k`. Here `k` is algebraically closed, so
   `B` is a line bundle on `X` itself.
4. Since `φ` is a homomorphism, `φ_{B^n} = nφ_B = φ_L`. By (7.22), the kernel
   of `φ` is `Pic^0`, so `B^n ⊗ L^{-1}` lies in `Pic^0`. For ample `L` the
   kernel `K(L)` of `φ_L` is finite, so `φ_L` is an isogeny and, `k` being
   algebraically closed, every class in `Pic^0` is `t_x^*L ⊗ L^{-1}` for a
   point `x`. Hence `B^n ≅ t_x^*L` is ample. A line bundle with an ample
   positive tensor power is ample, so `B` is ample.

Step 4 may be replaced by the diagonal criterion (11.4)(iii): `B` is ample if
and only if `(id, λ)^*P` is ample. Bilinearity of the Poincaré bundle `P`
gives `(id, nλ)^*P ≅ ((id, λ)^*P)^n`, which is ample by (11.4)(iii) applied to
`nλ` and `L`.

The hypothesis `0 < n` is used twice: it ensures that `[n]` is an
epimorphism in step 2, and it makes `B^n` a positive tensor power, so that
its ampleness implies that of `B` in step 4.

The conclusion is condition (b1) of (11.5) with the trivial field extension,
written as the Library's predicate `HasAmpleMumfordPresentation` for the
Library's Mumford map; over a field the inverse line bundles and evaluation
isomorphisms that the predicate quantifies exist.

The source proves (11.2) without restriction on the characteristic. With
`M = (id, λ)^*P` and `N = M^2`, it shows that the full subgroup scheme `X[2]`
is totally isotropic for the commutator pairing `e_N`: after an fppf covering,
`T`-valued points of `X[2]` are doubles of points of `X[4]`, and `e_N` takes
values in `μ_4` on `X[4]`. Corollary (8.11) (printed p. 117, PDF p. 121), whose
proof splits the commutative extension of `X[2]` by `G_m`, then descends `N`
along `[2]`. Working with the subgroup scheme rather than with rational torsion
points is what covers characteristic `2`.

# Statement: the Weyl quotient of a torus in a smooth affine group

Worker 235.

`Langlands.GroupScheme.SmoothAffineTorusWeylQuotientStatement.{u} : Prop` is a
statement-only definition for every universe `u`. This pair states the torus case
of Conrad's general smooth affine normalizer/centralizer quotient theorem. It
does not supply a proof.

## Objects and hypotheses

The proposition quantifies over an arbitrary scheme `S : Scheme.{u}` and an actual
group scheme `G : GroupScheme S`, assuming `Smooth G.X.hom` and
`IsAffineHom G.X.hom`. It then quantifies over an actual commutative group scheme
`T : CommGroupScheme S` and a homomorphism `t : T.toGrp ⟶ G` with:

- `RelativeTorus.IsTorus T.toGrp`: an étale cover of `S` on which the base changes
  of `T` are finite-rank split tori; the rank may vary on the cover;
- `IsClosedSubgroup t`: the scheme map `t.hom.hom.left` is a closed immersion.

These are all the hypotheses. The base is unrestricted, the ambient group need
not be reductive or connected, and the torus need not be maximal.

## Actual normalizer and centralizer

The conclusion constructs group schemes `N`, `Z`, `W` over `S` and homomorphisms
`n : N ⟶ G`, `z : Z ⟶ G` and `q : N ⟶ W`. Both `n` and `z` satisfy
`IsClosedSubgroup`, together with
`(torusNormalizer t).IsRepresentedBy n` and
`(torusCentralizer t).IsRepresentedBy z`, respectively.

Here `SubgroupFunctor.IsRepresentedBy` requires a monomorphism over `S` and
equality of the range subgroup functor with the specified functor. Thus, for
every test scheme `U : Over S`, a point of `G` factors through `n` exactly when
it belongs to the published `torusNormalizer t`, and it factors through `z`
exactly when it belongs to the published `torusCentralizer t`.

These are the existing functors, with their full refinement quantifiers.
A point `g : U ⟶ G.X` belongs to the normalizer when, after every map
`a : V ⟶ U` of test schemes, conjugation by `a ≫ g` and by its inverse
preserves the points factoring through `t`. It belongs to the centralizer when,
after every such refinement, it commutes with every point of `T` mapped into
`G`. These conditions express normalization and centralization of the
base-changed subgroup as a functor, including tests with nilpotents.

## Quotient geometry and the all-test kernel

The structure map `W.X.hom` is separated, quasi-compact and étale.
An étale morphism is locally of finite presentation; together with
quasi-compactness and separatedness, these properties give the finite
presentation appearing in Conrad's theorem. The statement asserts no finiteness
of `W` over `S`.

The underlying scheme map `q.hom.hom.left` is flat, surjective and locally of
finite presentation, so it is an fppf covering. For every test scheme
`U : Over S` and every `y : U ⟶ N.X`, the proposition requires

```text
y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U.
```

The `1` on the left is the identity element of the group of `U`-points of `W`,
or equivalently the identity section of `W` composed with `U → S`.
The equivalence identifies the kernel on every test scheme with the centralizer
viewed inside the normalizer. Its right side refers to the centralizer in `G`,
through `n`, rather than to independently supplied kernel data.

This is the fppf quotient `N_G(T)/Z_G(T)`. Indeed, the cover condition gives
fppf-local lifts of every `W`-point to `N`, by pulling back `q`. The kernel
condition says that two such lifts have the same image exactly when their ratio
belongs to `Z_G(T)`. Representability of the two subgroup functors supplies
their inclusions, with `Z_G(T)` contained in `N_G(T)`. Consequently the
sheafification of the pointwise quotient is represented by `W`. This does not
assert that every `W(U)` is the raw quotient `N(U)/Z(U)` without sheafification.

## Original source and correspondence

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. Registered source:
`conrad-2014-reductive-group-schemes`, readable file
`/home/taskhub/central-library/Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`,
SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The printed page numbers agree with one-based PDF page numbers.

- **Theorem 2.3.1, p.67, proof pp.68–69:** for a smooth affine group over a
  scheme and a subgroup of multiplicative type, the normalizer modulo the
  centralizer is represented by a separated étale group scheme of finite
  presentation. The Lean statement restricts the subgroup to a relative torus,
  a special case of multiplicative type, and expresses finite presentation by
  quasi-compactness together with the stated separated étale geometry. It
  extracts this quotient conclusion; it does not state the theorem's other
  homogeneous-space conclusions.
- **Proposition 2.1.2, p.56:** the normalizer is a finitely presented closed
  subgroup, smooth when the ambient group is smooth. Its all-base-change
  normalizer functor is the one encoded by `torusNormalizer t`.
- **Definition 2.2.1, p.64, and Lemma 2.2.4, pp.64–65:** the functorial
  centralizer is represented by a finitely presented closed subgroup, smooth
  for a multiplicative-type subgroup in a smooth ambient group. Its functor
  is the one encoded by `torusCentralizer t`.

For the representability results, smoothness and affineness of `G → S` imply
finite presentation: smoothness gives local finite presentation, and an affine
morphism is quasi-compact and separated. The étale-local split-torus hypothesis
places `T` in the multiplicative-type case. The closedness and functor identities
in the conclusion therefore match these source results.

The source constructs the fppf quotient sheaf. Its projection is a torsor under
the smooth centralizer supplied by Lemma 2.2.4; it is consequently smooth and
surjective, hence flat and locally of finite presentation. This explains the
explicit cover and all-test kernel formulation in Lean. The statement records
these consequences without asserting smoothness of the chosen `N` or `Z`.

## Library interfaces and remaining proof

The Lean module imports only
[`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md) and
[`Torus.Relative`](Relative.md). The former supplies the actual subgroup
functors, their representation predicate and `IsClosedSubgroup`; the latter
supplies the general-base torus predicate and the scheme geometry interfaces.
No auxiliary supplied quotient, reductivity predicate or maximality predicate
occurs in the statement.

[`WeylGroupSchemeFiniteEtaleStatement`](WeylGroupSchemeFiniteEtaleStatement.md)
is the separate reductive maximal-torus target, based on Conrad
Proposition 3.2.8. The present general construction leaves its finiteness
argument as an additional obligation. A proof of the proposition defined in
this pair remains required.

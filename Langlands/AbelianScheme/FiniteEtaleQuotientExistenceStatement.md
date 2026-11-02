# Existence of quotients by finite étale subgroups of projectively embedded abelian schemes

`Langlands.AbelianScheme.FiniteEtaleQuotientExistenceStatement` is a
universe-polymorphic proposition (a `def` returning `Prop`, with universe
parameter `u`). It is a theorem target only. This module constructs no quotient
and proves nothing about quotients; the proof is a separate obligation.

## The proposition

For every scheme `S : Scheme.{u}` with `[IsLocallyNoetherian S]`, every
`A : Langlands.AbelianScheme S`, every natural number `n`, and every scheme
morphism

```text
i : A.X.left ⟶ Langlands.AlgebraicGeometry.RelativeProjectiveSpace S n
```

with `[IsClosedImmersion i]` and

```text
i ≫ Langlands.AlgebraicGeometry.RelativeProjectiveSpace.toBase S n = A.X.hom,
```

the proposition asserts `Nonempty K.QuotientData` for every
`K : Langlands.AbelianScheme.FiniteEtaleSubgroup A`.

The meanings are those of the imported published modules, which are not
changed:

- `Langlands.AbelianScheme` (module `Basic`) is an actual commutative group
  scheme over `S` whose structure morphism `A.X.hom : A.X.left ⟶ S` is smooth
  and proper with geometrically connected fibres.
- `Langlands.AlgebraicGeometry.RelativeProjectiveSpace S n` is the actual base
  change to `S` of the integral polynomial-Proj model `ProjectiveSpace
  (ULift.{u} ℤ) n`, and `toBase S n` is its projection to `S`.
- `FiniteEtaleSubgroup A` (module `FiniteEtaleQuotient`) is an actual
  commutative group scheme `K.G` over `S` with a homomorphism
  `K.inclusion : K.G ⟶ A.toCommGroupScheme` whose underlying scheme morphism
  is a closed immersion, and whose structure morphism `K.G.X.hom` is finite and
  étale.
- `K.QuotientData` is the prerequisite's published structure, used directly
  with all of its fields. Its elements are an abelian scheme `B` over the same
  `S`, a homomorphism `q : A ⟶ B` whose underlying scheme morphism
  `AbelianScheme.hom q` is finite, étale and surjective, and the cartesian
  square

  ```text
  IsPullback (CommGroupScheme.hom K.inclusion) K.G.X.hom
    (AbelianScheme.hom q) η[B.X].left
  ```

  of actual scheme morphisms. It says that `K` is exactly the scheme kernel of
  `q`, the fibre product of `q` with the unit section of `B`.

So `B`, `q`, the finiteness, étaleness and surjectivity of `q`, and the kernel
square are all outputs of the existential `Nonempty`. None of them is a
hypothesis. `Nonempty` asserts existence only; it selects no particular
quotient.

## Scope of the quantifiers

- The base is any locally noetherian scheme. It may be nonreduced,
  disconnected, non-affine or empty. No integrality, excellence, dimension or
  characteristic condition appears.
- `K` ranges over all finite étale closed subgroups. The subgroup is an actual
  scheme with its own group structure, not a set of points or an abstract
  finite group. No constant rank or order of `K` is specified.
- `n` ranges over all natural numbers, including `0`.
- `i` and the equation are data and a hypothesis supplied by the user of the
  statement. Since they are universally quantified, the proposition is
  equivalent to its version with the premise "some closed immersion over `S`
  into some relative projective space exists". The equation is an equality of
  scheme morphisms, not an identification up to isomorphism. No embedding is
  chosen by the statement, and the quotient is not required to be compatible
  with `i`.
- The instance `u := 0`, `FiniteEtaleQuotientExistenceStatement.{0}`, is the
  universe-zero case needed by the consumer.

The projectivity hypothesis is the displayed embedding into the published
relative projective space. `Langlands.AlgebraicGeometry.IsHProjective` is not
used: it is defined only over affine ring bases, and `S` here is arbitrary. No
other notion of projectivity, quotient or abelian scheme is introduced. There
are no hypotheses on polarizations, line bundles, relative dimension or level
structures.

## Source and derived provenance

The source is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian
Varieties*, preliminary chapters. It is registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`, file
`/home/taskhub/pilot/literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
The pages cited below were read directly. No source-specific errata note was
found in the available project notes.

The source contains no single theorem with this conclusion. The proposition
is a derived arbitrary-base specialization, and its expected proof uses the
source results as follows.

1. **Free translation action.** Definition (4.1)(ii), printed p. 49 (PDF
   p. 53), calls an action free when the graph morphism
   `Ψ = (ρ, pr₂) : G ×_S X → X ×_S X` is a monomorphism, and strictly free when
   it is an immersion. Example (4.3), printed p. 50 (PDF p. 54), states that a
   subgroup scheme acting on a group scheme by translation acts strictly
   freely. Here `K` acts on `A` through `K.inclusion`. `K.G` is finite and
   étale over `S`. An étale morphism is flat and locally of finite
   presentation, so `K.G` is finite locally free over `S`.
2. **Quotient and torsor square.** Theorem (4.16), printed p. 55 (PDF p. 59),
   takes a finite locally free group scheme acting on an `S`-scheme `X` such
   that the orbit of every closed point lies in an affine open subset. Part
   (i) gives the quotient `Y` as an `S`-scheme. Since `S` is locally
   noetherian and `X` is of finite type over `S`, it also says that
   `q : X → Y` is finite and surjective and `Y` is of finite type over `S`.
   Part (iii) says that for a free action `q` is finite locally free and
   `G ×_S X → X ×_Y X`, induced by `Ψ`, is an isomorphism (the torsor square).
   Here `X = A.X.left`, which is of finite type over `S` because `A.X.hom` is
   proper.
3. **Orbit affineness from the embedding.** Remark (4.17)(i), printed p. 56
   (PDF p. 60), states that the affineness condition of (4.16) holds when `X`
   is quasi-projective over `S`. The displayed closed immersion `i` over `S`
   into relative projective space is the projectivity input used for this
   condition. The remark argues with finite sets of closed points of
   projective space over a ring.
4. **Group structure and kernel.** (4.37), printed p. 65 (PDF p. 69), says
   that a representable fppf quotient of a group scheme by a normal subgroup
   scheme is a group scheme and the quotient map is a homomorphism. `K` is
   normal because `A` is commutative. Theorem (4.39)(c), printed p. 66 (PDF
   p. 70), gives this representability for a finite locally free closed
   subgroup under an affineness condition, citing Theorem (4.16). The scheme
   kernel of `q` is then identified with `K` by restricting the torsor
   isomorphism along the unit section of `A`. This is the `isPullback` field,
   with kernels in the sense of Definition (3.13), printed pp. 36–37 (PDF
   pp. 40–41).
5. **Abelian-scheme output over a general base.** That the quotient is again
   an abelian scheme, that is, smooth, proper and with geometrically connected
   fibres over `S`, is not stated by the source over a general base. It must
   be derived by descending these properties from `A` along the finite locally
   free surjection `q`.
6. **Étaleness of the quotient map.** Since `K.G ×_S A ≅ A ×_Y A`, the base
   change of `q` along itself is a base change of the étale morphism
   `K.G.X.hom`. Étaleness of `q` then follows by descent along the fppf cover
   `q`. This step uses the hypothesis that `K` is étale. For a merely finite
   locally free `K`, the source gives only a finite locally free quotient map.

Example (4.40), printed p. 66 (PDF p. 70), concerns abelian varieties over a
field. It obtains the quotient by a closed subgroup scheme from Theorem (4.38)
and Theorem (4.35) and says the quotient is again an abelian variety. On its
own it does not give the conclusion over a general locally noetherian base,
and the proposition is not a verbatim restatement of it.

## Not included

The proposition asserts existence only. It does not include:

- a proof, or a construction of `B` or `q`;
- a universal property or factorization of homomorphisms vanishing on `K`
  through `q`, as in (4.37);
- uniqueness of the quotient;
- compatibility with arbitrary base change, as in Theorem (4.16)(ii)–(iii);
- descent of actions of integral orders, endomorphisms or polarizations to
  the quotient.

It assumes no CM representability, no representing scheme and no integral
model.

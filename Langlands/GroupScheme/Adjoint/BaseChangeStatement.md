# Field base change of actual adjoint quotients

Authors: Worker 1401 and Worker 1410.

This module states that field base change preserves the existing actual
adjoint-quotient interface `Langlands.GroupScheme.IsAdjointQuotient` of
`Adjoint.Quotient`. It proves nothing about existence or base change. It adds
conditional declarations that only reuse the existing comparison
isomorphism.

## Statement

`Langlands.GroupScheme.AdjointQuotientBaseChangeStatement.{u}` is the
proposition below. Take fields `k K : Type u` with `[Algebra k K]`, group
schemes `G A : GroupScheme (Spec (CommRingCat.of k))` and a homomorphism
`q : G ⟶ A`. If `IsAdjointQuotient q`, then

```
IsAdjointQuotient ((GroupScheme.baseChange (algebraBaseMap k K)).map q).
```

Here `algebraBaseMap k K` is the Library's `Spec.map` of `algebraMap k K`,
a morphism `Spec K ⟶ Spec k` (module `Torus.LatticeGalois`).
`GroupScheme.baseChange f` is the Library's `(Over.pullback f).mapGrp`: the
actual scheme pullback along `f` with its induced group law. Write `G_K` and
`A_K` for the images of `G` and `A`, and `q_K : G_K ⟶ A_K` for the image of
`q`. Then `q_K` is the actual base-changed homomorphism, not a separately
chosen map.

The hypothesis is only the quotient interface for `q` over `k`. Nothing is
assumed about `G_K`, `A_K` or `q_K`. No base-changed quotient is supplied, and
base-change preservation is not a premise.

Unfolded over `Spec K`, the conclusion contains every field of
`IsAdjointQuotient q_K`:

1. `IsConnectedReductive G_K`: `G_K` is smooth, affine and connected, with
   trivial unipotent radical after base change to `AlgebraicClosure K`. Also
   `IsAdjoint A_K`:
   `A_K` is semisimple with a finite actual centre representative, and the
   all-test centre functor of `A_K` over `Spec K` is `⊥`.
2. The underlying scheme morphism of `q_K` is flat, surjective and locally of
   finite presentation.
3. `IsSchemeTheoreticCenter (kernelι q_K)`. The actual pullback kernel of `q_K`
   is a closed subgroup of `G_K` whose range is the full centre functor of
   `G_K`. Centrality is tested on every scheme over `Spec K` and after every
   further base morphism.
4. Group universal property over `K`: for every group scheme `H` over
   `Spec K`, every homomorphism `G_K ⟶ H` that kills the centre of `G_K`
   factors uniquely through `q_K`.
5. Scheme universal property over `K`: for every `Y : Over (Spec K)`, every
   scheme morphism `G_K.X ⟶ Y` that is invariant under the centre of `G_K`
   factors uniquely through the underlying morphism of `q_K`.

## Scope

The universe `u` and both fields are arbitrary. Every ring homomorphism
between fields is injective, so `[Algebra k K]` is exactly a field extension.
The extension need not be algebraic, finite, separable or normal. Neither field
needs to be perfect or algebraically closed, and the characteristic is
unrestricted.

The centre is the scheme-theoretic centre and need not be smooth or reduced.
For example, CGP's example after Definition A.1.9 says that the centre of
`SL_p` in characteristic `p` is `μ_p`. The statement requires the
base-changed kernel to represent this full centre functor, including its
infinitesimal part. It imposes no finiteness on `q_K` or on its kernel.

`q` is the quotient of a connected reductive group by its full centre, as in
Milne's Remark 17.63. Its target is the adjoint group, which is a quotient of
`G`. This is not the simply connected central cover of the derived group,
which maps onto the derived group. The statement says nothing about simply
connected covers or other central isogenies.

## Categorical scope of the universal properties

Both universal properties in the conclusion are categorical. The group one is
stated in the category `GroupScheme (Spec K) = Grp (Over (Spec K))`, and the
scheme one in `Over (Spec K)`. All objects lie in universe `u`. Targets need
not be of finite type, affine or separated. The interface records the fppf
properties and the kernel separately; the statement asserts no further
sheaf-theoretic exactness.

The statement does not imply that `A_K(K)` is `G(K)/Z(K)`. It also does not
imply that `q_K` is surjective on `K`-points or on `T`-points. Surjectivity is
surjectivity of the underlying morphism of schemes. For example, for the
adjoint quotient `SL_2 → PGL_2` over `ℚ`, the map `SL_2(ℚ) → PGL_2(ℚ)` is not
surjective: through the determinant, the quotient of `PGL_2(ℚ)` by its image
is `ℚ^×/ℚ^{×2}`. No quotient-of-rational-points statement should be inferred.

## Comparison with an independently supplied quotient

Suppose `h : AdjointQuotientBaseChangeStatement`, `hq : IsAdjointQuotient q`,
and `q' : G_K ⟶ A'` with `hq' : IsAdjointQuotient q'`. Here `q'` may be an
adjoint quotient of `G_K` constructed independently, for instance by an
existence theorem over `K`. The conditional helpers are:

- `AdjointQuotientBaseChangeStatement.isAdjointQuotient h hq` applies the
  statement to the supplied quotient.
- `AdjointQuotientBaseChangeStatement.quotientIso h hq hq'` is the canonical
  comparison from the base-changed quotient to the supplied quotient.
- `AdjointQuotientBaseChangeStatement.comp_quotientIso_hom` records its
  compatibility with the maps from `G_K`.

The second submitted comparison interface reuses these same declarations:

- `AdjointQuotientBaseChangeStatement.comparisonIso h hq hq' : A_K ≅ A'` is
  an abbreviation for `h.quotientIso hq hq'`, which unfolds to
  `(h k K G A q hq).quotientIso hq'`.
- `AdjointQuotientBaseChangeStatement.comp_comparisonIso_hom` proves
  `q_K ≫ (comparisonIso h hq hq').hom = q'`. Its proof reuses
  `h.comp_quotientIso_hom hq hq'`.

Both are conditional on `h` and only reuse the Library's existing
`IsAdjointQuotient.quotientIso` and `IsAdjointQuotient.comp_quotientIso_hom`.
The module adds no new uniqueness theorem. The existing
`IsAdjointQuotient.hom_ext`, applied to `h k K G A q hq`, shows that any
homomorphism `A_K ⟶ A'` composing with `q_K` to `q'` is this comparison.

## Source correspondence

Provenance is derived. Neither source states this proposition as one
numbered result. The conclusion assembles base-change facts about each part
of the quotient interface. The sources, read in the registered files, are
listed below.

- Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
  Definition A.1.8, printed p.468 / PDF p.494. Over a field, the kernel
  `f⁻¹(1)` is the unique closed subscheme representing
  `S ↝ ker(G(S) → G′(S))`. This is the `kernel`/`kernelι` in item 3.
  Formation of the actual pullback kernel commutes with base change; the
  Library records this as `kernelBaseChangeIso`.
- CGP Definition A.1.9 and the discussion after it, printed pp.468–469 /
  PDF pp.494–495. It says that "the formation of `Z_G(V)` and `N_G(V)`
  commutes with any extension of the ground field, but they need not be
  smooth". The example given is `Z_G(G) = μ_p` for `G = SL_p` in
  characteristic `p`. This is the source for the centre part of item 3 over
  an arbitrary extension `K / k`.
- CGP Definition A.1.10, printed p.469 / PDF p.495. It defines the
  scheme-theoretic centre `Z_G = Z_G(G)` of a smooth group through its points
  over every algebra. It also notes that formation of the identity component
  commutes with any extension of the ground field.
- CGP Definition A.1.11, printed p.470 / PDF p.496. The quotient `G → G/H` is
  faithfully flat and initial among morphisms invariant under right
  translation by `H`. For normal `H` it is a homomorphism with kernel `H`,
  proved by descent. These are items 2, 4 and 5.
- CGP Example A.1.12, printed p.470 / PDF p.496. A surjective homomorphism of
  smooth affine groups has the quotient property "from descent theory and the
  isomorphism `H × G ≃ G ×_{G′} G`". In general, a surjective homomorphism
  between affine groups of finite type over a field is a quotient map if and
  only if it is flat. Flatness, surjectivity and the kernel are compatible
  with base change, so this is how the quotient property passes to `K`.
- J. S. Milne, *Algebraic Groups* (2017), proof of Corollary 17.62(c)–(e),
  printed pp.372–373 / PDF pp.388–389. Part (c): "The formation of the centre,
  and the largest subtorus, commute with extension of the base field". Part
  (d) uses `(G/R(G))_{k^a} ≃ G_{k^a}/R(G)_{k^a}`, so quotient formation
  commutes with extension of the base field. Part (e) gives that `G/Z(G)` has
  trivial centre.
- Milne, Remark 17.63, printed p.373 / PDF p.389: "An adjoint group is a
  semisimple group with trivial centre. The quotient of a reductive group `G`
  by its centre is an adjoint group (17.62e), called the adjoint group
  `G^ad` of `G`." Accordingly the statement says that `(G^ad)_K` with `q_K` is
  the adjoint group of `G_K`.

Milne's algebraic groups are of finite type. In 6.46, printed p.135 / PDF
p.151, a connected group variety over `k` is reductive if its geometric
unipotent radical `R_u(G_{k^a})` is trivial. The Library's
`IsConnectedReductive` likewise uses the unipotent radical after base change
to `AlgebraicClosure k`, together with smoothness, affineness and
connectedness. The `Adjoint.Quotient` Markdown explains why the interface
records the group and scheme universal properties as explicit fields.

Further source locators from the companion contribution are Milne's
Proposition 1.92 and its following paragraph (printed pp.33–34 / PDF
pp.49–50) for centralizers, Definition 5.5 and Theorem 5.13 (printed
pp.99 and 101 / PDF pp.115 and 117) for quotient maps and factorization,
Proposition 19.5 (printed pp.398–399 / PDF pp.414–415) for semisimplicity
under field extension, and Proposition 19.13 (printed p.400 / PDF p.416)
for reductivity under field extension.

Errata: the registered official Milne errata snapshot of 2026-11-02 has no
correction to p.135 or pp.372–373. For CGP, the registered author-page check of
2026-11-02 found no dedicated errata link for the second edition. That check
is not a claim that no corrections exist.

## Proof boundary

This module only states the proposition and gives the conditional
comparison declarations above. It adds no axiom or proof hole. Its
publication proves no base-change or existence result, and it constructs no
adjoint quotient over `k` or over `K`. A separate exact-target proof must
establish the statement for every universe and field extension. A Lean proof
may take any valid route.

One expected route follows. The centre functor of `G_K` agrees formally with
that of `G` on schemes over `Spec K`, because the Library centre tests every
further base morphism. The kernel uses `kernelBaseChangeIso`. Flatness,
surjectivity and local finite presentation are stable under base change. The
universal properties follow by fppf descent along `q_K`, as in CGP A.1.11 and
A.1.12. Connectedness passes to `G_K` because a connected group scheme over a
field with a rational point is geometrically connected. Trivial geometric
unipotent radical passes to `G_K` through an embedding of algebraic closures.

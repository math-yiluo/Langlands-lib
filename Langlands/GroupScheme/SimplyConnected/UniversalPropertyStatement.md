# Unique factorization for semisimple simply connected central covers

`Langlands.GroupScheme.SimplyConnectedCentralCoverUniversalProperty.{u}`
is a proposition stating the following implication for every field
`k : Type u`, actual group schemes `C` and `G` over `Spec k`, and actual
group-scheme homomorphism `π : C → G`:

```text
IsSimplyConnected C →
IsSemisimple G →
IsCentralIsogeny π →
HasCentralCoverUniversalProperty π.
```

Unfolding the conclusion, for every actual group scheme `H` over `Spec k`
and homomorphism `q : H → G`, if `H` is semisimple and `q` is a central
isogeny, there is a unique actual group-scheme homomorphism `a : C → H`
such that `a ≫ q = π`, that is, `q ∘ a = π`. The lift lands in the source
`H` of the incoming cover `q`. Uniqueness is equality of homomorphisms in
`Langlands.GroupScheme (Spec k) = Grp (Over (Spec k))`.

The three premises are the published intrinsic predicates.
`IsSimplyConnected C` includes semisimplicity of `C` and says that every
incoming central isogeny from a semisimple group to `C` is an isomorphism.
`IsSemisimple G` uses geometric-fibre reductivity and finiteness of the full
scheme-theoretic centre. `IsCentralIsogeny π` requires the actual scheme
morphism to be finite, flat, surjective and locally finitely presented,
with its actual kernel central on every test scheme. The same convention
applies to `q`. All test schemes, including nonreduced schemes, remain in
these imported definitions. There is no smoothness assumption on a centre
or kernel and no assertion of surjectivity on rational points.

The statement has arbitrary universe `u`, arbitrary characteristic and
arbitrary field `k`, including imperfect fields. Its premises include no
universal law, chosen covering group, lift, section, base-change law or
`IsSimplyConnectedCover π`. Once proved, the implication supplies precisely
the fourth field of `IsSimplyConnectedCover π` from its first three fields.
It asserts the universal property of a supplied map; it asserts no
existence of a covering map or compatibility with field extension.

This is a derived semisimple specialization of the following sources.

- Conrad, Gabber and Prasad, *Pseudo-reductive groups*, second edition
  (2015), the definition immediately before Corollary A.4.11 and
  Corollary A.4.11(1), printed pp.500–501 / PDF pp.526–527, give the
  incoming-central-isogeny criterion for simple connectedness and the
  existence and uniqueness of simply connected central covers over any
  field. The present proposition singles out the incoming factorization
  law rather than restating that existence or field-extension result.
- Milne, *Algebraic Groups* (2017), Definition 18.1, printed p.387 /
  PDF p.403, defines central and multiplicative isogenies and explains
  why they agree for a reductive source. Definitions 18.5 and 18.7,
  printed pp.388–389 / PDF pp.404–405, define simple connectedness and
  universal coverings. Proposition 18.8, printed p.389 / PDF p.405,
  supplies the unique factorization through an incoming multiplicative
  isogeny, under the additional condition that the field or the target
  group is perfect. Proposition 19.15 and its proof, printed pp.400–401 /
  PDF pp.416–417, identify the simple-connectedness criterion with the
  semisimple central-isogeny convention used here.
- Milne's complete official errata, retained as the HTML snapshot of
  2026-11-02, Chapter 18, entry for printed p.389, corrects the target
  of the factorization in Proposition 18.8 to the source of the incoming
  isogeny. With `G' = H`, the corrected map is exactly `a : C → H`.
  That snapshot has no correction to Proposition 19.15. No retained
  project errata note for the CGP source was found.

The source correspondence is derived rather than a literal translation
of Proposition 18.8: in the semisimple setting its group-perfectness
condition must be discharged by a structural result, without restricting
the field to be perfect. A proof following that proposition must also
justify its central-to-multiplicative and simple-connectedness comparisons
and its fibre-product section argument on the actual group schemes.
Alternatively, it may construct an appropriate semisimple part of the
fibre product and apply the incoming-isogeny criterion. These are proof
obligations; none is additional data in the proposition.

This module defines the target proposition and proves no instance of it.
The existing `IsSimplyConnectedCover.lift`, `lift_unique`, `hom_ext` and
canonical `iso` consume the explicit universal property already stored
in `IsSimplyConnectedCover`. They therefore do not prove this implication
from the three intrinsic hypotheses. A separate exact-target proof is
required.

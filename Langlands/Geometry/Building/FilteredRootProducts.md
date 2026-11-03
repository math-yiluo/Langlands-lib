# Actual filtered root blocks and ordered multiplication

This definition unit supplies the finite real-depth specialization of
Kaletha–Prasad, Definition 7.3.3(1), printed p. 247 (book PDF p. 278):

`U_{a,x,f} = U_{a,x,f(a)} U_{2a,x,f(2a)}`.

It uses the published actual data `D : KPApartmentData i ω`, its apartment
point `x`, and `D.filtration`. The factors are subgroups of the actual
`Langlands.GroupScheme.rationalPoints G`; they come from the actual
relative-root subgroup functors. The character `a` is explicit.

`doubleFiltration` is `D.filtration x (2 • a) r` when `2 • a` is an actual
relative root, and the trivial subgroup otherwise, following the convention
preceding Definition 6.3.4 (printed p. 223, book PDF p. 254). Its two
conditional identities follow by unfolding the definition. Its inclusion
in `doubleRootGroupPoints i a` uses the existing inclusion of a filtration
subgroup in its actual root group.

`filtrationBlock x f a` is the literal set product of those two filtration
groups. The function `f` here is real-valued on the character lattice.
Only its values at `a` and `2 • a` are used. This is a specialization of
the source's more general depth notation; strict depths such as `0+`
and infinite depths are outside this unit. The membership lemma is the
definition of a set product.

The block is not replaced by its first factor. Remark 7.3.4, printed
p. 247 (book PDF p. 278), explains why such a replacement can fail when
the doubled-root level is smaller than twice the first level. No
concavity premise is needed to define the set product. Identifying it
with a subgroup, or with a filtered subgroup inside a unipotent radical,
requires separate structural results.

`orderedFiltrationBlockProduct` sends a dependent family of block
elements to their product in the order `0, …, n-1`, implemented by
`List.ofFn` and `List.prod`. This multiplication map is internal
notation for the fixed-sign products in Proposition 7.3.12(3) and the
chamber decompositions in Corollary 7.4.9. Later targets must require
that the index list enumerate all indivisible roots of one sign once;
this definition allows any list and claims no injectivity, range,
decomposition, or existence of valid building data.

The statements of those results still require their corrected ambient
hypotheses. In particular, `KPApartmentData` alone is not a certificate
for full V6/V7, affine-root-system properties, the equivariant apartment
family, or AS5. This definition unit does not define the full chamber
Iwahori or identify a sharp group with a parahoric.

Sources:

- `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
  Definition 7.3.3(1), Remark 7.3.4, and the convention preceding
  Definition 6.3.4.
- `kaletha-prasad-2024-corrections`, 1 November 2024, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
  PDF pp. 33–34, for the corrected Chapter 7 scope of the later
  decomposition targets. Those targets are not asserted here.

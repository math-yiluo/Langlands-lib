# Represented subgroups under an ambient isomorphism

This internal derived construction works over an arbitrary base scheme `B`.
Let `i : H ⟶ G` and `j : H' ⟶ G'` represent subgroup functors `F` and `K`,
let `e : G ≅ G'`, and assume the full subgroup-functor equality
`K.comap e.hom = F`. The existing `IsRepresentedBy` predicate requires that
the underlying inclusions are monomorphisms and have the specified ranges on
every scheme test.

`IsRepresentedBy.isoOfComap` constructs an actual group-scheme isomorphism
`q : H ≅ H'`. The `hom_comp` and `inv_comp` theorems prove
`q.hom ≫ j = i ≫ e.hom` and `q.inv ≫ i = j ≫ e.inv`.
`isoOfComap_unique` states that the forward inclusion square determines `q`
uniquely. The `hom_points` and `inv_points` formulas give the corresponding
identities after precomposition by any point of any scheme test.

The implementation reuses `IsRepresentedBy.comp_iso` from
`Dynamic/AffineRepresentability.lean`, which has no affine hypothesis, with
`e.symm`. Thus `j ≫ e.inv` represents `K.comap e.hom = F`.
`isoOfIsRepresentedBy` from `RepresentedSubgroup.lean` identifies this
representative with `i`. Its inclusion identity gives the forward square
after cancellation of `e.inv`; the inverse identity gives the reverse square.
The published `hom_ext` proves uniqueness, and precomposition of the squares
proves the all-test formulas. No external mathematical assertion is introduced.

Representatives and the comap equality are inputs. The construction proves no
representability existence result and imposes no smoothness, affine, field,
or reduced-test restriction.

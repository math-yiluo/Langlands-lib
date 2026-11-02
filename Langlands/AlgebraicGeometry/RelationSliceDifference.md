# Difference of two arrows in a relation slice

For a scheme equivalence relation `(t,s)` and a morphism `g : V → U`, write
`B = V ×_{g,U,t} R`, with projection `p : B → V` and associated map
`h = s ∘ pr₂ : B → U`. Two arrows in `B` above the same point of `V` have the
same source. Composing the inverse of the first with the second gives an
arrow from the first target to the second. The definition `difference` makes
this construction as a morphism `B ×_V B → R`, using the symmetry and
transitivity fields of the published `AtlasRelation.IsEquivRel`.

The projection identities state that composing this difference map with `t`
gives `h` after the first projection, and composing with `s` gives `h` after
the second. Both corresponding squares are pullbacks. For the square over
`t`, composing a given first arrow with a relation arrow constructs the
second arrow. For the square over `s`, compose a given second arrow with the
inverse relation arrow to construct the first. The monomorphism of the
relation into `U × U` supplies uniqueness in both universal properties.

This is an internal groupoid construction for propagating properties of slice
maps. Its inputs are just the published relation axioms and existing scheme
pullbacks; no smoothness, finiteness, quotient existence, or unproved Library
statement is assumed. The already published `FiniteLocusInvariant` module is
used for `IsEquivRel.hom_ext`, which is proved directly from that monomorphism.

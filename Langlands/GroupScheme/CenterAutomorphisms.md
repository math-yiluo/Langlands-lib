# Automorphisms fixing the full scheme-theoretic centre

This internal structural interface uses the Library's actual centre subgroup
functor. It applies to every group scheme over any base scheme, at every universe
parameter.

`AutomorphismFixesCenter f` means that for every test scheme `T` over the base,
every point of the full scheme-theoretic centre over `T` is fixed by the actual
group-scheme automorphism `f`. Centrality here also tests all restrictions to
further test schemes, as in `Rational/Characters`. In particular this definition
retains nonreduced centres in positive characteristic.

The elementary lemmas prove that this property holds for the identity and is
closed under composition and inversion. They also prove its invariance under
transport through an actual group-scheme isomorphism. The inverse and transport
proofs use `mem_center_comp_iso` from `Reductive/Semisimple`, which preserves the
full centre on every test scheme, and the actual inverse identities.

Every `innerIso` fixes the centre. Its proof evaluates the inner automorphism on
each test scheme, uses the defining commutation property of a central point, and
cancels the conjugating point. Composition on either side with any centre-fixing
automorphism preserves and reflects centre fixation. These equivalences support
changes of model and inner corrections without losing a nontrivial centre action.

The provenance is internal: the interface packages actual pointwise equality,
and the proofs follow directly from the published centre and inner-automorphism
definitions. This file does not classify norm-one group automorphisms or prove
any local Tits-index exclusion.

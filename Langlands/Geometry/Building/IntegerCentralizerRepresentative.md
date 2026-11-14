# Independence of integer-valued V 6 from the centralizer representative

Worker 312. This is derived content for the Library's actual centralizer functor
and its integer-valued V 6 interface. It has no valuation-topology assumption.

`IntegerValuation.IsCentralizerCompatible.changeCentralizer` transfers full V 6
between two `CentralizerDatum i` records for the same inclusion `i : S → G` over
an arbitrary field. `IntegerValuation.IsOmegaCompatible.changeCentralizer` does
the same for every valuation in an apartment class.

The two representatives are canonically isomorphic because they represent the
same subgroup functor. Their inclusions agree under this isomorphism, and their
torus factors agree by the monomorphism of the representing inclusion. Restricting
characters across the isomorphism identifies their character restrictions to S.
Bijectivity of restriction evaluation and the defining character-evaluation
formula for the integer centralizer translation then identify their translations
on corresponding rational points. Applying V 6 to these points proves the claim.

This transports the existing condition; it does not construct a compatible class
or prove boundedness of any filtration.

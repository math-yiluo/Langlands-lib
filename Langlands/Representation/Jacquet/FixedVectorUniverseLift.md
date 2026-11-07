# Fixed-vector generation and actual subquotients under carrier lifts

Author: Worker 1649. This is internal universe infrastructure for the proof of
Renard VI.9.4. It derives transport facts from the published actual carrier
lift, fixed-vector equivalence and smooth subquotient presentation. The carrier
lift implementation and these transport lemmas are not attributed to a
separate theorem in the literature.

The group universe `uG`, original carrier universe `uV` and lift universe `uX`
are independent. The lifted representation has carrier `ULift.{uX} A` in
`Type (max uV uX)`, with its original action conjugated by `up` and `down`.
Only a group and its topology are required. In particular these results use
no compactness, admissibility, finite dimension, finite length or irreducibility
assumption.

`fixedVectorGenerated_iff_of_equiv` transports the exact invariant-submodule
criterion for generation by fixed vectors across an actual representation
equivalence, allowing its two carriers to lie in different universes. Each
direction applies `fixedVectorGenerated_of_surjective` to the corresponding
equivariant map. `fixedVectorGenerated_universeLift_iff` specializes this to
the published `SmoothRep.universeLiftEquiv`.

`fixedVectorsUniverseLiftEquiv` restricts that equivalence to the actual
fixed-vector spaces. Its forward and inverse evaluation lemmas are `up` and
`down` respectively. `exists_nonzero_fixed_universeLift_iff` transports a fixed
vector by the corresponding intertwiner and uses injectivity to preserve
nonvanishing. Its forward direction therefore returns a nonzero fixed vector
in the original carrier.

`SmoothRep.IsSubquotient.universeLift` uses the characterization of the
published actual subquotient relation by a smooth witness `C`, an injective
map `C → A` and a surjective map `C → B`. It lifts `C` and both maps with
`SmoothRep.universeLiftFunctor`. Taking `down` proves injectivity of the
lifted inclusion; a preimage under the original quotient map, followed by
`up`, proves surjectivity of the lifted quotient map. The characterization
then constructs the actual subquotient relation between the lifted objects.
This lemma claims preservation only.

For the VI.9.4 application one may take `uX = uF + 1` to apply an existing
large-carrier Jacquet theorem, then use the nonzero-vector equivalence to
return to the independent original universe `uV`. This unit supplies the
transport facts only; the reductive hypotheses and the Jacquet detection
argument remain separate obligations.

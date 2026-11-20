# Products of the actual infinite Whittaker slices

For one supplied cuspidal spectral presentation, `ModelData` describes the
input needed for separation at the infinite places. Each local map takes a
vector of the actual place source model to a function on the corresponding
real or complex general linear group. Some vector has local coefficient
value one at the identity. After fixing the finite tensor and all the other
infinite vectors and group coordinates, the actual coefficient in the
remaining vector and group coordinate is a scalar multiple of this local
map. The scalar can depend on the frozen data. There is one model map for
each place and character.

`placeTuplePoint` assembles a tuple of infinite local group elements into
an actual adelic point with identity finite part. The coordinate comparison
identifies this point with `infinitePoint` when the tuple comes from an
adelic point. A tuple supported at one place gives `realPlacePoint` or
`complexPlacePoint`.

For each infinite place, pair its variable vector with its variable group
element. Fix a normalized vector and the identity group element as the
reference pair. The slice equation expresses the effect of changing this
pair as multiplication by the corresponding model coefficient. Inductively
changing the pairs across the finite set of infinite places gives the
product formula for `tensorWhittaker`.

`exists_normalized_product` fixes the normalized finite references and
uses the value at the tuple of archimedean references and identity group
elements as the common scalar. The reference pure tensor gives a nonzero
actual global vector. `exists_infiniteResidual_ne_zero_of_global` supplies
a nonzero value of its normalized residual. By the product identity that
value would vanish if the scalar were zero. The resulting scalar is
independent of the prescribed infinite vectors and all group points.

`exists_model_real` and `exists_model_complex` show that every actual place
restriction lies in the range of the chosen local map. First move its
finite right translate into the global vector by genuine finite covariance.
The restriction map is linear, since every global Whittaker value is a
linear functional on the cuspidal carrier. On a pure tensor, apply the
slice equation with identity group elements at the other places. The
result is the local model evaluated at a scalar multiple of the chosen
coordinate vector. Induction in the infinite and binary tensor products
carries this range membership to every vector of the actual carrier.

The proof is an internal consequence of the supplied local comparisons and
the Library's actual tensor, point, and coefficient identities.

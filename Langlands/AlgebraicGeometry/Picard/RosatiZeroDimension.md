# Actual Rosati positivity in relative dimension zero

This internal helper treats the zero-dimensional case using the actual geometric objects. It works over every field `k : Type u`, with no algebraic-closure or characteristic assumption. Let `A` be an actual abelian scheme over `Spec k` satisfying the existing predicate `A.HasRelativeDimension 0`.

`HasTrivialOutgoingHom A` is the Prop-valued predicate that for every actual abelian scheme `B` on the same base, all actual integral homomorphisms `A ⟶ B` and all rational homomorphisms `Hom0 A B` are zero.

`hom_eq_zero_of_relativeDimension_zero` applies the published group-scheme theorem `eq_zero_of_smoothOfRelativeDimension_zero_over_field` to the actual underlying group homomorphism. The geometrically connected structure morphism of `A` gives connectedness of its underlying space over the one-point base. The group-scheme theorem uses that the structure morphism is étale, its unit is a rational section, and a connected étale scheme with a rational section is the base scheme. Passing back through additive notation gives the claimed equality of abelian-scheme homomorphisms.

`hom0_eq_zero_of_relativeDimension_zero` unfolds the existing rational Hom as `Q` tensor the actual integral Hom group. Tensor induction reduces to pure tensors, each of which is zero by the integral result, and sums of zero tensors. The combined theorem `hasTrivialOutgoingHom_of_relativeDimension_zero` proves the predicate, and `subsingleton_end0_of_relativeDimension_zero` records that the actual rational endomorphism algebra has just one element.

`Langlands.AbelianScheme.Rosati.positivity_of_relativeDimension_zero` takes the existing prerequisites `P`, actual dual datum `W`, its exact additivity witness `hadd`, an actual map `lam`, and the quantified `HasRationalInverse P W lam` instance. It proves the exact local conjunction used in `PositivityStatement`: symmetry of `traceForm`, nonnegativity on its diagonal, and strict positivity of `geometricEndomorphismTrace A (a * involution P W hadd lam a)` whenever `a` is nonzero. Subsingletonness makes symmetry immediate and the diagonal zero by bilinearity. It also contradicts the nonzero premise in the strict clause. No polarization premise is required for this zero-dimensional argument.

All results retain universe `u` throughout. This unit is an internal derivation from the published connected étale triviality theorem and the existing actual rationalization and Rosati constructions. It does not establish the positive-dimensional case of geometric Rosati positivity.

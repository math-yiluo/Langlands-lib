# Normal semigroup comparison through unipotent radical quotients

Worker 1372.

This is an internal reduction assembled from the Library's actual radical
quotients, quotient actions, normal reductive comparison and full-kernel
semigroup transport. It introduces no external structural assertion as a theorem.
All fields and schemes live at arbitrary universe `u`, and all subgroup
equalities concern morphisms from every scheme over the base.

`NormalSemigroupRadicalPrerequisites` is the conjunction of the independent
`NormalUnipotentRadicalIntersectionStatement`,
`NormalReductiveSemigroupPrerequisites` and
`Torus.SolvableFixedContainmentConnectedStatement`. Naming this bundle does
not prove any of its components.

`semigroup_comap_eq_of_normal_radical_quotients` works over an algebraically
closed field. It takes smooth connected affine groups `G` and `H`, a closed
normal embedding `i : H ⟶ G` equivariant for actual actions of a split torus,
supplied represented unipotent radicals `r : U ⟶ G` and `s : V ⟶ H`,
and explicit stability of both radical ranges under their actions. It also takes
actual fppf quotients `q : G ⟶ Q` and `p : H ⟶ R` by these full radical ranges,
with `Q` and `R` connected reductive. For an additive character semigroup
containing zero, the conclusion is
`(semigroupSubgroup b A).comap i = semigroupSubgroup c A`.

The implemented proof proceeds as follows.

1. Affineness of the sources implies quasi-compactness of the quotient
   projections, using their factorization of the source structure morphisms.
   The existing fppf quotient action construction supplies actions on `Q` and
   `R` from the stated radical stability.
2. The radical-intersection premise identifies the full kernels and supplies a
   closed normal homomorphism `j : R ⟶ Q` with `i ≫ q = p ≫ j`.
   Its equivariance is proved by lifting locally along the fpqc projection `p`,
   using the two canonical quotient action equations and the original
   equivariance. Equality then descends; no lift on each original test scheme
   is assumed.
3. Normal reductive comparison, with its structural prerequisites still
   explicit, supplies the semigroup equality along `j`.
4. The closed embedding of `V` in the affine group `H` makes `V` affine.
   Its radical predicate supplies smoothness, connectedness and unipotence.
   Existing unipotent solvability and uniform solvability bridges give
   `IsSolvableScheme V`. Restricting the original action to the represented
   stable radical supplies an actual action on `V` and equivariance of `s`.
   The represented smooth-kernel theorem makes `p` smooth.
5. The existing solvable-kernel semigroup transport theorem now lifts the
   quotient equality to `i`. The published `semigroupRealization` and
   `semigroupSmoothQuotient` proofs discharge those two inputs. The independent
   solvable connectedness proposition remains a premise through the bundle.

`semigroup_comap_eq_of_normal_stable_radicals` retains all the preceding
original-group, radical, stability, action and semigroup hypotheses. It uses
the actual `unipotentRadicalQuotient` proof twice to choose the fppf quotients.
Their pseudo-reductivity becomes connected reductivity using the explicitly
supplied `PerfectFieldPseudoReductiveStatement`, since the field is
algebraically closed and hence perfect. It then applies the supplied-quotient
consumer.

These are conditional normal-branch reductions. They do not prove radical
stability, choose radicals, prove the bundled structural propositions or
perfect-field comparison, descend comparison to general ground fields, or
prove the full `SemigroupComparisonStatement` with its three intersection
alternatives. Their provenance is the displayed derivation from existing
interfaces; no source theorem beyond the explicit structural premises is
silently used.

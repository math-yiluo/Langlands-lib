# Prescribed embedded finite coefficient vectors in the actual global tensor

This module connects finite Whittaker tensor separation to the prescribed
coefficient-model vectors on the **actual embedded local components** of a
cuspidal spectral presentation. Its provenance is the existing actual
local-component equivalences, coefficient-model surjectivity, finite
Whittaker separation and the Library's presentation tensor construction.

The entry proposition is
`Langlands.Global.RankinSelbergGlobal.FiniteWhittakerModel.PrescribedModelVectorAssemblyStatement`.
The theorem `finiteWhittakerModelAssembly` proves it by
`exists_prescribed_modelVectors`. Field universe `u` and supplied
presentation-carrier universe `uQ` remain independent and free. It includes
rank `r = 0` and the empty finite set `S`.

Fix an actual cuspidal realization `T` over a number field with compact additive
adelic quotient, a supplied spectral presentation `P` with irreducible
admissible actual finite components, and finite `S` containing the exceptional
set. Supply a unitary adelic additive character `ψ` trivial on the field and
its canonical nontrivial finite components `ψv` at `S`. At each `v ∈ S`, supply
a nonzero standard Whittaker functional `ℓ v` on the actual representation
`(P.localComponent v).representation`, and any prescribed vector `f v` of its
coefficient-image model. These are genuine functions on the local general
linear group, rather than abstract assigned coefficient values.

The local component and supplied factor carriers differ. `ComponentFunctionals`
uses the embedded component with the same canonical standard character as the
finite separation module `FiniteWhittakerTensor`. The genuine representation equivalence
`P.presentation.localComponentEquiv P.finiteSlice.nonzero v` maps
`P.localFactor v` onto that embedded component. Pulling the functional back
along this equivalence defines `factorFunctional`, now on the exact factor of
`P`'s restricted tensor. Nonzeroness of the functional is preserved by
surjectivity of the equivalence.

The conclusion chooses two finite tuples `a` and `a₀` in those supplied factors.
The second normalizes every pulled-back functional to one. The first exactly
realizes every prescribed model function:

`factorFunctional v ( (P.localFactor v).representation h (a v) ) = f v (h)`.

Write `X(a,t) = P.allPlaceTensorEquiv (P.finitePure S hPS a ⊗ₜ t)` for the
actual global carrier vector. This vector is spherical outside `S` for every
joint infinite tensor `t`. If every prescribed `f v` is nonzero and `t` is a
pure tensor of nonzero infinite source vectors, then `X(a,t)` is nonzero.

For every base point `g` with identity finite component at every place of `S`
and every finite adelic `d` integral outside `S`, the exact coefficient identity is

`W_(X(a,t))(g · ι_f(d))`
`  = (∏ v : S, f v (localProjection F (r+1) v d)) * W_(X(a₀,t))(g)`.

Here `W` is the existing `cuspWhittaker F T ψ.complex`, and `ι_f` uses the
existing actual adelic group-point equivalence and `AdelicGL.ofFinite`.
The normalized tuple `a₀`, prescribed tuple `a` and all local identities are
chosen independently of `g`, `d` and `t`. There is no additional scalar. The
remaining global coefficient still retains all infinite variables together.

The proof has the following implemented steps.

1. The generic `pullbackFunctional` composes an equivariant linear functional
   with the linear map of a genuine representation equivalence. The
   intertwining identity proves its same-character equivariance, and
   surjectivity proves `pullbackFunctional_ne_zero`. This construction permits
   an arbitrary subgroup and character, so it is also valid for an inverse
   character; the main entry proposition here uses the supplied standard one.
2. `exists_coefficient_vector` lifts a prescribed coefficient-model vector to
   its original representation using `Whittaker.modelMap_surjective`, and
   applies the inverse representation equivalence to that vector. The
   intertwining identity and exact coefficient-map definition prove equality
   of the resulting functions at every group element. This is an equality of
   functions, not proportionality.
3. `exists_factorVector` specializes this construction to the presentation's
   actual local-component equivalence. `factorVectorData` chooses such a
   factor vector together with its exact coefficient identity. If a chosen
   factor vector were zero, all values of its prescribed coefficient function
   would be zero. The two subtype extensionality arguments give equality to
   the zero model vector. Hence `factorVectorData_ne_zero` proves nonzero
   factors for nonzero prescribed model vectors.
4. Choose these factor vectors at every place of `S`. Independently normalize
   the nonzero pulled-back functionals by choosing a vector with nonzero
   value and scaling it by the inverse value. The previously proved
   `translated_coefficient_eq_product` applies to these exact factor
   functionals. Substituting the local coefficient identities into its finite
   product gives the displayed formula with the originally prescribed `f v`.
5. `allPlaceTensorEquiv_finitePure_sphericalOutside` supplies the precise
   existing spherical-outside-`S` predicate. If the local functions are
   nonzero, the chosen finite factor vectors are nonzero; `finitePure_ne_zero`
   and `allPlaceTensorEquiv_pure_ne_zero` then prove the asserted nonzero
   global pure-vector result.

The generic supporting `coefficient_vector_ne_zero` also proves the same
nonzero-vector observation within one coefficient model. No nonvanishing of
an integral or of the residual coefficient at a specified point is asserted.
Local Whittaker functionals and coefficient-model vectors remain supplied
inputs. Applying this to Rankin–Selberg test data uses those data's recorded
functionals and vectors; the statement does not itself choose that test data
or its Schwartz function.

`EqualFiniteWhittakerTests` applies the vector construction and
`normalizedVector` to the functionals and vectors of the finite
Rankin–Selberg test data.

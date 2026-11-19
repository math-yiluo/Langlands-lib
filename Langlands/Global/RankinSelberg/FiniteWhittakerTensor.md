# Finite-place separation of the actual cuspidal Whittaker coefficient

This internal unit proves the finite-place part of Whittaker factorization on
the exact supplied cuspidal tensor presentation. It uses the published
nonarchimedean local Whittaker multiplicity-one theorem, the actual global
Whittaker coefficient, and the Library's algebraic tensor constructions.

The entry proposition is
`Langlands.Global.RankinSelbergGlobal.FiniteWhittakerTensor.FiniteWhittakerSeparationStatement`;
`finiteWhittakerSeparation` proves it. Its field universe `u` and supplied
finite-carrier universe `uQ` are independent and free. Rank `r = 0` and the
empty finite set `S` are included.

Fix a number field `F` with compact additive adelic quotient, an actual cuspidal
operator realization `T`, and a supplied spectral presentation `P` whose actual
finite local components are irreducible and admissible. Let `S` contain
`P.exceptional`. Supply a unitary adelic additive character `ψ` trivial on `F`
and its canonical nontrivial finite components `ψv` at the places of `S`.
No additive conductor or support hypothesis outside `S` is needed for this
finite separation identity.

`FactorFunctionals P v (ψv v)` is the genuine standard Whittaker-functional
subspace on `(P.localFactor v).representation` for that canonical component.
It uses the exact supplied factor, rather than its actual embedded local-copy
carrier. Supply a nonzero functional `ℓ v` in this space at each `v ∈ S`.
The theorem chooses vectors `a₀ v` with `ℓ v (a₀ v) = 1`, independently of all
subsequent group points and vectors.

Write `X(a,t) = P.allPlaceTensorEquiv (P.finitePure S hPS a ⊗ₜ t)` for the
actual carrier vector, where `a v` are arbitrary vectors in the given finite
factors and `t` is an arbitrary vector of the tensor of the chosen actual
infinite source spaces. `finitePure` retains `P`'s reference vectors outside
`S`. For any adelic point `g` whose finite components at `S` are the identity,
and any finite adelic element `d` integral outside `S`, the theorem proves

`W_(X(a,t))(g · ι_f(d))`
`  = (∏ v : S, ℓ v ((P.localFactor v).representation d_v (a v)))`
`      * W_(X(a₀,t))(g)`.

Here `W` is exactly `cuspWhittaker F T ψ.complex`, `ι_f(d)` is the specified
point obtained by applying the inverse adelic point equivalence to
`AdelicGL.ofFinite d`, and `d_v = localProjection F (r+1) v d`. All finite
factors are actual coefficient functions of the prescribed local vectors.
The formula has constant exactly one because the residual vector uses the
normalization `ℓ v (a₀ v) = 1`. The residual coefficient can be zero; the theorem
does not assert its nonvanishing. The infinite variables remain together in
this actual residual global coefficient, with no product over infinite places.

The proof proceeds as follows.

1. `finitePureMultilinear` composes the finite tensor stage's universal
   multilinear map with its actual direct-limit embedding, the map tensoring
   with `t`, and `P.allPlaceTensorEquiv`. Its value is exactly `X(a,t)`.
   `finitePureMultilinear_update` shows that a group element supported at
   `v ∈ S` changes only the `v` coordinate and transforms the global image by
   the genuine finite action. This follows from the existing local-insertion
   pure-tensor formula and the proved finite covariance of the full equivalence.
2. `whittakerMultilinear` composes this vector-valued multilinear map with the
   published linear functional `x ↦ cuspWhittaker F T ψ x g`. The supporting
   slot-membership lemma takes a global local-equivariance certificate and
   proves that every one-slot linear form satisfies the same Whittaker identity
   on the given local factor.
3. For `g_v = 1`, the published `whittakerFunctional_mem` gives that global
   certificate. Its character is the canonical standard local character by
   `genericCharacter_localPoint`. Thus the slice is in the actual
   `FactorFunctionals` subspace. No local uniqueness conclusion is presumed
   in this step.
4. `factorFunctionals_eq_smul` applies the proved
   `Whittaker.localFieldMultiplicityOne` to the supplied factor. The published
   local-component equivalences transfer the original irreducibility and
   admissibility assumptions to this factor. `localGL_topology_eq` transports
   admissibility from the native completion topology to the canonical p-adic
   topology used by the character and local uniqueness theorem. The field
   topology, valuation and local-field instances are the canonical ones. This
   yields proportionality of every slice to the specified nonzero `ℓ v`.
5. `multilinear_eq_product` is an elementary finite-slot argument. A multilinear
   form whose `i`th slices lie on a normalized line `ℓ i` satisfies the one-slot
   identity `L(update b i x) = ℓ i x * L(update b i (a₀ i))`. Induction on the
   finite set of coordinates replaced from `a₀` by the input tuple gives
   `L a = (∏ i, ℓ i (a i)) * L a₀`. It includes the empty family. Applying this
   proves `coefficient_eq_product` at `g` without finite translation.
6. For `d` integral outside `S`, the published finite tensor action formula
   transforms `finitePure a` into the same-stage pure tensor with coordinates
   `(P.localFactor v).representation d_v (a v)`. Genuine finite covariance of
   `P.allPlaceTensorEquiv` and `cuspWhittaker_finiteRepresentation` move this
   action to right translation of the global argument. Substitution into the
   previous product yields `translated_coefficient_eq_product`.
7. A nonzero linear functional has a vector with nonzero value; scaling that
   vector by the inverse value normalizes it to one. Choosing these normalized
   vectors at all places of `S` gives the witness in the entry proposition.

The theorem retains nonzero local Whittaker functionals as supplied data. It
does not prove existence of these functionals for a chosen character, identify
their vectors with the local coefficient-model vectors of the Rankin–Selberg
test data, or claim nonvanishing of any integral. The original vector
nonvanishing and spherical-outside-`S` lemmas are in the presentation
tensor module. This identity also permits zero input vectors and zero residual
values.

The result is an internal consequence of the Library's
`CuspidalPresentationTensorDecomposition` and local uniqueness theorem.
`FiniteWhittakerSemilocalProduct` uses these coefficient identities with
prescribed local vectors on the partial adelic domain.

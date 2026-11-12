# Local isolation of actual unramified-twist coincidences

This is a derived supporting construction for the finite-stabilizer part of
Konno, *A note on the Langlands classification and irreducibility of induced
representations of p-adic groups* (2003), Claim 4.2.1, printed page 403. It does
not assert disjointness of Jacquet constituents or irreducibility of induction.

`rationalUnramifiedTwistIsoLocus G A B` is the set of actual full rational-norm
unramified characters whose published smooth twist of `A` is isomorphic to `B`.
The rational-point group has its canonical evaluation topology; its continuous
character group has Mathlib's compact-open topology, and the unramified
character subgroup has the subspace topology. The field and representation
universes are independent.

For a connected reductive group over a nonarchimedean local field and an
irreducible smooth complex object `A`, the locus is finite. There is no
admissibility hypothesis, and `B` is an arbitrary smooth object. If the locus
is nonempty, fix one of its characters `χ₀`. The injective translation
`χ ↦ χ₀⁻¹ * χ` maps it into the stabilizer of `A`. The proof cancels twists using
`rationalUnramifiedTwistMulIso`, `rationalUnramifiedTwistOneIso` and
`SmoothRep.twistIso`, and applies the published
`Langlands.CuspidalSupport.rationalTwistStabilizerFinite`.

The complement of the finite locus with the identity removed is an open
neighborhood of the identity. Within it, `χ ⊗ A ≅ B` is equivalent to `χ = 1`
and `A ≅ B`. Finiteness gives closedness because the character space is
Hausdorff. Pulling this neighborhood back by a map continuous at a base point
with value one gives `eventually_rationalUnramifiedTwistIso_separation`.
Applying that result to `g⁻¹ * f`, and canceling the twist by `g`, gives
`eventually_rationalUnramifiedTwistsIso_separation`: two twist families based
at the identity can be isomorphic nearby exactly when their characters agree
and their underlying objects are isomorphic.

These are internal consequences of the cited published stabilizer theorem
and elementary topology, rather than additional representation-theoretic
premises. They leave the Weyl-parameter, exponential-coordinate and
composition-factor parts of Konno's claim to their consumers.

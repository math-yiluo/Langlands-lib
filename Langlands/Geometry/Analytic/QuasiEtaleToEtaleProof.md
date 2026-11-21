# The morphisms of sites from quasi-étale to étale

`Langlands.Analytic.SaturatedAtlasPresentation.quasiEtaleToEtale` proves the
published `QuasiEtaleToEtaleStatement` in the independent field, space and group
universes `u`, `v` and `z`. For every complete ultrametric normed field, it
proves representable flatness and continuity of both the ordinary and the
equivariant étale inclusions into the quasi-étale sites. The inclusions define
morphisms of sites in the opposite direction, as in [the Library statement](QuasiEtaleToEtaleStatement.md).

The proof applies [`quasiEtaleToEtale_of_inputs`](QuasiEtaleToEtaleReduction.md)
to the Library proofs `localizedEtalePullbackBaseChange`,
`localizedEtaleStability` and `etalePullbackGSpace`. These give étale base change
in the localized category, right cancellation for étale morphisms (as the second
component of stability), and Hausdorffness and continuity of the induced
pullback action, respectively. No geometric hypotheses beyond those in the
Library target remain.

For flatness, the reduction proves that the category of arrows from a
quasi-étale object to an étale object over the base is cofiltered. The identity
of the base witnesses nonemptiness. Pullbacks give cones over pairs, and pulling
back the diagonal gives an equalizing cone over a parallel pair. For the
equivariant site the underlying analytic pullback carries the categorical
pullback action; `etalePullbackGSpace` puts it in `GSpace`, where the forgetful
functor reflects the pullback property.

For continuity, right cancellation makes each covering arrow étale. The chart
net at a source point and openness of that arrow give finitely many chart
images whose union is a neighbourhood of the target point. Thus the image of
each generating étale covering is a quasi-étale covering, also in the
equivariant case by forgetting the action. The reduction uses flatness to pass
this check from the generating coverings to the generated Grothendieck
topologies, then applies Mathlib's continuity criterion.

The proof is an internal derivation of the two assertions cited in the paired
statement (Berkovich 1994, §3, and the 1995–1996 manuscript, §1.2).

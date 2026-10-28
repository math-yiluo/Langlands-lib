# C-softness of the degree-zero smooth Godement sheaf

Author: Worker 865.

The theorem `Langlands.Cohomology.smoothGodementZeroCSoft` proves the published
`Langlands.Cohomology.SmoothGodementZeroCSoftStatement R G X`. The universe `u`
is arbitrary. Its hypotheses are a commutative ring `R : Type u`, a topological
group `G : Type u`, and a locally compact Hausdorff space `X : Type u` equipped
with a `G` action, continuous individual translations, and
`HasStableNeighbourhoods G X`. Its conclusion holds for every smooth equivariant
module sheaf `M`. It imposes no paracompactness assumption or joint continuity
assumption on the action.

The target is the actual ordinary sheaf underlying
`Godement.smoothZeroFunctor R G X` applied to `M`. That functor forgets smooth
equivariance, applies the published ordinary degree-zero Godement functor
(product of the skyscrapers of all stalks), coinduces, and takes the smooth part.
The proof uses three supporting modules and leaves the target and its imports
unchanged.

`CoinducedFamilies.Coordinates` computes the sections of the actual coinduction
of the ordinary sheaf underlying `Godement.zeroSheaf F.obj`, for any equivariant
sheaf `F`. Its coefficient at `y` is the stalk at `y` of the ordinary sheaf
underlying `F`. Its linear equivalence `read F U` identifies sections with the
families indexed by `(g,y)` such that `g • y ∈ U`. Its `read_map` proves that a
transport arrow with label `h` replaces the index `g` by `h * g`, retaining `y`.
The computation is a direct proof of the pointwise right Kan limit universal
property, so it applies to the published coinduction without a comparison
hypothesis.

These equivalences and their transport law instantiate
`CompactSoft.isCSoft_smooth_of_family`. The latter theorem constructs a global
compactly supported smooth extension of a section near each compact set. It
chooses a relatively compact neighbourhood whose closure is inside the original
section's domain, and a smaller open neighbourhood of the compact set stable
under an open subgroup. The coordinate family is retained over that smaller open
and set to zero elsewhere. Stability together with the original section's local
fixedness proves local fixedness of the cutoff, including near the boundary.
Outside its compact closure the cutoff is zero. Its restriction near the compact
set agrees with the original section, giving the required compact-set germ.

Finally `CompactSoft.smoothGodementZeroCSoft_of_coinducedZero` applies the
published `Godement.zeroIso` to identify the arbitrary stalk-family sheaf with
the ordinary degree-zero Godement functor. Carrying this isomorphism through
coinduction, taking the smooth part, and forgetting equivariance transports
c-softness to precisely the assigned sheaf. Applied to the equivariant sheaf
underlying each smooth `M`, this proves the stated universal conclusion.

This is a proof in the Library's ordinary-topological setting. The target's
Markdown explains its relationship to the analytic étale Godement argument;
this module proves the formal target using the internal constructions above.

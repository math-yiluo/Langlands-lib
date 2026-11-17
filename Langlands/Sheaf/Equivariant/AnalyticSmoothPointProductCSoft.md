# Ordinary c-softness of actual analytic smooth point products

The construction fixes a complete ultrametric normed field `K : Type u`, a
normed extension field `L : Type uL`, an actual analytic
`X : LocalizedCategory.{u, v, v}`, and supplied `EtaleSite.PointAxioms L x`
for every `L`-valued point of `X`. The group `G : Type z` is a topological
group acting by analytic automorphisms through `ρ : G →* Aut X`. Put
`W = max u (v + 1) uL`. The setup requires `Small.{W} G` and admissible
refinements for `distinguishedLiftSystem ρ` on `twistedEtaleTopology ρ`.
The coefficient ring is an arbitrary commutative `R : Type W`, and the
independent coefficient family assigns a `ModuleCat.{W} R` object to every
index in `ULift.{W}` of the actual `L`-valued points.

The sheaf in this module is the existing induction of the actual analytic
Godement point product with arbitrary independent coefficients, followed by the
existing locally discrete subsheaf construction and actual restriction to the
ordinary étale site.

The compact-extension and c-softness theorems additionally require that the
underlying analytic space is Hausdorff and that `IsContinuousAction ρ` holds
in the existing analytic sense. These two hypotheses are used for the
theorems; they are not needed to define the sheaf above.

`hasCompactExtensions_etaleRestrictedSmoothPointProduct` proves the ordinary
restriction has the compact-neighborhood extension property under these
additional hypotheses. It applies the
actual locally discrete compact cutoff theorem, views the resulting globally
locally discrete section as a section of the actual subsheaf, and uses the
proved global-section comparison with ordinary opens. Agreement and zero
restriction are checked through the injective subtype maps.

`isCSoft_universeLift_etaleRestrictedSmoothPointProduct` then proves the existing
native `CompactSoft.IsCSoft` predicate under the same Hausdorffness and analytic
continuity hypotheses, after canonical sheaf transport to the
lifted underlying space in the coefficient universe. Every original independent
universe and coefficient is retained.

This is an internal consequence of the stated constructions and their proved
cutoff and transport formulas. It asserts ordinary c-softness, not vanishing of
higher ordinary direct images or étale compact cohomology.

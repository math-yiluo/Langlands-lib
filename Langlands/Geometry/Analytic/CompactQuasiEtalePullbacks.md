# Compact pullbacks in the quasi-étale site

`CompactQuasiEtalePullbacksStatement` is an internal geometric prerequisite
isolated from the finite tuple-cone construction. It is a proposition
definition, not a proof or an additional hypothesis of the published tuple target.

Fix a complete ultrametric normed field `K : Type u`. For every analytic space
`X : LocalizedCategory.{u,v,v}` and every cospan `U → B ← V` in the actual
`QuasiEtaleSite X`, assume that the underlying analytic spaces of `B`, `U`, and
`V` are compact and Hausdorff. The statement asks for a pullback cone `t` in that
site with compact Hausdorff point. The square of its underlying analytic maps
must satisfy `IsPullback` in `LocalizedCategory.{u,v,v}`, with the universal
property against every localized analytic test object and every pair of maps
satisfying the square equation. The site cone already includes its structure
map to `X` and the proof that this map is quasi-étale.

No compactness or separation assumption is imposed on `X`. The cospan arrows
are arbitrary morphisms of the quasi-étale site, not only domain inclusions.
There is no action or coefficient hypothesis. The explicit localized universal
property supports inducing automorphisms on the pullback; its restriction also
gives the site's universal property.

Provenance: this is an internal decomposition of the published
`CompactCompatibleTupleConesStatement`, designed to separate analytic pullback
existence, compactness, and quasi-étale stability from continuous actions and
finite categorical induction. It is not attributed to a separately cited
literature statement. Its proof is `compactQuasiEtalePullbacks` in
`CompactQuasiEtalePullbacksProof`; no existing specialized pullback or compactness
construction is asserted here to discharge this full proposition.

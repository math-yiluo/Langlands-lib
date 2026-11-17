# Local points of actual torsors at almost all finite places

This internal helper is derived from the published fpqc descent results and
the actual torsor shear map. It will support the torsor clause of Conrad's
Exercise 5.5.3(iii).

For `separated_of_isIso_leftSMul`, the shear isomorphism identifies the
self-base-change of the torsor's structure map with the base change of the
group's structure map. Separatedness is invariant under isomorphism, is stable
under base change, and descends along the flat, surjective, quasi-compact
structure map.

The proof of `geometricallyConnected_of_isIso_leftSMul` uses the same
identification and the published descent of geometric connectedness along a
surjective change of base. No flatness or quasi-compactness is needed for this
second conclusion.

`eventually_nonempty_ringPoint_of_torsor` proves exactly the torsor clause of
`Langlands.GroupScheme.AlmostAllPlacesQuasiSplitStatement`, for every universe,
every number field, and every connected reductive group over it. The torsor
is an actual scheme with a `ModObj` action, a flat, surjective,
quasi-compact structure map, and invertible shear; no torsor-spreading
assumption is added.

The connected smooth affine group is geometrically connected by the published
group-scheme theorem `geometricallyConnected_of_connected`. Its torsor is smooth
by `IntegralTorsorPoint.smooth_of_isIso_leftSMul`, separated by the first lemma
here, and geometrically connected by the second. The general smooth,
separated, quasi-compact, geometrically connected scheme theorem
`Langlands.Global.eventually_nonempty_ringPoint_of_smooth_geometricallyConnected`
then supplies points over almost all finite completions.

The construction `torsorCompletionPoints` returns a finite exceptional set and
an actual relative scheme point over each remaining finite completion. It
chooses the finite set of places where the point type is empty, and uses
classical choice at every other place. Its purpose is to expose actual points
as data for later constructions. This is derived internal content, not a
separate source definition. It is a direct consequence of the preceding
theorem, whose conclusion is the second assertion of Conrad, *Reductive group
schemes* (2014), Exercise 5.5.3(iii), printed pp.182–183. The implemented route
uses uniform Lang–Weil and scheme spreading rather than spreading the action.

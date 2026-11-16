# Fppf-local concrete pinning preservation

This internal module defines `IsFppfLocallyPinned` to mean that an actual
comparison becomes `IsLocallyPinned` on one flat surjective cover locally of
finite presentation. It retains the concrete dual-number pinning equations on
the cover and permits their root relabellings to vary with local affine tests.

The actual pullback tower law proves that concrete pinning preservation is
insensitive to reassociation of successive pullback maps, with the endpoint
identifications included. Pulling the cover back gives arbitrary pullback
stability. Composing covers proves reflection from one fppf cover. Taking the
fibre product of two covers proves closure under composition. Identity
comparisons are locally pinned.

The torus and cocharacter clauses descend by their previously proved fppf
reflection, so this localized predicate still implies both exact global
geometric clauses. None of these results asserts geometric existence of a
pinned representative, uniqueness in an inner-equivalence class, or
independence of prospective local representatives.

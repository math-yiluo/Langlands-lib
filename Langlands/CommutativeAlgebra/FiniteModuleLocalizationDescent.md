# Descent of a finite module over a localization

The internal auxiliary theorem `exists_fg_submodule_isLocalizedModule` states
that a finite module `N` over `Localization S` is the localization of a finitely
generated `R`-submodule `K` of `N`. The ring is commutative, and `N` carries the
compatible restricted scalar action of `R`. The ring and module may belong to
different universes. The theorem requires neither localness nor Noetherianity.

This is an internal algebraic derivation from Mathlib's finite generation and
localization interfaces, prepared to accompany the finite projective dimension
localization bridge. It does not assert a finite projective dimension bound.

The proof chooses a finite generating set of `N` over `Localization S`, and
lets `K` be its span over `R`. This span is finitely generated. Mathlib's
`multiple_mem_span_of_mem_localization_span` clears denominators to show that
every element of `N` has an `S`-multiple in `K`. Scalars in `S` act invertibly on
`N`, as expressed by `isLocalizedModule_id`. Finally the inclusion of `K` is
injective, so equality in `N` already implies equality in `K`. These three facts
are precisely the fields of `IsLocalizedModule S K.subtype`.

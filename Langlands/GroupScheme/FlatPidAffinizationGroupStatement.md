# Canonical affinization of flat groups over principal ideal domains

Worker 596.

`canonicalAffinization X` is the actual scheme `Spec Γ(X, O_X)`, with structural
map obtained by taking the spectrum of the ring map on global sections induced
by `X → Spec R`. `toCanonicalAffinization X` is the canonical map of schemes,
regarded as a morphism over `Spec R`. Its structural compatibility follows from
the naturality of `Scheme.toSpecΓ` and the canonical identification
`Γ(Spec R, O) ≅ R`.

`Langlands.GroupScheme.FlatPidAffinizationGroupStatement.{u}` is a proposition
definition. For every principal ideal domain `R` and every actual flat,
quasi-compact, separated group scheme `G` over `Spec R`, it asserts that the
prescribed object `canonicalAffinization G.X` admits an actual group object
structure for which the prescribed map `toCanonicalAffinization G.X` is a
monoid homomorphism. For group objects this also preserves inversion. Neither
the group nor its global function ring is assumed to be of finite type. The
statement includes both fields and discrete valuation rings. It makes no
claim of smoothness or finite type for the affinization, and contains no
base-change assertion or proof of the group-law existence assertion.

## Provenance

This is an internal prerequisite isolating the canonical group construction
used in the smooth part of Prasad–Yu, *On quasi-reductive group schemes*,
Proposition 3.1, author-preprint p.5. The original proof sets
`A = Γ(G, O_G)` and uses `Spec A` as an affine group, before finite generation
of `A` has been established. The present proposition defines that missing
obligation at a reusable scope. The principal-ideal-domain generality is an
internal extension of the DVR instance needed there: torsion-free modules are
flat, and flat base change of global sections supplies the expected comparison
on products of flat schemes. That route remains a proof obligation.

Registered source: `prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`,
Proposition 3.1, author-preprint p.5. The only implemented proof in this module
is the structural compatibility of the canonical map, from the existing
Mathlib naturality identities.

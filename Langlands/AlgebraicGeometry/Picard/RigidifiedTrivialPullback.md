# Pullback of the canonically rigidified trivial bundle

For any commuting square of schemes with maps `f : X' ⟶ X`,
`g : S' ⟶ S`, `ε : S ⟶ X`, and `ε' : S' ⟶ X'` satisfying
`ε' ≫ f = g ≫ ε`, `RigidifiedLineBundle.pullbackTrivialIso`
constructs an actual isomorphism from the pullback of `trivial ε`
to `trivial ε'`. The underlying module-sheaf comparison is the
canonical `Langlands.Scheme.Modules.pullbackUnitIso f`. Its
compatibility with the canonical rigidifications is proved, rather
than assumed or replaced by an arbitrary isomorphism of carriers.

The helper `RigidifiedModule.pullbackUnitIso_inv_compHom` extends
the existing inverse unit-comparison composition law to a specified
composite, by substitution of the equality of scheme maps.
`pullbackTrivial_compatibility` then cancels the target unit
comparison. The proved unit-composition law rewrites the remaining
pullback of that comparison. The existing formula
`pullback_rigidification_hom_comp` expands the pulled-back
rigidification, the helper identifies its first three factors with
the inverse comparison for the composite, and inverse followed by
forward comparison is the identity. Finally `isoMk` packages this
proved compatibility together with `pullbackUnitIso f`.

This is derived infrastructure for the actual rigidified pullback
of Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, paragraph (6.2), printed p.88 (PDF p.92),
registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The source specifies a rigidification as an isomorphism from the
structure sheaf and requires bundle morphisms to preserve it.
The present comparison follows from the existing actual pullback
and its proved unit coherence; it needs neither representability
nor the additional hypotheses used in that source to compare the
rigidified functor with a sheafified Picard functor. It uses the
published `RigidifiedPullbackProofs` and `PullbackUnitProofs`, with
no unproved coherence premise. No tensor group law is asserted.

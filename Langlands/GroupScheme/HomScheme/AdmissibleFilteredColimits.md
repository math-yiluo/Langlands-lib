# Filtered colimits of actual closed torus subgroups

Author: Worker 668.

For a quasi-compact, separated, locally finitely presented group over a
locally noetherian scheme, the small presheaf of actual closed torus
subgroups satisfies Murre's filtered-colimit condition. It sends
filtered colimits of algebras over each affine open to colimits of
sets. The stage maps may be arbitrary algebra homomorphisms.

A subgroup over the colimit algebra has a closed torus model over a
finitely generated coefficient algebra. That algebra is finitely
presented over the noetherian ground ring, so its map to the colimit
factors through a stage. The composition law for family evaluation
recovers the original subgroup on every test scheme.

For two subgroups agreeing at the limit, take the filtered tail of
arrows out of their common stage. Each containment is detected by
invertibility of a projection from the scheme-theoretic intersection
to one torus. The projection is a closed immersion between affine
schemes locally of finite presentation over the stage. Invertibility
descends along the affine limit and persists after further pullback.
Both containments therefore hold at a common stage.

Raynaud proves commutation with limits for subtori in SGA 3,
Exposé XV, Corollary 6.3, and applies it as condition 8.10(ii).
The Lean condition restricts to affine opens of a locally noetherian
base and uses literal ranges of actual closed torus inclusions.
[Gille–Polo recomposition, PDF pp. 42 and 62](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo15.pdf)

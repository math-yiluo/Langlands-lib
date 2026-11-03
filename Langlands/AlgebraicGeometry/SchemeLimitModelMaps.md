# Actual morphisms between models at levels and at a limit

This is an internal construction for the morphism and prescribed-isomorphism
parts of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(1),(3).
It constructs the actual maps to which descent assertions will apply.
It does not assert morphism factorization, eventual equality, or
isomorphism descent.

Let `D : I ⥤ Scheme` be a diagram, `S` a scheme, and `t` a compatible
family `Dᵢ → S`. Let `a : X → S` and `b : Y → S` be arbitrary scheme
morphisms. All categories and schemes share an arbitrary universe `u`.
No affineness, finite presentation, separation, filteredness, or
topological ring assumption occurs in these constructions.

The file reuses
`EtaleEquivalenceRelation.Action.TargetLimit.diagram` and its cone,
which construct the actual pullbacks `Dᵢ ×ₛ X` and `T ×ₛ X`.
The existing `AffineLimit` projection equations used here are general
pullback identities; their names impose no affine hypotheses.

`LevelHom D t a b i` is the subtype of actual scheme morphisms
`Dᵢ ×ₛ X → Dᵢ ×ₛ Y` commuting with the projections to `Dᵢ`.
`LimitHom a b p`, for a supplied map `p : T → S`, is the same subtype
of actual morphisms `T ×ₛ X → T ×ₛ Y` over `T`.
No equivalence class or abstract assumed morphism space is substituted
for these carriers.

For `r : i → j`, `restrict r` base changes a morphism at level `j`
to level `i`. Its first projection is the projection to `Dᵢ`; its
second projection is the transition to `Dⱼ ×ₛ X`, the given morphism,
and the projection to `Y`. `restrict_square` identifies its actual
transition square. `restrict_id` and `restrict_comp` give the identity
and composition laws.

For a supplied cone `c`, map `p : c.pt → S`, and equations
`c.πᵢ ≫ tᵢ = p`, `toLimit i` constructs the actual morphism over `c.pt`
induced by a morphism at level `i`. A limit witness is not needed to
form this map. `toLimit_square` states its commuting square with the
two base-changed cone legs. `toLimit_restrict` proves compatibility
with every transition. The `_fst` and `_snd` lemmas state the
respective projection formulas. All these laws follow directly from
the pullback universal property and cone or diagram naturality.

The provenance is internal: the subtypes make explicit the relative
Hom sets in Conrad's Theorem 3.4(1), and the maps implement its stated
base changes using existing Library constructions. A separate statement
and proof must establish factorization and eventual equality under
their individual finiteness assumptions, and descent of a prescribed
isomorphism under finite presentation of both models. Initial model
existence, property descent, arithmetic realization, topology, and
whole-paper coverage remain separate obligations.

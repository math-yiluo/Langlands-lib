# Cross-cover maps of associated coefficient reduction systems

Author: Worker 13.

Let `R : Type u` be a commutative ring, `I : Ideal R`, and `X : Scheme.{u}`.
Let `G` and `H` be groups in universe `u`, `Y : Action X.Etale G`, and
`Z : Action X.Etale H`. All module carriers also lie in `u`. Fix a group
homomorphism `φ : H →* G`, an equivariant cover-object map
`a : Z ⟶ (Action.res X.Etale φ).obj Y`, coefficient actions
`M : Action (ModuleCat R) G` and `N : Action (ModuleCat R) H`, and an
equivariant coefficient map `c : res(φ) M ⟶ N`. The sheaves below use
`X.smallEtaleTopology`.

This is an internal construction from `CrossCover`, `EtaleCrossCover` and
`Reduction`. It uses their actual invariant sheaves, quotient coefficient
modules, transition maps and canonical reduction comparisons. It is a
functoriality construction for these objects, with no new transcription of a
result in Harris. In particular, no geometric covering or torsor property of
`Y`, `Z` or `a` is required.

Write `A_Y` and `A_Z` for the existing constant associated functors and
`k(c) : A_Y(M) ⟶ A_Z(N)` for `etaleCrossCoverMap X φ a c`.
`etaleCrossCoverMap_sameCover` identifies this map with the existing
associated coefficient map when the group and cover are fixed.

`crossCoverMap_coefficient_square` proves the corresponding square for arbitrary
sheaf coefficient actions on the small etale site. Given coefficient maps
`d : F ⟶ F'`, `e : E ⟶ E'`, `c : res(φ) F ⟶ E`, and
`c' : res(φ) F' ⟶ E'` with `res(φ).map d ≫ c' = c ≫ e`, it proves
that the associated image of `d` followed by the cross-cover image of `c'`
equals the cross-cover image of `c` followed by the associated image of `e`.
The proof composes with the inclusion into the target product sheaf, uses
naturality of the inclusion and of cover pullback, and then applies the
product-sheaf functor to the given coefficient equation.
`etaleCrossCoverMap_coefficient_square` specializes this to constant module
coefficients; faithfulness of forgetting equivariance reduces its coefficient
equation to functoriality of the constant sheaf functor.

Let `P_n` denote the actual module quotient by `I^n`, retaining its
`R`-module structure and full group action. `modulePowerReductionCrossMap I φ n c`
is `P_n.map c` on `H`-actions. Restricting the group action commutes
definitionally with applying this quotient functor, so the source is also
`res(φ) (P_n M)`. The two lemmas with suffixes `_unit` and `_transition`
prove that these maps commute with the actual equivariant quotient units
`u_n` and every power transition `t_nm`. Both proofs apply naturality of the
module transformations constructed in `Reduction` to `c` on `H`-actions.

`etaleCrossCoverModuleReductionSystemsMap I X φ a c` constructs a morphism
of ordinary inverse systems

`(n ↦ A_Y(P_n M)) ⟶ (n ↦ A_Z(P_n N))`.

Its component at `n : ℕᵒᵖ` is `k(P_(n.unop).map c)`. Its inverse-index
naturality is the preceding coefficient-square lemma applied to the actual
module transition equation. The systems are exactly those of
`constantAssociatedModuleReductionFunctor`, including exponent zero.
The `_id` theorem proves that identity cover and coefficient maps give the
identity system map, using preservation of identities by power reduction and
`etaleCrossCoverMap_id`. The `_comp` theorem retains the cross-cover composition
law: for a further group homomorphism `ψ : K →* H`, map
`b : W ⟶ res(ψ) Z` and coefficient map `d : res(ψ) N ⟶ P`, the
composite is the map for `φ.comp ψ`, `b ≫ res(ψ).map a` and
`res(ψ).map c ≫ d`. Its proof evaluates at each index, uses
`etaleCrossCoverMap_comp`, and forgets equivariance to apply preservation of
composition by the actual module quotient functor.

Let `Q_n` be sheaf power reduction and let
`C_n(Y,M) : Q_n(A_Y M) ⟶ A_Y(P_n M)` be the comparison in `Reduction`.
`constantAssociatedPowerReductionComparison_crossCover` proves

`Q_n.map (k(c)) ≫ C_n(Z,N) = C_n(Y,M) ≫ k(P_n.map c)`.

The proof precomposes with the actual sheaf quotient epimorphism
`q_n(A_Y M)` and cancels it using the published
`Langlands.Sheaf.AdicSystem.quotientMap_app_epi` instance. Naturality of `q_n`
and `constantAssociatedPowerReductionComparison_unit` turn the two composites
into `k(c) ≫ A_Z.map u_n` and `A_Y.map u_n ≫ k(P_n.map c)`.
The coefficient-square lemma and `modulePowerReductionCrossMap_unit` identify
these maps. The compatibility square is proved, rather than supplied as a
premise; no sectionwise-surjectivity assumption is introduced.

`constantAssociatedReductionSystemsComparison_crossCover` evaluates that
square at every index to prove the equality of inverse-system morphisms:
applying the sheaf reduction-system functor to `k(c)` and then the system
comparison for `Z,N` equals the comparison for `Y,M` followed by the
constructed cross-cover system map.

These constructions use no group topology, finiteness, flatness, covering,
torsor or completeness assumption. They supply ordinary sheaves and inverse
systems and their functorial maps. They do not prove invertibility, local
triviality, smoothness, a derived-limit or cohomology comparison, or identify
these systems with the particular geometric coefficient systems of Harris.
Reversing the cover-comparison legs in `VaryingCover` still requires its
separate torsor comparison obligation.

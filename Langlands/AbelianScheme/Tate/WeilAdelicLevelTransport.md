# Path transport and level maps for actual Weil-compatible adelic frames

This module constructs path transport on the actual full adelic
Weil-compatible frames and their geometrically fixed right orbits. It proves
independence from the supplied path, and constructs forgetting level and right
Hecke translation, with their identity, composition and transport laws.
Every construction remains explicitly conditional on
`Langlands.AbelianScheme.RationalWeilGeometricTransportStatement`.

The source model is Harris–Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed p.91 (PDF p.99): invariant level
orbits, canonical independence from the geometric point, forgetting level,
and the maps induced by right composition with `g`. Kottwitz, *Points on some
Shimura varieties over finite fields* (1992), Section 5, printed pp.390–391
(PDF pp.18–19), explains the actual Tate-twist value line, commuting left
monodromy and right similitudes, and why fixing an orbit removes the choice
of geometric point. These are registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura` and
`kottwitz-1992-points-shimura-finite-fields`. Harris–Taylor p.18 supplies the
rationalization convention already implemented by the imported Tate module.
The present conditional arbitrary-path construction is derived from the
published Library objects; it does not prove the geometric existence results
used in those sources.

## Inputs and scope

Fix an actual abelian scheme `A/S` over a quasi-separated scheme, with the
published dual-scheme geometry, Poincaré evaluation, pullback-tensor coherence,
Picard pullback and finite Weil transition inputs. The map `polarizationMap`
is an actual homomorphism from `A` to its constructed dual. As in `WeilFrame`,
no polarization predicate is required for this more general interface. Fix
a rational algebra `D`, a rational `D`-module `V`, a rational bilinear form
`ψ`, and `i : D →ₐ[ℚ] Rationalization.End A`. Let `G` denote
`ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ`.

The two endpoints are field-valued points `s : Spec Ω → S` and
`t : Spec Ω' → S`; geometric points are the intended application. Retain
finite fibres for the actual finite étale cover fibre functors, the
`TorsionFiniteEtaleStatement`, invertibility on `S` of every positive
integer, and finite étaleness of all root-of-unity schemes. The full
rational/profinite-integer adele comparison `h` is explicit. The module
uses the same actual full Tate and section-ring twist modules, forms, source
actions and monodromy actions as `WeilFrameMonodromy`.

A path means an isomorphism `p` between these actual finite étale fibre
functors. This module does not assert that a path exists. It needs neither
connectedness nor local noetherianity once the displayed path and hypotheses
are supplied. It does not supply finite-dimensionality, faithfulness,
involution compatibility, alternation, nondegeneracy, compact openness, or
nonemptiness of frame spaces. Those remain separate PEL specialization
hypotheses and obligations. The construction applies to any subgroup `U` of
`G`, in particular to a compact open subgroup once that structure is supplied.

## Frame transport

`weilAdelicFrameTransport p` is an equivalence from the existing
`WeilAdelicFrame` at `s` to the one at `t`. Its underlying map is

`η ↦ τ_A ∘ η`,

where `τ_A` is the actual tensor-algebra-linear
`finiteAdeleAlgebraTransport`. Its value equivalence is the actual
`TateTwist.Geometry.sectionFiniteAdeleTransport`, denoted `τ_1`. The second
clause of the explicit geometric compatibility proposition gives

`e_t(τ_A x, τ_A y) = τ_1(e_s(x,y))`.

Applying `PEL.FormIso.transport` with these two equivalences therefore
preserves the actual Weil-form condition. An existential twist trivialization
is composed with `τ_1` inside the proof of compatibility. No roots or basis
are chosen, and no trivialization is retained as frame data.

The application lemma identifies the underlying map with the constructed
`rationalTransport p`. The `refl`, `trans` and `symm` lemmas give transport
along the identity, concatenation `p ≪≫ q`, and reverse path. Their proofs
use subtype and linear-equivalence extensionality, then the corresponding
actual Tate-transport laws (or their defining inverse maps).

`weilAdelicFrameTransport_right` proves that this map commutes with right
source composition: transport of `η ∘ g` equals `(τ_A ∘ η) ∘ g`.
`weilAdelicFrameTransport_monodromy` intertwines the actual left monodromy
by the constructed group isomorphism `pathConjugation p`. The proof reduces
pointwise to `rationalTransport_monodromy`.

## Fixed orbits and path independence

`weilAdelicLevelTransport U p` applies `InvariantOrbit.equiv` to the frame
equivalence, path conjugation and the two equivariance laws. It is an
equivalence between `WeilAdelicLevel U` at the two endpoints. These levels
are right `U`-orbit classes fixed by the whole geometric fundamental group;
a representative need not be fixed.

`weilAdelicLevelTransport_path_independent` states that, for any two paths
`p,q` with these endpoints, their level equivalences are equal. The actual
law `rationalTransport_change_path` says that the two frame maps differ by
the target monodromy loop `p.symm ≪≫ q`. The generic
`InvariantOrbit.equiv_eq_of_left` then identifies their maps on fixed orbit
classes. This is a proof of independence from the supplied path; a
canonical equivalence for every pair of geometric points additionally needs
a path-existence theorem under the relevant base hypotheses.

The level `refl`, `trans` and `symm` lemmas establish the corresponding
identity, concatenation and inverse laws. The proofs reduce equality of
fixed-orbit elements to equality of their quotient classes, use quotient
induction, and apply the respective frame-transport law.

## Level changes and Hecke translation

For subgroups `U,U'` and `g : G`, `weilAdelicLevelTranslate g hg` sends
`[η]` to `[η ∘ g]`, provided

`∀ u ∈ U, g⁻¹ * u * g ∈ U'`.

Thus `U` is the source subgroup and `U'` the target subgroup. This is the
condition `g⁻¹ U g ≤ U'` from the right-action convention of Harris–Taylor
p.91, with its source and target levels named explicitly. The definition
specializes the existing `InvariantOrbit.translate` using the actual
commuting actions, so it is well defined on orbit classes and preserves
monodromy invariance.

`weilAdelicLevelForget hU`, for `hU : U ≤ U'`, specializes this translation
to `g = 1`. `weilAdelicLevelTranslate_one` and
`weilAdelicLevelForget_refl` give the identity maps. Successive translations
by `g` and then `k` equal translation by `g*k`; the proof specializes
`InvariantOrbit.translate_comp`, whose conjugation condition composes in
that order. `weilAdelicLevelForget_comp` specializes the same result to two
identity elements, proving transitivity of forgetting level.

Finally, `weilAdelicLevelTransport_translate` proves that the path
equivalence commutes with every displayed right translation by applying
`InvariantOrbit.map_translate` to the actual frame transport.
`weilAdelicLevelTransport_forget` is its identity-element specialization.
These are maps of the actual restricted level sets. Transport between
different abelian schemes by rational isogenies or scheme base change, the
prime-to-modulus variant, and the unpointed PEL moduli functor are not
constructed in this module.

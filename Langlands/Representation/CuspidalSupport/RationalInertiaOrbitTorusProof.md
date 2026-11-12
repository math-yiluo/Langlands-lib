# Unramified orbits of irreducible representations are tori: proof

Module `Langlands.Representation.CuspidalSupport.RationalInertiaOrbitTorusProof`.
Namespace `Langlands.CuspidalSupport`.

Worker 5102. The theorem `rationalInertiaOrbitTorus` proves the exact published
proposition `Langlands.CuspidalSupport.RationalInertiaOrbitTorusStatement`,
with the universes `uF` and `uV` of the statement. The statement's Lean and
Markdown files and everything they import are unchanged, and no hypothesis is
added.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
V.2.7, Corollary and the following Notations paragraph, printed p.109 / PDF
p.115. The implemented proof follows the route sketched in the statement's
Markdown. The algebra is in the supporting module
`RationalInertiaOrbitTorusAlgebra` (namespace `OrbitTorus`); its Markdown
explains each step.

## Auxiliary declarations in this module

These use the canonical rational-point topology `rationalPointTopology F G.X`,
as the statement does.

- `rationalTwistStabilizer G A`: the stabilizer
  `{s | rationalUnramifiedTwist G s A ≅ A}` as a subgroup of the unramified
  characters. Its carrier is, by definition, the set `S` of the statement.
  - It contains `1` by `rationalUnramifiedTwistOneIso`.
  - It is closed under products: compose `rationalUnramifiedTwistMulIso`
    with the twist of a stabilizing isomorphism (`SmoothRep.twistIso`).
  - It is closed under inverses: twist a stabilizing isomorphism for `s` by
    `s⁻¹`, then use `rationalUnramifiedTwistMulIso`, `s⁻¹ s = 1` (through
    `eqToIso`) and `rationalUnramifiedTwistOneIso`.
- `nonempty_rationalUnramifiedTwist_iso_iff`: `A ⊗ χ ≅ A ⊗ χ'` if and only if
  `χ⁻¹ χ' ∈ rationalTwistStabilizer G A`.
  - From `A ⊗ χ ≅ A ⊗ χ'`, twisting by `χ⁻¹` gives
    `A ⊗ χ⁻¹χ' ≅ A ⊗ χ⁻¹χ ≅ A`.
  - From `A ⊗ χ⁻¹χ' ≅ A`, twisting by `χ` gives
    `A ⊗ χ' ≅ A ⊗ χ(χ⁻¹χ') ≅ A ⊗ χ`.

  Both directions use only `SmoothRep.twistIso`,
  `rationalUnramifiedTwistMulIso`, `rationalUnramifiedTwistOneIso` and
  `eqToIso` for the group identities.
- `rationalUnramifiedDescendHom G`: the published descent
  `rationalImageUnramifiedDescend G`, packaged as a group homomorphism from
  the unramified characters to `Λ(G) →* ℂˣ`. Multiplicativity is checked on
  points `rationalValuationImageProjection G g`, using the published
  `rationalImageUnramifiedDescend_projection` and the surjectivity of the
  projection. `rationalUnramifiedDescendHom_projection` restates that lemma
  for the packaged map.
- `rationalUnramifiedDescendHom_bijective`:
  - Injectivity: two characters with the same descent agree at every
    `g ∈ G(F)`.
  - Surjectivity: a character `f` of the discrete group `Λ(G)` is the
    descent of the published `rationalImageUnramifiedPullback` of `f`. That
    pullback uses the published continuity
    `continuous_rationalValuationImageProjection G`.
- `rationalUnramifiedCoordinateEvaluation_single_apply`: the published
  evaluation `rationalUnramifiedCoordinateEvaluation G hp` sends
  `single a c` to `χ ↦ c · (descent of χ)(a)`, by the published
  `rationalImageCoordinateEvaluation_single`.

## The proof of `rationalInertiaOrbitTorus`

1. After introducing `F`, `G` and `hG`, the proof recreates the instances
   fixed by the statement:
   - the affine structure map from `hG.isAffineHom`;
   - affineness of `G.X.left`;
   - smoothness `hG.smooth`;
   - the canonical topology `rationalPointTopology F G.X`;
   - the published topological-group instance
     `rationalPoint_isTopologicalGroup F G`, as in the published finiteness
     proof.

   It then introduces `A`, its irreducibility, and the statement's `S` and
   `invariant`.
2. **Finiteness of `S`.** The published proof `rationalTwistStabilizerFinite`
   of V.2.7, Lemma, applied to `A`, shows that `S` is finite. So the subgroup
   `rationalTwistStabilizer G A` is a finite group.
3. **The algebra.** `OrbitTorus.exists_invariant_laurent` is applied with:
   - `Λ = rationalDiscreteValuationImage G` and its published basis
     `rationalReductiveValuationBasis G hG`, indexed by
     `Fin (rationalImageRank G)`;
   - `X` the unramified characters and `D = rationalUnramifiedDescendHom G`
     (bijective);
   - `E = rationalUnramifiedCoordinateEvaluation G hp` (monomial formula
     above, and the published
     `rationalUnramifiedCoordinateEvaluation_injective`);
   - the finite subgroup `rationalTwistStabilizer G A`.

   This gives `Φ` with clauses 2 and 3 of the statement and the orbit
   criterion `χ⁻¹ χ' ∈ S ↔ (all elements of F^S agree at χ, χ')`. These hold
   for the set `{f ∈ range E | f(χ s) = f(χ) for s ∈ S}`.
4. **Identifying `F^S`.** The published
   `rationalUnramifiedCoordinateEvaluation_range` says that the range of `E`
   is `unramifiedRegularFunctions`. With it, that set is definitionally the
   statement's `invariant`.
5. **Clauses 1 and 4.**
   - Clause 1 is `nonempty_rationalUnramifiedTwist_iso_iff`.
   - Clause 4 is clause 1 composed with the orbit criterion from step 3.

The proof depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

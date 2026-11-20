# Proof of base change of the projective frame locus

This module proves the published statement
`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusBaseChangeStatement`
by the theorem `frameLocusBaseChange`.

Statement: let `S` be locally noetherian, `T` any scheme, `0 < d`,
`a : Datum P S g d n`, `f : T ⟶ S` and
`ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2*g) → ZMod n`. Then
`(a.pullback f).frameLocus ρ = f ⁻¹ᵁ a.frameLocus ρ`.

Notation: `π = a.abelian.X.hom`, `V = a.rigidificationModule = π_* L³`,
`σ = a.torsionPoint r`. For the pulled-back datum, `π'`, `V'`, `σ'` and
`L'³` are the corresponding objects and `q = pullback.fst π f`. The published
canonical comparison is `B = a.rigidificationBaseChangeMap f : f^* V ⟶ V'`.

## Steps of the proof

1. **Torsion points.** `Datum.torsionPoint_pullback_fst`:
   `σ' ≫ q = f ≫ σ`. This is the underlying-morphism form of the published
   `enumerateTuple_pullback`.
2. **Coherence.** `section_baseChange_coherence` is a general identity for a
   section `σ` of `π`, a commutative square `q ≫ π = π' ≫ f` and a section `σ'`
   of `π'` with `σ' ≫ q = f ≫ σ`. Two canonical isomorphisms
   `f^* V ≅ σ'^* q^* π^* V` agree:
   - the identification `f^*V ≅ σ'^*π'^*f^*V`, followed by the inverse square
     comparison `pullbackSquareIso`;
   - the pullback of `V ≅ σ^*π^*V`, followed by the comparison
     `f^*σ^* ≅ σ'^*q^*`.

   Both sides are written with the published generalized composition
   comparisons `compIso`. The proof composes with an isomorphism to
   `f^* V` and reduces each side to the identity. It uses the published
   `compIso_assoc` three times, `compIso_id_left_congr` and
   `pullbackComp_inv_app_comp_pullbackId`, through the helper lemmas
   `pullbackSquareIso_inv_app_eq` and
   `pullback_map_pullbackId_inv_comp_compIso`.
3. **Torsion evaluations.** `Datum.torsionEvaluation_eq` rewrites the published
   `Datum.torsionEvaluation` with `compIso`.
   `Datum.rigidificationBaseChangeMap_comp_torsionEvaluation` shows

   `B ≫ (a.pullback f).torsionEvaluation r = f^*(a.torsionEvaluation r) ≫ c_r`.

   Here `c_r = Datum.torsionEvaluationBaseChangeIso f r` is the comparison of
   `f^* σ^* L³` with `σ'^* L'³`. It is built from `compIso` and the published
   `Datum.cubicBundlePullbackIso`. The proof uses:
   - naturality of the identity and composition comparisons;
   - the published counit identity `Datum.cubicEvaluationAdjoint_baseChange`;
   - step 2.
4. **Frame evaluations.** `Datum.rigidificationBaseChangeMap_comp_frameEvaluation`
   gives the same square for `a.frameEvaluation ρ k`. The target comparison
   `Datum.frameEvaluationBaseChangeIso` is the product of the `c_r`, after the
   isomorphism of `f^*` of a finite product with the product of the `f^*`.
   Pullback is additive, so it preserves finite products. The square is checked
   on each projection.
5. **Pointwise base change.** `Datum.mem_frameLocus_pullback_iff`: for `t : T`,
   `t` lies in the frame locus of `a.pullback f` iff `f t` lies in that of `a`.
   - The published `cubicDirectImage` (here `S` is locally noetherian and
     `0 < d`) gives two facts. `V` is locally free of rank `6^g d`, and `B` is
     an isomorphism.
   - So `V` and `V'` have finite local bases. For `V'` this uses the published
     `pullbackFiniteLocalBasisRank` and `IsLocallyFreeOfRank.ofIso`.
   - By `Datum.coe_frameLocus` (module `FrameLocusIsoLocus`), both frame loci
     are intersections of iso loci of frame evaluations.
   - By step 4 and the published `mem_isoLocus_iff_of_comm`, the iso locus of a
     pulled-back frame evaluation equals that of `f^*` of the original.
   - By `mem_isoLocus_pullback_iff_of_hasFiniteLocalBasis` (module
     `IsoLocusPullbackFree`), that is the preimage of the original iso locus.
6. `frameLocusBaseChange` concludes by extensionality of opens.

## Provenance

The route follows the remark after Mumford–Fogarty–Kirwan, *Geometric
Invariant Theory*, Definition 7.5 (printed p.130, PDF p.143). There, base
extension commutes with the direct image of the cubic bundle, so linear
rigidifications are functorial. The determinant and stalk argument of
`IsoLocusPullbackFree` replaces the fibrewise linear algebra.

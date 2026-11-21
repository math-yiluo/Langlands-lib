# Proof of isomorphism invariance of the projective frame locus

This module proves the published statement
`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusIsoInvarianceStatement`
with the theorem `frameLocusIsoInvariance`. The theorem is universe-polymorphic
in `u` and adds no hypotheses.

Statement: take `P : Prerequisites.{u}`, a scheme `S`, natural numbers
`g d n m`, data `a b : Datum P S g d n` and `ρ : Fin (m + 2) → Fin (2*g) → ZMod n`.
If `PolarizedIso a b` is nonempty, then `a.frameLocus ρ = b.frameLocus ρ`.

No local noetherianity, positivity of `d`, rank, local freeness or
stalk-locus description is used. The proof compares the two families of frame
evaluations by isomorphisms on both sides. It then shows that the opens in the
two suprema defining the frame loci are the same.

## Notation

Fix `α : PolarizedIso a b`. Write:

- `q = hom α.abelianIso.hom`, the morphism `A_a ⟶ A_b` of total spaces, with
  `A_a = a.abelian.X.left` and `A_b = b.abelian.X.left`;
- `p = b.abelian.X.hom` and `p' = a.abelian.X.hom`, the structure morphisms;
- `L = b.cubicBundle.obj` and `L' = a.cubicBundle.obj`;
- `σ = b.torsionPoint r` and `σ' = a.torsionPoint r`.

The input facts are published:

- `hom_structure`: `q ≫ p = p'`;
- `PolarizedIso.torsionPoint_hom`: `σ' ≫ q = σ` (module
  `FrameEmbeddingTransport`);
- `PolarizedIso.cubicBundlePullbackIso`: an isomorphism `e : q^* L ≅ L'`
  (module `PolarizedBundleTransport`).

`q` is an isomorphism (instance `isIso_hom_of_iso`). `compIso` (module
`Modules/PullbackTransport`) is the generalized composition comparison
`(g ≫ u = u') → g^* u^* ≅ u'^*`.

## Steps of the proof

1. **Direct image along an isomorphism** (`directImageIso`, general). Let
   `q : X ⟶ Y` be an isomorphism, `p : Y ⟶ S`, `p' : X ⟶ S` with `q ≫ p = p'`,
   and `e : q^* L ≅ L'`. Then `p_* L ≅ p'_* L'` is the composite of:
   - `p_*` applied to the unit `L ⟶ q_* q^* L`. The unit is an isomorphism
     because `q_*` is an equivalence (the published `pushforwardEquivalence`,
     module `Modules/SchemeIsoCohomology`). The proof uses the instance
     `Functor.IsEquivalence` that this equivalence provides;
   - `p_* q_*` applied to `e`;
   - Mathlib's `pushforwardComp` and `pushforwardCongr`.
2. **Its adjoint** (`directImageIso_counit`). Pull the comparison back along
   `p'` and compose with the counit `p'^* p'_* L' ⟶ L'`. The result is
   `(compIso q p p')⁻¹` followed by `q^*` of the counit `p^* p_* L ⟶ L` and
   then by `e`. The proof:
   - reduces to `p' = q ≫ p`. There `compIso_rfl` identifies
     `compIso q p (q ≫ p) rfl M` with the component
     `(pullbackComp q p).app M : q^* p^* M ≅ (q ≫ p)^* M`, where
     `M = p_* L`. So the inverse in the formula above is
     `(pullbackComp q p).inv.app M`;
   - applies the adjunction bijection of `p'^* ⊣ p'_*`;
   - rewrites with `homEquiv_conjugate`, Mathlib's
     `conjugateEquiv_pullbackComp_inv` and `homEquiv_comp_map` (module
     `Modules/PullbackUnitProofs`);
   - recognizes the adjunction bijection of the original counit as the
     identity, and `pushforwardCongr rfl` as the identity.
3. **Comparisons** (`rigidificationIso`, `torsionTargetIso`).
   - Step 1 with `q`, `p`, `p'` and `e` gives
     `D : b.rigidificationModule ≅ a.rigidificationModule`.
   - The torsion targets are compared by `c_r : σ^* L ≅ σ'^* L'`. It is the
     inverse of `compIso σ' q σ` applied to `L`, followed by `σ'^* e`.
4. **Torsion evaluations** (`torsionEvaluation_comm`):

   `D.hom ≫ a.torsionEvaluation r = b.torsionEvaluation r ≫ c_r.hom`.

   - The published `Datum.torsionEvaluation_eq` (module
     `FrameLocusBaseChangeProof`) writes both torsion evaluations through
     `pullbackId⁻¹`, `compIso⁻¹` and `σ^*` (resp. `σ'^*`) of
     `cubicEvaluationAdjoint`, the counit of `p^* ⊣ p_*` at `L`.
   - Both sides are precomposed with the isomorphism
     `σ'^* q^* p^* M ≅ M` (`M = b.rigidificationModule`). This isomorphism
     is `compIso σ' q σ`, then `compIso σ p (𝟙 S)`, then `pullbackId`.
   - The equation then follows from:
     - step 2;
     - `compIso_assoc` for the two factorizations of `𝟙 S` through
       `σ' ≫ q ≫ p`;
     - naturality of `pullbackId` and of `compIso` (`compIso_naturality`).

     `compIso_rfl`, `compIso_assoc` and `compIso_naturality` are published in
     module `Modules/LineBundleFlatDescentStr`.
   - This lemma carries the local option
     `set_option maxHeartbeats 900000 in`; the default limit times out.
5. **Frame evaluations** (`frameEvaluation_comm`). `frameTargetIso` is
   `Pi.mapIso` of the `c_{ρ j}` over the entries `j ≠ k`. The square
   `D.hom ≫ a.frameEvaluation ρ k = b.frameEvaluation ρ k ≫ (frameTargetIso).hom`
   is checked on each product projection, where it is step 4.
6. **Conclusion** (`frameLocusIsoInvariance`). Unfold `Datum.frameLocus` and
   show that the two sets of opens indexing the suprema are equal. Fix an open
   `W`, an index `k` and `F = (Scheme.Modules.pullback W.ι)`.
   - Applying `F` to step 5 gives
     `F(D.hom) ≫ F(a.frameEvaluation ρ k) = F(b.frameEvaluation ρ k) ≫ F(frameTargetIso.hom)`.
   - `F` of an isomorphism is an isomorphism.
   - By `isIso_comp_left_iff` and `isIso_comp_right_iff`,
     `F(a.frameEvaluation ρ k)` is an isomorphism exactly when
     `F(b.frameEvaluation ρ k)` is.

The module sets `backward.isDefEq.respectTransparency false`, as other modules
in this development do. It uses no `sorry` and adds no axioms.

## Provenance

Internal (derived) proof of an internal statement; it asserts no external
source. The route is a direct adjunction calculation: functoriality of direct
images and of the torsion evaluations under an isomorphism of abelian schemes.
It avoids the noetherian base-change theorem and the description of the frame
locus by stalk isomorphisms.

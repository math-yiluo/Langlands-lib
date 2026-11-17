# Rigidity of normal idempotent endomorphisms of a Weil restriction, from two inputs

Worker 47.

This module proves

```lean
theorem Langlands.GroupScheme.WeilFactor.weilFactorIdempotentRigidity_of_inputs
    (h1 : RelativeAlmostSimpleNormalIdempotentStatement.{u})
    (h2 : WeilAbelianImageTrivialityStatement.{u}) :
    WeilFactorIdempotentRigidityStatement.{u}
```

so the published statement
[`Reductive.WeilFactorIdempotentRigidityStatement`](WeilFactorIdempotentRigidityStatement.md)
(normal idempotent endomorphisms of `H = R_{B/A}(G')` over any `A`-algebra `T` are the factor
projections of idempotents of `B ⊗_A T`) follows from two inputs:

- [`Reductive.RelativeAlmostSimpleNormalIdempotentStatement`](RelativeAlmostSimpleNormalIdempotentStatement.md)
  (R1): the same statement for a single group `G` over `Spec B`, i.e. the case `B = A`;
- [`Reductive.WeilAbelianImageTrivialityStatement`](WeilAbelianImageTrivialityStatement.md)
  (HV-W): homomorphisms from `H` with pairwise commuting values are trivial.

The theorem has exactly these two hypotheses and no others. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`. Neither input is proved here.

The module imports
[`Reductive.WeilFactorUniquenessReduction`](WeilFactorUniquenessReduction.md) (and through it
[`Reductive.WeilFactorProjection`](WeilFactorProjection.md),
[`AffineIdempotentPoints`](../AffineIdempotentPoints.md) and
[`Algebra.EtaleGraphIdempotent`](../../Algebra/EtaleGraphIdempotent.md)), together with the
two statement modules. It uses from them: the factor projections
`factorProjection A B G e he` with `pointsEquiv_pt_factorProjection`, `eq_factorProjection`,
`factorProjection_comp`, `restrict`; the points `fst`, `snd`, `proj` of a group over a ring
split by an idempotent; and, from the uniqueness reduction, `resA` (a `B`-algebra regarded as
an `A`-algebra), `mulMap A Y : B ⊗_A Y → Y`, the graph idempotent `graphIdem A Y` of `B → Y`,
the embedding `embNat A G : G(Y) → H(Y)` onto the factor cut out by `graphIdem A Y`, and the
projection `projNat A G : H(Y) = G(B ⊗_A Y) → G(Y)` along `mulMap`.

Notation: `pE = AffineWeil.pointsEquiv A B G X : H(X) ≃* G(B ⊗_A X)`, and `pt ψ X` is `ψ` acting
on `H(X)`.

## Proof route

**Step 1: commutation with factor projections (uses HV-W).** For a normal endomorphism `ψ` of
`H` over `T`, which need not be idempotent, and an idempotent `e` of `B ⊗_A T`, let
`c = fp(1 - e) ≫ ψ ≫ fp(e)`, where `fp = factorProjection`. Components for `e` and `1 - e`
commute (`commute_pt_factorProjection`), so normality of `ψ` makes `ψ(fp(1-e) x)` commute with
every `fp(e) h`. Applying `fp(e)` shows that the values of `c` commute with each other. HV-W
with `M = H` then gives `c = 1` (`pt_cross_eq_one`). Since `x = fp(e) x · fp(1 - e) x`
(`pt_factorProjection_mul_one_sub`), this applied to `e` and to `1 - e` gives
`ψ ≫ fp(e) = fp(e) ≫ ψ` (`factorProjection_comm`). The pointwise form for an idempotent `f` of
`B ⊗_A X` over a single `T`-algebra `X` (`proj_pt_comm`) restricts `ψ` along `X.hom` and
evaluates at `Under.mk (𝟙 X)`.

**Step 2: the induced endomorphism `θ` of `G` (definition `theta`).** Let
`T' = tensorB B T = B ⊗_A T` as a `B`-algebra, and `incl B T : T → B ⊗_A T`, `t ↦ 1 ⊗ t`, an
`A`-algebra map when `B ⊗_A T` is regarded as an `A`-algebra through `B`. A
`B ⊗_A T`-algebra `Y` gives the `T`-algebra `liftU A Y`. Define

`θ_Y = projNat_Y ∘ ψ_{liftU Y} ∘ embNat_Y : G(Y) → G(Y)`,

as a composite of whiskered natural transformations, so naturality is automatic. On points it
is `thetaPt_eq`, with point-level wrappers `embPt`, `prjPt`, `ptL` and `thetaPt`.

- `θ` is normal (`thetaPt_normal`), because `embNat` is a homomorphism, `ψ` is normal and
  `projNat ∘ embNat = id`.
- `θ` is idempotent (`theta_idem`). By Step 1 with `f = graphIdem A Y`, `ψ` maps the
  graph-idempotent factor into itself (`embPt_prjPt_ptL`), so
  `embNat (projNat (ψ (embNat y))) = ψ (embNat y)`; then idempotence of `ψ` applies.

**Step 3: apply R1** to `G` over `B`, `T'` and `θ`. This gives a unique idempotent
`e ∈ B ⊗_A T` such that `θ` is the identity modulo `1 - e` and trivial modulo `e` on every
`T'`-algebra.

**Step 4: `ψ` is the factor projection of `e`.** For a `T`-algebra `X`, let
`tensorU B X = B ⊗_A X` as a `B ⊗_A T`-algebra, via `1 ⊗ X.hom`, and let
`kappa X : X → liftU A (tensorU B X)` be `x ↦ 1 ⊗ x`, a map of `T`-algebras. Then:

- `prjPt_incl`: `projNat (H(kappa) h) = pE h`, because `mulMap ∘ (1 ⊗ incl) = id`
  (`mulMap_lT_incl`);
- `embPt_prjPt`: `embNat (projNat h) = pE⁻¹ (proj_g (pE h))` for the graph idempotent `g`;
- `prjPt_symm_proj`: `projNat (pE⁻¹ (proj_g k)) = projNat k`, since `mulMap g = 1`;
- naturality of `ψ` along `kappa` (`pt_naturality`).

Together with Step 1 at `liftU A (tensorU B X)` they give `pE (ψ x) = θ_{B ⊗ X} (pE x)`
(`pointsEquiv_pt_eq_thetaPt`). Since the image of `e` in `B ⊗_A X` under `tensorU B X` is
`baseIdem X e = (1 ⊗ X.hom) e`, Step 3 at `B ⊗_A X` is exactly the defining property of the
target for `e`.

**Step 5: uniqueness.** If `f` has the target property, then `ψ = fp(f)`
(`eq_factorProjection`). Then `θ_Y = proj_{Y.hom f}` (`thetaPt_factorProjection`), using
`mulMap (baseIdem (liftU A Y) f) = Y.hom f` (`mulMap_baseIdem_liftU`). So `f` has the R1
property for `θ`, and the uniqueness in R1 gives `f = e`. Step 5 does not use HV-W.

## Declarations

In `Langlands.GroupScheme.IdempotentPoints` (points over a ring `C` with an idempotent `e`):

- `fst_proj_one_sub`, `snd_proj_one_sub`: the `e`-restriction of the `(1 - e)`-component is
  `1`; its `(1 - e)`-restriction is that of the point;
- `proj_mul_proj_one_sub`: `proj e g * proj (1 - e) g = g`;
- `commute_proj_proj_one_sub`: `proj e g` and `proj (1 - e) h` commute.

In `Langlands.GroupScheme.WeilFactor`:

- Section `Commutation`: `factorProjection_congr`, `baseIdem_one_sub`,
  `pointsEquiv_pt_factorProjection_one_sub`, `pt_factorProjection_mul_one_sub`,
  `commute_pt_factorProjection`, `pt_factorProjection_idem`, `pt_cross_eq_one` (HV-W
  applied), `factorProjection_comm`, `proj_pt_comm`.
- Section `Theta`:
  - `tensorB B T` (abbrev): `B ⊗_A T` as an object of `CommAlgCat B`.
  - `inclAlg B T` (def): `t ↦ 1 ⊗ t` as an `A`-algebra map, for the `A`-algebra structure
    `Algebra.compHom` through `B`.
  - `incl B T : T ⟶ (resA A B).obj (tensorB B T)` (def): `inclAlg` as a morphism; `incl_apply`.
  - `mulMap_lT_tmul`, `mulMap_lT_incl`.
  - `liftU A Y`, `tensorU B X` (abbrevs, written as structure instances so that `.right`
    reduces).
  - `kappa X` (def), `kappa_right`.
- Section `Points`: `embPt`, `prjPt` (defs, typed with `affinePoints`), `prjPt_apply`,
  `prjPt_embPt`, `snd_embPt`, `prjPt_symm_proj`, `graphIdem_isIdempotentElem`,
  `embPt_prjPt_of_snd`, `embPt_prjPt`, `pointsEquiv_affinePointMap_res`, `prjPt_incl`.
- Section `ThetaDef`:
  - `theta G ψ` (def, the entry declaration): the induced endomorphism of
    `Under.forget (tensorB B T) ⋙ G.affinePointFunctor`.
  - `ptL`, `thetaPt` (defs).
  - `thetaPt_eq`, `pt_idem`, `pt_naturality`, `ptL_idem`, `ptL_conj`, `proj_ptL_comm`,
    `thetaPt_normal`, `embPt_prjPt_ptL`, `theta_idem`, `pointsEquiv_pt_eq_thetaPt`,
    `mulMap_baseIdem_liftU`, `thetaPt_factorProjection`.
- Section `Main`: `weilFactorIdempotentRigidity_of_inputs`.

`B ⊗_A T` carries two `A`-algebra structures that are not definitionally equal: the
tensor-product structure, and the one through `B` used by `resA`. Lemmas that need the second
are therefore stated for a variable `B`-algebra `W`, or a variable `Y`, and instantiated
afterwards. Examples are `pointsEquiv_affinePointMap_res`, `mulMap_lT_tmul` and
`graphIdem_isIdempotentElem`.

## Provenance

Provenance: derived. This is a formal deduction written for Task 6492; it is not taken from a
source. It isolates, in the setting of Brian Conrad, *Reductive group schemes* (2014),
Proposition 6.4.4 and its proof, pp.232–233 (registered as
`conrad-2014-reductive-group-schemes`), two separate inputs to the identification of the
factors of `R_{B/A}(G')`:

- the reduction from the Weil restriction to a single factor, done here with the graph
  idempotent of `B → Y` instead of étale localization;
- the perfectness of semisimple groups, used to show that normal idempotent endomorphisms
  commute with the factor projections.

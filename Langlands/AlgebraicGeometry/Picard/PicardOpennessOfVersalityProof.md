# Openness of versality for actual Picard families: proof

Module `Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityProof`, namespace
`Langlands.AlgebraicGeometry.Picard`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`).

The theorem `picardOpennessOfVersality : PicardOpennessOfVersalityStatement.{u}` proves the
Library statement `Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityStatement`
(module `PicardOpennessOfVersalityStatement`) unchanged, at every universe `u`. The module
also contains the helper `affineBaseMap_mem_basicOpen`: the field point
`affineBaseMap χ` of `Spec A` lies in the basic open of `g` iff `χ g ≠ 0`.

## Statement (recalled)

For a noetherian ring `R`, `X` proper and flat over `Spec R`, `U` locally of finite type
over `Spec R`, a line bundle `L` on `U ×_R X`, a point `u₀` of `U` and a field point
`p : Spec K → U` identifying `κ(u₀) ≅ K`, locally of finite type, at which `L` is formally
versal: some open neighbourhood `V` of `u₀` has the property that `L` is formally versal at
every locally-finite-type field point of `U` with image in `V`.

## Proof (as implemented)

1. **Affine chart.** `p.left` is surjective on stalks (it is `Spec.map e.hom` followed by
   `fromSpecResidueField`, a preimmersion) and locally of finite type. By
   `OpennessOfVersality.exists_affineChart` there are an `R`-algebra `A₀` of finite type, an
   open immersion `ι : affineBase R A₀ ⟶ U` and a surjective `χ₀ : A₀ →ₐ[R] K` with
   `affineBaseMap χ₀ ≫ ι = p`. `A₀` is noetherian. The restricted family
   `L₀ = restrictBundle L ι` is formally versal at `affineBaseMap χ₀`
   (`PointFiberArtinianLifting.isFormallyVersalAt_restrictBundle`).
2. **Chart data.** A presentation `s : R[x₁, …, xₙ] → A₀`
   (`Algebra.FiniteType.iff_quotient_mvPolynomial''`) gives `P = R[x]/J²`
   (`OpennessOfVersality.Presentation`), with `π : P → A₀` surjective and nilpotent kernel.
   `ChartFrames.exists_chartFrames` gives a cover `Kc` of `relSpace f P` (compact, since
   `relProj` is proper), frames of `L₀` and lifted units `g` with `hge` and `hg`. The kernel
   `Q = ker π` with its `A₀`-module structure `qModule` (finite), its inclusion `jQ`, the
   derivation `presDer s : P → A₀ⁿ` and its universality (`exists_presDer_factor`), and the
   lifting property `Presentation.exists_lift` complete the data.
3. **Necessity and openness.** `OpennessOfVersality.hOneVanishes_of_isFormallyVersalAt`
   gives `HOneVanishes` with coefficients in `K`; `ChartOpenness.exists_versal_basicOpen`
   (which uses the published `ObstructionCone.openStatement`) gives `g₀ ∈ A₀` with
   `χ₀ g₀ ≠ 0` such that `L₀` is formally versal at every field point `χ'` with
   `χ' g₀ ≠ 0`.
4. **The neighbourhood.** `V = ι(D(g₀))` (image of the basic open under the open
   immersion). It contains `u₀ = p.left pt` since `χ₀ g₀ ≠ 0`
   (`affineBaseMap_mem_basicOpen`, `Scheme.fromSpecResidueField_apply`). For a field point
   `p'` with image in `V`, `p'` factors as `affineBaseMap χ' ≫ ι` (`pointLift`,
   `exists_affineBaseMap_eq`), and `χ' g₀ ≠ 0` because `ι` is injective. Then `L₀` is
   formally versal at `affineBaseMap χ'`, hence `L` at `p'`
   (`ArtinianChartTestReduction.isFormallyVersalAt_of_restrictBundle`).

## Relation to the source

Source: The Stacks Project, Chapter 98 *Artin's Axioms*, registered snapshot
`stacks-artin-axioms-approximation-2026-11-06` (`artin.pdf`). The target is openness of
versality, Definition 98.13.1 (Tag 07XQ, p. 22), for versality at a finite type point in the
sense of Definition 98.12.2 (Tag 07XF, p. 18); the Library statement replaces the
predeformation-category formulation by the actual-point lifting predicate
`ArtinianChartVersality.IsFormallyVersalAt`, as recorded in the statement's Markdown.

The source proves openness of versality by a conditional criterion:

- Lemma 98.23.3 (Tag 07YM, pp. 43–44): given `ξ : E → NL_{A/Λ}` such that liftings are
  detected by `E → NL_{A/A'}` (i) and tangent spaces are `Ext⁰(E, -)` (ii), versality at
  `u₀` is equivalent, for a closed point, to `H⁻¹(ξ ⊗ k)` surjective and `H⁰(ξ ⊗ k)`
  injective. The direction "versal ⇒ (2)" builds, by Artin–Rees, a small essential extension
  `A'/(p')ⁿ → A/pⁿ` from a hypothetical extension class and derives a contradiction with
  versality; the converse lifts maps `A → C` along small extensions.
- Lemma 98.23.4 (Tag 07YN, p. 44): if moreover the cohomology of `E` is finite, the cone
  condition is open around a closed point (More on Algebra, Lemma 78.4).
- Situation 98.24.2 and Lemmas 98.24.3–98.24.4 (Tags 07YX, 07YY, 07YZ, pp. 46–48): from a
  complex `K•` with `T_x = H¹(K• ⊗ -)` and obstruction classes in `H²(K• ⊗ I)` satisfying the
  compatibility (iv), and `K•` perfect, one constructs `ξ` using a presentation
  `P = Λ[x₁, …, xₙ] → A` with kernel `J`, the ring `P/J²` and the naive cotangent complex
  `NL(α) = (J/J² → ⊕ A dxᵢ)`, and reduces to Lemma 98.23.4.
- Lemma 98.12.5 (Tag 07XG, p. 19) passes versality to finite extensions of residue fields
  under (RS); the proof of the openness lemmas first shrinks `U` so that `u₀` is closed
  (p. 46).

The implementation does not apply these conditional criteria: their hypotheses (RS*) and
(i)–(iv) are not assumed or proved for the Picard groupoid, and no perfect complex is supplied
as an input (a finite projective model is constructed inside `openStatement`, see below). It
carries out the same mechanism directly for actual line bundles, in Čech form:

- The role of `K• ⊗ -` and of the cone of `ξ` is played by the obstruction cone of the
  published `ObstructionCone.HOneVanishes` with the data of `OpennessOfVersality.CechData` and
  `Obstruction`: the base-changed Čech complex `cplx f K A₀` of the structure sheaf of the
  relative space of `P = R[x]/J²` (the source writes its polynomial ring as `P` and its
  thickening as `P/J²`; here `P` already denotes the thickening), the module
  `F = A₀ⁿ = ⊕ A₀ dxᵢ` with the derivation `D = presDer` (partial derivatives modulo `J`),
  the conormal module `Q = J/J²` with `δ = D ∘ jQ` (the differential `J/J² → ⊕ A₀ dxᵢ` of
  `NL(α)`), the 2-cochain `z` (the obstruction of the lifted transition functions over
  `P = R[x]/J²`, as `o_x(P/J²)` in the proof of Lemma 98.24.3) and the 1-cochain `θ` (their
  derivative, the canonical element). `z` is a cocycle (`dz = 0`), while `θ` need not be
  closed: the identity relating them is `dθ = δ_* z`. `HOneVanishes` with coefficients in `M`
  is the vanishing of the corresponding first cohomology of the cone.
- Necessity at a closed point (the direction "versal ⇒ (2)" of Lemma 98.23.3) is
  `OpennessOfVersality.hOneVanishes_of_isFormallyVersalAt`: as in the source, Artin–Rees
  (`NecessityRings.exists_pow_vanish`) yields an Artinian extension realizing a given
  linear form on `J/J²`, but the deformation of the line bundle is glued explicitly from a
  Čech cocycle (`NecessityGluing`) and versality is applied to the resulting actual point;
  the lift is read back through the universality of the derivation `presDer`
  (`Presentation.exists_presDer_factor`, the analogue of using `NL(α)`). The closed point is arranged by `exists_affineChart`, which makes the residue map
  `χ₀ : A₀ → K` surjective, matching the shrinking step on p. 46.
- Openness (Lemma 98.23.4 with More on Algebra, Lemma 78.4) is the published
  `ObstructionCone.openStatement`, a linear-algebra statement for a flat bounded complex with
  finitely generated cohomology. Its inputs are proved, not assumed: the Čech cochains are
  flat over `A₀` (base change of `CechData.flat_cochain`, from flatness of `f`), bounded
  (`subsingleton_cplx`) and have finitely generated cohomology
  (`CechData.finiteCohomology_dif`, from properness of `f`); `F = A₀ⁿ` is finite free; `Q`
  is finite (`Presentation.qModule_finite`); `dθ = δ_* z` and `dz = 0` are
  `dif_thetaObs` and `dif_zObs`. No perfect model is required as a Picard input:
  `openStatement` itself constructs a bounded complex of finite projective modules
  quasi-isomorphic to the Čech complex (`boundedFlatComplexProjective`, step 1 of its proof)
  from boundedness, flatness and finite cohomology.
- Sufficiency (the direction "(2) ⇒ versal") is `ChartOpenness.exists_versal_basicOpen`, via
  `BaseLifting` and the published `Sufficiency.exists_lift`: vanishing with coefficients in the
  kernel of an elementary surjection of Artinian tests gives the lifting of actual points.
  It uses the square-zero lifting property of `P = R[x]/J²` (`Presentation.exists_lift`).
- Lemma 98.12.5 (Tag 07XG) is not needed: `openStatement` gives vanishing with coefficients
  in every module over every `A₀`-algebra in which `g₀` is a unit, in particular over
  Artinian tests with any residue field `K'`. Hence versality holds directly at every field
  point `χ' : A₀ → K'` with `χ' g₀ ≠ 0`, not only at points with residue field `κ(u)`, and
  no condition (RS), algebraicity, atlas or representability of the Picard functor is used.

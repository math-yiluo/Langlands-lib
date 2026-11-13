# Formally versal Picard line bundles over complete local bases: proof

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleProof`.

Author: Worker 5124, for task `72b6bcbb-1ed4-456e-a4d3-aadbfdc6fe56`.

The theorem `Langlands.AlgebraicGeometry.Picard.finiteTypeFormalVersalBundle`
proves the published proposition
`Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleStatement.{u}`
at every universe `u`. Its type is exactly that proposition. The statement
module and its Markdown are unchanged.

## What is proved

Let `R : Type u` be a commutative ring of finite type over `ℤ`, `X` a scheme
over `Spec R` with `X.hom` proper and flat, `K : Type u` a field of finite type
over `R`, and `L₀` an actual line bundle on
`(relativeSpace X.hom).obj (ArtinianTest.residueBase R K)`. The proof produces:

- the ring `A = ArtinianPicardSourceTower.limitRing ε₀ hε₀ f L₀ s₀` (data below),
  with its published Noetherian, local and maximal-ideal-adic completeness
  instances and its `R`-algebra structure;
- `ε = limitAugmentation ε₀ hε₀ f L₀ s₀ : A →ₐ[R] K`, which is surjective by
  `limitAugmentation_surjective`;
- `L = ArtinianPicardTowerAlgebraization.effectiveBundle ε₀ hε₀ f L₀ s₀`, an
  actual line bundle on `(relativeSpace f).obj (affineBase R A)`. By
  definition `affineBase R A` is `Over.mk (Spec.map (CommRingCat.ofHom
  (algebraMap R A)))`, the base required by the statement;
- `p = residuePoint ε₀ hε₀ f L₀ s₀ = affineBaseMap ε`, with
  `p.left = Spec.map (CommRingCat.ofHom ε.toRingHom)` by `residuePoint_left`
  (this holds by `rfl`);
- formal versality `IsFormallyVersalAt X.hom L p` (below);
- the isomorphism `effectiveResidueIso : residueBundle X.hom L p ≅ L₀`.

No hypothesis is added. `R` may be non-reduced or not a domain. `X` is any proper
flat scheme over `Spec R`, `K` any field of finite type over `R`, and `L₀` any
line bundle on `X_K`.

## The implemented argument

The proof is an assembly of published Library constructions and theorems. It
introduces no new definition or lemma. Write `f = X.hom` and `M = L₀`.

1. **Finiteness of the base.** Two local facts are derived:
   `Module.Finite R K` (published
   `FiniteTypePicardInitialStage.residueModuleFinite`, from the Jacobson
   property of finite-type `ℤ`-algebras and the Zariski lemma), and
   `IsNoetherianRing R` (Mathlib's `Algebra.FiniteType.isNoetherianRing ℤ R`).
   They supply the instances of the published complete polynomial source.

2. **Source and initial stage.** The published `FiniteTypePicardInitialStage`
   gives the complete Noetherian local `R`-algebra `S = sourceRing f M`. It
   also gives its surjective augmentation `ε₀ = augmentation f M : S →ₐ[R] K`
   (with `hε₀ = augmentation_surjective f M`) and the initial stage
   `s₀ = stage f M`. This stage is the actual pointed finite tangent-basis
   family `FiniteBasisPicardFamily.family f M` on the split square-zero test
   `K ⊕ K^Index`, presented as a quotient of `S`.

3. **Hull and effective bundle.** The published Picard source tower over
   `(S, ε₀, s₀)` has limiting quotient ring `A = limitRing ε₀ hε₀ f M s₀`. The
   published `ArtinianPicardTowerAlgebraization` builds the formal line-bundle
   system of the tower and algebraizes it with the published proof
   `properFormalLineBundleEffectivity` (Grothendieck existence). The result is
   `effectiveBundle`, together with `residuePoint` and the isomorphism
   `effectiveResidueIso` with `M`. These provide `A`, `ε`, `L`, `p`, condition 2
   and condition 4 of the statement.

4. **Ring-map lifting (RL).** For every elementary surjection `q : B' ⟶ B` of
   Artinian tests with a one-dimensional kernel `c : Kernel q ≃+ K`, every
   actual line bundle `N` on `X_{B'}` and every actual point `y` of `L` with
   values in `N` over `baseMap q` with closed point `p`, the published
   `ArtinianPicardTowerRingLifting.exists_ringLift` extends `y.1` along
   `baseMap q`. Its hypothesis `hlift` asks that augmentation-compatible maps
   out of `S` lift across every surjective test arrow. This hypothesis is the
   published `FiniteTypePicardInitialStage.postcomp_surjective`, which holds
   because `S` is a completed polynomial source.

5. **Lifting along the dual numbers (TL).** The published
   `FiniteBasisPicardTangentLifting.hasLiftingForAt f M` proves the
   full-specified-isomorphism lifting predicate
   `HasLiftingForAt f s₀.family.right.of (reduction s₀.test) (dualReduction R K)`
   for the initial basis family. Here `s₀.family.right.of` is by definition
   `FiniteBasisPicardTangentLifting.bundle f M`. The published
   `ArtinianPicardTowerTangentLifting.hasLiftingForAt_dualReduction` transfers
   it to `HasLiftingForAt f L p (dualReduction R K)`.

6. **Formal versality.** The published
   `ArtinianPrincipalLifting.isFormallyVersalAt_of_ringLifting`, applied to
   (RL) and (TL), gives `IsFormallyVersalAt f L p`. It needs `f` flat.

The final term packages these data and proofs in the order of the statement's
existential. The instance arguments are found by `inferInstance`: the published
`ArtinianPicardSourceTower` instances `IsLocalRing` and `IsNoetherianRing` on
`limitRing`, and `ArtinianPicardSourceCompletion.limitRing_isAdicComplete`.

### Actual inputs

All inputs are published Library theorems and constructions, imported by Lean
name:

- `FiniteTypePicardInitialStage` (`residueModuleFinite`, `sourceRing`,
  `augmentation`, `augmentation_surjective`, `stage`, `postcomp_surjective`);
- `ArtinianPicardSourceTower` (`limitRing`, `limitAugmentation`,
  `limitAugmentation_surjective`, and its local and Noetherian instances) and
  `ArtinianPicardSourceCompletion.limitRing_isAdicComplete`;
- `ArtinianPicardTowerAlgebraization` (`effectiveBundle`, `residuePoint`,
  `residuePoint_left`, `effectiveResidueIso`). This module uses the proved
  theorem `properFormalLineBundleEffectivity`;
- `ArtinianPicardTowerRingLifting.exists_ringLift`;
- `ArtinianPicardTowerTangentLifting.hasLiftingForAt_dualReduction`;
- `FiniteBasisPicardTangentLifting.hasLiftingForAt`;
- `ArtinianPrincipalLifting.isFormallyVersalAt_of_ringLifting`.

The proof takes no unproved proposition as input. In particular it does not
use `FiniteTypeVersalChartStatement`, `VersalAlgebraizationStatement`,
`FiniteTypePointSmoothChartStatement`, `VersalSmoothNeighbourhoodStatement`,
`PicardOpennessOfVersalityStatement`, `FieldPicardStackAtlasStatement`, any
Picard representability statement, or an assumed atlas or formal-versal family.
A development `lean_check` with declaration inspection (Lake build) reported
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the sources

The cited sources are The Stacks Project, registered as
`stacks-formal-deformation-theory-2026-11-06` (Chapter 90 "Formal Deformation
Theory", chapter PDF version ed88ff78, numbered internally without the chapter
prefix), `stacks-artin-axioms-approximation-2026-11-06` (`artin.pdf`,
Chapter 98 "Artin's Axioms") and
`stacks-formal-line-bundle-effectivity-2026-11-03` (`088C.html`).

- **Proof of Lemma 98.13.8 (Tag 07XY), `artin.pdf` statement printed p. 23,
  proof p. 24.** A versal formal object over `x₀ = L₀` comes from Formal
  Deformation Theory Lemma 90.13.4, and assumption (3) makes it effective.
  Steps 2–6 above carry out this first step for the Picard stack of `X`.
- **Lemma 90.13.4 (Tag 06IW), Chapter 90 printed p. 39, proof pp. 39–40.**
  Stacks takes a power series ring `S = R[[X₁, …, X_r]]` with `r = dim T_F`.
  Its object `ξ₂` over `S/J₂` is given by a basis of the tangent space. It
  chooses `J_{n+1}` minimal among the ideals over which `ξ_n` lifts, and the
  hull is `S/⋂ J_n`. In the Library, step 2 supplies the complete polynomial
  source and the stage over the split test `K ⊕ K^Index` carrying a tangent
  basis. The published source tower iterates `ArtinianPicardSourceStep.Stage.next`,
  the quotient by the least admissible equation ideal (its universal property
  is `ArtinianPicardSourceMinimality`). Its limit ring `A` is the quotient by
  the intersection `limitingEquations` of all stage ideals (step 3). The proof's dichotomy
  "`S/J_n ×_A B → S/J_n` has a section or is an essential surjection" is the
  case split in step 4. The published `exists_ringLift` does this with an
  explicit computation for one-dimensional kernels and with the minimality of
  the tower successor.
- **Lemma 90.13.2 (Tag 06IU), Chapter 90 printed p. 37.** Versality is
  equivalent to (1) surjectivity on tangent spaces and (2) lifting along small
  extensions. In the Library, condition (1) is replaced by actual lifting
  along the dual numbers (step 5). Condition (2) is ring-map lifting along
  one-dimensional small extensions (step 4). The criterion is the published
  `isFormallyVersalAt_of_ringLifting` (step 6). Conditions (S1) and (S2) for
  line bundles are the published flat-base gluing theorems used inside it.
- **Proposition 30.25.4 (Tag 088C).** Grothendieck existence for line bundles
  over a complete Noetherian local ring makes the formal object effective
  (step 3, through `properFormalLineBundleEffectivity`).
- **Definition 98.12.1 and Lemma 98.12.3 (Tags 0CXJ, 0CXK), `artin.pdf`
  printed pp. 18–19.** The statement's predicate `IsFormallyVersalAt` at the
  closed point of `Spec A` is the actual point-fibre form of versality of the
  formal object of `L`, as explained in the statement Markdown. The proof works
  with this actual predicate throughout and does not pass through deformation
  functors.

The finite dimensionality of the tangent space `H¹(X_K, 𝒪)` (hypothesis (4) of
Lemma 90.13.4) enters through the published finite tangent-basis family of
step 2, whose index is finite by the published
`ArtinianDualNumberComparison.finiteDimensional_classes`.

## Provenance

Internal assembly of published Library results; the route is the one cited
above. The implementation follows the proof of Stacks Lemma 90.13.4 with the
replacements described in steps 4 and 5.

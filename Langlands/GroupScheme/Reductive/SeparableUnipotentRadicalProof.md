# Unipotent radicals under separable algebraic extension: proof

Author: Worker 169. The proof route follows the outline of a draft by Worker 3483
(Task 3483) described in the context of Task 5659; that draft's files were not
available in this instance, so the Lean code here was written anew.

The theorem `Langlands.GroupScheme.separableAlgebraicUnipotentRadical` proves the
unchanged published proposition
`Langlands.GroupScheme.SeparableAlgebraicUnipotentRadicalStatement.{u}`
(module `Langlands.GroupScheme.Reductive.SeparableUnipotentRadicalStatement`) at an
arbitrary universe `u`, with no added hypothesis. The module also proves two
auxiliary theorems in the namespace `Langlands.GroupScheme.SeparableUnipotentRadical`.

Throughout, `k` is a field, `G` is a group scheme over `Spec k` with instances
`Smooth G.X.hom`, `IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`, and
`i : U ⟶ G` satisfies `IsUnipotentRadical i`. For a field extension `k → L`, the
base change of `i` is
`(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map i`.

## Step 1: Galois extensions of any degree

`SeparableUnipotentRadical.isUnipotentRadical_baseChange_galois`: if `[IsGalois k L]`
(no finiteness assumed), then the base change `i_L` of `i` is a unipotent radical of
`G_L` in the sense of `IsUnipotentRadical`.

Proof as implemented. Write `c : Spec L ⟶ Spec k`.

1. `G_L` is smooth and affine over `L` (pullback instances, after unfolding its
   structure map to `pullback.snd G.X.hom c`) and connected
   (`connectedSpace_baseChange_of_smooth_affine`). So `unipotentRadicalExistence`
   gives an `L`-radical `i' : U' ⟶ G_L`.
2. `IsUnipotentRadical.galoisRadicalDescent` applied to `i'` yields a
   `UnipotentRadicalDescent i'`: a `k`-group `source`, a `k`-radical
   `inclusion : source ⟶ G`, and an isomorphism `comparison : source_L ≅ U'` with
   `(inclusion)_L = comparison.hom ≫ i'` (field `recovers`).
3. `i` and `inclusion` are both `k`-radicals of `G`, so they have the same image on
   every test scheme (`IsUnipotentRadical.range_eq`). Since both are closed subgroups,
   `IsClosedSubgroup.sourceIsoOfRangeEq` gives `e : U ≅ source`, and
   `IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp` gives `e.hom ≫ inclusion = i`.
4. Hence `i_L = (e_L).hom ≫ (inclusion)_L = (e_L ≪≫ comparison).hom ≫ i'`, by
   functoriality of base change and `recovers`. An `L`-radical precomposed with an
   isomorphism of its source is again an `L`-radical
   (`IsUnipotentRadical.precomp_iso`), which proves the claim.

## Step 2: separable algebraic extensions (Part 1 of the target)

`SeparableUnipotentRadical.isUnipotentRadical_baseChange`: if
`[Algebra.IsSeparable k K]`, then the base change `i_K` is a `K`-radical of `G_K`.

Proof as implemented. Let `L = SeparableClosure k`. Mathlib's `IsSepClosed.lift`
gives a `k`-algebra map `ι : K →ₐ[k] L`; give `L` the `K`-algebra structure
`ι.toRingHom.toAlgebra` (the `k`-algebra structure on `L` is Mathlib's own). Write
`b : Spec K ⟶ Spec k`, `d : Spec L ⟶ Spec K` and `c : Spec L ⟶ Spec k` for the
induced morphisms. Then `d ≫ b = c`, by `Spec.map_comp`,
`CommRingCat.ofHom_comp` and `ι.commutes`.

1. `L/k` is Galois (Mathlib's instance for a separable closure), so Step 1 shows that
   `(baseChange c).map i` is an `L`-radical. Rewriting with `d ≫ b = c`, so is
   `(baseChange (d ≫ b)).map i`.
2. The naturality square `baseChangeCompIso_hom_naturality b d i` gives
   `(baseChange d).map ((baseChange b).map i) =
   (baseChangeCompIso b d U).symm.hom ≫ (baseChange (d ≫ b)).map i ≫
   (baseChangeCompIso b d G).hom`. The right side is an `L`-radical by
   `IsUnipotentRadical.comp_iso` (ambient isomorphism) followed by
   `IsUnipotentRadical.precomp_iso` (source isomorphism).
3. So the base change along `K → L` of `i_K` is an `L`-radical. `G_K` is affine over
   `K`, and `i_K` is a closed subgroup (`IsClosedSubgroup.baseChange`). Therefore
   `IsUnipotentRadical.of_baseChange`, applied to the extension `K → L`, shows that
   `i_K` is a `K`-radical of `G_K`.

## Step 3: the main theorem

`separableAlgebraicUnipotentRadical` introduces `k`, `K`, `G` and the three
hypotheses `Smooth G.X.hom`, `IsAffineHom G.X.hom`, `ConnectedSpace G.X.left`,
installs them as local instances, and proves the conjunction:

- Part 1 is Step 2.
- Part 2, forward: `pseudoReductiveSeparableExtension k K G` (the published proof of
  `PseudoReductiveSeparableExtensionStatement`).
- Part 2, converse: if `G_K` is pseudo-reductive, its field
  `hasTrivialUnipotentRadical` and `HasTrivialUnipotentRadical.of_fieldExtension`
  (which uses `IsAffineHom G.X.hom`) give `HasTrivialUnipotentRadical G`. Together
  with the three hypotheses on `G` this is `IsPseudoReductive G`.

## Published inputs used

| Lean name | Module |
| --- | --- |
| `SeparableAlgebraicUnipotentRadicalStatement` (target) | `Langlands.GroupScheme.Reductive.SeparableUnipotentRadicalStatement` |
| `IsUnipotentRadical`, `IsUnipotentRadical.range_eq` | `Langlands.GroupScheme.Reductive.UnipotentRadical` |
| `unipotentRadicalExistence` | `Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof` |
| `IsUnipotentRadical.galoisRadicalDescent` | `Langlands.GroupScheme.Reductive.GaloisRadicalDescent` |
| `UnipotentRadicalDescent` (and its fields) | `Langlands.GroupScheme.Reductive.RadicalOverlapDescent` |
| `IsClosedSubgroup.sourceIsoOfRangeEq`, `IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp` | `Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction` |
| `IsUnipotentRadical.precomp_iso`, `IsUnipotentRadical.of_baseChange` | `Langlands.GroupScheme.Rational.UnipotentRadicalProperties` |
| `IsUnipotentRadical.comp_iso` | `Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport` |
| `baseChangeCompIso_hom_naturality` | `Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction` |
| `baseChangeCompIso` | `Langlands.AbelianScheme.Tate.BaseChangeCoherence` |
| `IsClosedSubgroup.baseChange` | `Langlands.GroupScheme.SubgroupBaseChange` |
| `connectedSpace_baseChange_of_smooth_affine` | `Langlands.GroupScheme.GeometricConnectedness` |
| `pseudoReductiveSeparableExtension` | `Langlands.GroupScheme.Reductive.PseudoReductiveSeparableExtensionProof` |
| `HasTrivialUnipotentRadical.of_fieldExtension` | `Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof` |
| `algebraBaseMap` (an abbreviation, used in a `change`) | `Langlands.GroupScheme.Torus.LatticeGalois` |

From Mathlib: `SeparableClosure`, `IsSepClosed.lift`, the `IsGalois` instance for a
separable closure, `Spec.map_comp` and `CommRingCat.ofHom_comp`.

The module sets `backward.isDefEq.respectTransparency false` and
`maxHeartbeats 800000`, as do the imported modules it relies on. The development
check reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is an internal deduction from the published results listed above. It changes
neither the statement's Lean/Markdown pair nor anything it imports.

The target derives from Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second
edition (2015), Proposition 1.1.9(1), printed pp. 8–9 (PDF pp. 34–35), registered as
`conrad-gabber-prasad-2015-pseudo-reductive` (SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`). The source
treats the Galois case by Galois descent of `R_{u,k'}(G_{k'})` and observing that the
descent lies in `R_{u,k}(G)`; Step 1 implements this with the Library's descent
theorem and the uniqueness of radical images. The reduction of the separable
algebraic case to a separable closure (Step 2) uses reflection of the radical
predicate along `K → L` instead of the source's further argument for general
separable extensions, which the restricted statement does not need.

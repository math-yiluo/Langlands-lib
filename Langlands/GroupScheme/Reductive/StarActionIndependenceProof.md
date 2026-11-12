# Independence of the star action: proof

Proof author: Worker 3483. Worker 162 reused the complete proof from Task 3483 shared
draft revision 5 and expanded the published-input documentation for Task 5308.

This module proves `Langlands.GroupScheme.StarActionIndependenceStatement` (module
`Langlands.GroupScheme.Reductive.StarActionStatement`). The theorem is
`Langlands.GroupScheme.StarActionIndependence.starActionIndependence`, at universe
parameter `u`, with no added hypotheses. `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`.

The statement: let `d` and `d'` be two Galois pinning data for `G` over `k` with
respect to `E`. Then some `E`-point `g` of `G_E` conjugates the torus of `d` onto the
torus of `d'` through an isomorphism `φ`. The induced isomorphism `e` of root data has
weight map `χ ↦ φ⁻¹ ≫ χ` (`characterLattice.congr φ`), preserves the chosen bases, and
satisfies `e ∘ (d.starAction σ) = (d'.starAction σ) ∘ e` for every `σ ∈ Aut_k(E)`.

## Route

The proof follows the usual argument for the `*`-action (literature id
`milne-2022-algebraic-groups`, §25.c, printed p.555). Any two split maximal tori of `G_E` are conjugate
over `E`. A conjugating point can be corrected by an element of the Weyl group so that
it carries one base to the other. The Galois conjugate of the conjugating point differs
from the point by an element of the normalizer of a torus. That element acts on the
root datum through the Weyl group, and the based projection kills it.

### 1. Root-datum algebra (section `RootData`, `Pinnings`)

- `equiv_ext_of_weightMap`: an equivalence of root data is determined by its weight
  map. The coweight map is the transpose, and the index map is recovered from roots.
- `conjAut e : P.Aut →* P'.Aut`, conjugation by an equivalence `e`. It sends the
  reflection at `i` to the reflection at `e.indexEquiv i` (`conjAut_reflection`), so it
  sends the Weyl group into the Weyl group (`conjAut_mem_weylGroup`). Also
  `e.comp x = (conjAut e x).comp e` (`comp_eq_conjAut_comp`).
- `mem_support_iff_of_isPos`: if `e` preserves positivity of roots for two bases, it
  carries simple roots to simple roots. It uses the Library characterization
  `RootPairing.Base.mem_support_iff_positive_indecomposable`
  (`Reductive/RootDatumGaloisSimpleRoots`).
- `conjAut_mem_basedRootDatumAut` and `comp_basedRootDatumProjection`: if `e` preserves
  the bases and `x' * (conjAut e x)⁻¹` lies in the Weyl group, then
  `e ∘ π(x) = π(x') ∘ e`, where `π` is `SplitPinning.basedRootDatumProjection`. It uses
  `basedRootDatumProjection_correction` and `basedRootDatum_representative_unique`
  (`Reductive/BasedRootDatumProjection`).
- `exists_weyl_comp_preserves_base`: for any equivalence `e₀` of the root data of two
  split pinnings, some Weyl element `w` makes `w ∘ e₀` preserve the bases. The proof
  transports the positive cocharacter of the first pinning by `e₀`. The cocharacter
  pairs nonzero with every root (`latticePairing_root_positiveCocharacter_ne_zero` and
  `_pos_iff`, `Reductive/SplitBorelCell`). Then
  `Langlands.LinearAlgebra.RootDatumWeylChambers.exists_same_signs` gives a Weyl element
  moving it into the chamber of the second pinning's positive cocharacter;
  `reflectionSubgroup_le` places that element in the Weyl group.

### 2. Conjugating points (section `Conjugation`, `Descent`)

`IsConjugatingPoint i j n φ` abbreviates
`i ≫ (H.innerIso n).hom = groupHom φ.hom ≫ j`. It is the two-torus analogue of the
Library predicate `IsNormalizingPoint`. Lemmas:

- `conj_inv`, `conj_mul`, and their wrapped forms `IsConjugatingPoint.inv` and `.mul`
  (`innerIso_inv_hom`, `innerIso_mul_hom`, `InnerAutomorphismHom`).
- `IsConjugatingPoint.transport` along an ambient isomorphism compatible with
  isomorphisms of the two subgroups. It copies the proof of the Library
  `IsNormalizingPoint.transport` (`Rational/CrossTorusWeylTransport`) and uses
  `innerIso_hom_comp` (`ConjugacyBaseChange`).
- `IsConjugatingPoint.baseChangeBasePoint`: pullback of the point (`baseChange_innerIso_hom`,
  `Rational/SubgroupConjugacyDescent`).
- `IsConjugatingPoint.baseChange_descent`: for `a : S ⟶ S` over `b : S ⟶ B`, the point
  `baseChangeBasePoint a _ g ≫ (descentBaseChangeIso b a ha H).hom.hom.hom` conjugates
  the base-changed subgroups through the canonical descent transport
  `(descentBaseChangeIso T)⁻¹ ≪≫ (baseChange a).mapIso φ ≪≫ descentBaseChangeIso T'`
  (`CommGroupScheme.descentBaseChangeIso`, `Reductive/RootDatumGaloisCoroots`;
  `descentBaseChangeIso_naturality`, `CocharacterTransportNaturality`).
- `descentTransport_inv_comp`: precomposition of characters with the transported
  isomorphism intertwines `characterLattice.transport`. It copies the proof of the
  Library `characterAut_descentTransport`.

### 3. Pinned tori over a field (section `Pinned`)

- `exists_conj`: the tori of two split pinnings of `H` are conjugate by a rational
  point. It uses the published `smoothMaximalSplitTorusConjugacy`
  (`Rational/SmoothMaximalSplitTorusConjugacyProof`) and
  `IsMaximalTorus.isMaximalSplitTorus` (`Torus/MaximalSplitComparison`).
- `exists_conj_based`: the conjugation can be chosen so that the induced root-datum
  equivalence `e` has weight map `χ ↦ φ⁻¹ ≫ χ` and preserves the bases.
  `rootDatumEquivOfTorusCompatibleIso` and its `_weightMap`
  (`Reductive/GeometricRootDatumComparison`) give `e₀` from the conjugation.
  `exists_weyl_comp_preserves_base` gives `w`. The published `weylGroup`
  (`Reductive/RootDatumWeylProof`: `weylImage i = P.weylGroup.map weightHom`) realizes
  `w` by a normalizer point `n`, and the new conjugating point is `n * g₀`
  (`isNormalizingPoint_normalizingAut`, `Torus/Maximal`).
- `exists_weyl_of_isNormalizingPoint`: conversely, a rational point normalizing the torus
  of a split pinning through `τ` acts on characters (`χ ↦ τ⁻¹ ≫ χ`) as an element of
  the Weyl group (`weylGroup`, `mem_normalizerPoints`, `IsNormalizingPoint.unique`).

### 4. Galois equivariance (section `Main`)

Fix `σ` and let `a = Spec σ`, `b = Spec E → Spec k`.

- `isConjugatingPoint_of_conj` restates the conjugation of the statement.
- `IsConjugatingPoint.baseChange_descent` gives the transported point `g_σ` and the
  transported isomorphism `φ_σ`. Then `g_σ * g⁻¹` normalizes the torus of `d'` through
  `φ⁻¹ ≪≫ φ_σ` (`isNormalizingPoint_of_isConjugatingPoint`). So it gives a Weyl
  element `w` with `w(χ) = (φ⁻¹ ≪≫ φ_σ)⁻¹ ≫ χ`.
- `galoisAction_weightMap_apply`: `d.galoisAction σ` acts on characters by
  `characterLattice.galoisRepresentation`
  (`IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus_weightMap`).
- `galoisAction_eq_weyl_mul`: `d'.galoisAction σ = w * conjAut e (d.galoisAction σ)`.
  This is a computation on weight maps using `descentTransport_inv_comp` and
  `characterLattice.galoisRepresentation_apply` (`Torus/LatticeGalois`).
- `starAction_intertwine` combines this with `comp_basedRootDatumProjection`.

The final theorem takes `g`, `φ`, `e` from `exists_conj_based` and applies
`starAction_intertwine`.

The point `g_σ` is the Galois conjugate `GaloisPointComparison.rationalConjugate`
(`rationalConjugate_eq_baseChange_descent`). The proof does not need this
identification. Implementation note: the types of `hσ` and `hn` in
`starAction_intertwine` are left to be inferred. Restating them by hand made the kernel
compare differently elaborated copies of the transported point and timed out.


## Published inputs used directly

All names in the table are in namespace `Langlands.GroupScheme`, except the explicitly
qualified root-pairing and linear-algebra names. Module names are complete Lean import
names. These are existing project theorems used by this proof; helpers introduced in
this module are described above.

| Published theorem(s) | Module | Use |
| --- | --- | --- |
| `RootPairing.Base.mem_support_iff_positive_indecomposable` | `Langlands.GroupScheme.Reductive.RootDatumGaloisSimpleRoots` | Recover the simple roots from positivity. |
| `SplitPinning.finite_rootDatum_weylGroup`, `SplitPinning.basedRootDatumProjection_correction`, `SplitPinning.basedRootDatum_representative_unique` | `Langlands.GroupScheme.Reductive.BasedRootDatumProjection` | Finiteness for the chamber argument and uniqueness of the based representative of a Weyl coset. |
| `SplitPinning.latticePairing_root_positiveCocharacter_pos_iff`, `SplitPinning.latticePairing_root_positiveCocharacter_ne_zero` | `Langlands.GroupScheme.Reductive.SplitBorelCell` | The chosen cocharacter determines the chosen positive roots and is regular. |
| `Langlands.LinearAlgebra.RootDatumWeylChambers.exists_same_signs`, `Langlands.LinearAlgebra.RootDatumWeylChambers.reflectionSubgroup_le` | `Langlands.LinearAlgebra.RootDatumWeylChambers` | Correct a root-datum equivalence by a Weyl element to preserve the chosen bases. |
| `innerIso_inv_hom`, `innerIso_mul_hom` | `Langlands.GroupScheme.InnerAutomorphismHom` | Invert and compose actual conjugating points. |
| `innerIso_hom_comp` | `Langlands.GroupScheme.ConjugacyBaseChange` | Transport conjugation through an ambient group-scheme isomorphism. |
| `baseChange_innerIso_hom` | `Langlands.GroupScheme.Rational.SubgroupConjugacyDescent` | Pull back a conjugating point. |
| `descentBaseChangeIso_naturality` | `Langlands.GroupScheme.CocharacterTransportNaturality` | Transport both torus inclusions through canonical descent. |
| `smoothMaximalSplitTorusConjugacy` | `Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof` | Conjugate the two pinned split maximal tori over the field itself. |
| `IsMaximalTorus.isMaximalSplitTorus` | `Langlands.GroupScheme.Torus.MaximalSplitComparison` | Supply maximal splitness for rational torus conjugacy. |
| `rootDatumEquivOfTorusCompatibleIso_weightMap` | `Langlands.GroupScheme.Reductive.GeometricRootDatumComparison` | Identify the weight map of the root-datum equivalence induced by conjugation. |
| `weylGroup` | `Langlands.GroupScheme.Reductive.RootDatumWeylProof` | Realize Weyl elements by rational normalizer points and identify normalizer actions as Weyl actions. |
| `mem_normalizerPoints`, `isNormalizingPoint_normalizingAut`, `IsNormalizingPoint.unique` | `Langlands.GroupScheme.Torus.Maximal` | Pass between normalizer membership and the actual induced torus automorphism. |
| `IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus_weightMap` | `Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots` | Identify the weight map of the ordinary Galois action. |
| `galoisBaseMap_over`, `characterLattice.galoisRepresentation_apply` | `Langlands.GroupScheme.Torus.LatticeGalois` | Regard `Spec σ` as a map over `Spec k` and compute the Galois action as character transport. |

The proof also uses the published constructions `SplitPinning.basedRootDatumProjection`
(`Langlands.GroupScheme.Reductive.BasedRootDatumProjection`),
`rootDatumEquivOfTorusCompatibleIso`
(`Langlands.GroupScheme.Reductive.GeometricRootDatumComparison`),
`CommGroupScheme.descentBaseChangeIso`
(`Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots`), and the actual character,
normalizer and base-change interfaces from the modules named above.
`IsNormalizingPoint.transport` (`Langlands.GroupScheme.Rational.CrossTorusWeylTransport`),
`IsNormalizingPoint.baseChange_descent` and `rationalConjugate_eq_baseChange_descent`
(`Langlands.GroupScheme.Rational.NormalizerGaloisAction`), and
`characterAut_descentTransport` (`Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots`)
are provenance for the two-torus transport arguments and their interpretation; they are
not additional premises of the theorem.

The remaining steps use Mathlib's root-datum equivalence/reflection identities, linear-map
extensionality, subgroup operations, and category/functor/isomorphism identities. In
particular, `RootPairing.Hom.weight_coweight_transpose_apply` and
`RootPairing.Hom.root_weightMap_apply` are from
`Mathlib.LinearAlgebra.RootSystem.Hom`. No new geometric hypothesis or unproved
statement is supplied as an input.

## Verification

Worker 162 checked the unchanged Lean proof against the current Library in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`: the Lake build passed with no errors or warnings,
and declaration inspection returned the sole universe parameter `u` and the axioms
`propext`, `Classical.choice`, and `Quot.sound`. The theorem's declared type is exactly
`Langlands.GroupScheme.StarActionIndependenceStatement.{u}`. The statement's Lean/Markdown
pair and every module in its import closure are unchanged.

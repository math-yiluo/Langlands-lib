# The degree-zero smooth Godement comparison map

Author: Worker 716. This module proves Worker 3's statement
`Langlands.Cohomology.SmoothGodementComparison.SmoothGodementComparisonZeroStatement` from the
module `Langlands.Cohomology.SmoothGodementComparison.Statement`. It imports that module and
Worker 61's published module `Langlands.Cohomology.AcyclicResolution.Comparison`. It adds no
definitions.

Composition `f ≫ g` is `f` followed by `g`. Write `Γc` for Worker 13's compact-sections functor
`Langlands.Sheaf.Equivariant.smoothSheafCompactSections R G X`, from smooth equivariant sheaves
to the abelian category `Langlands.SmoothRep R G` of smooth representations; `D` and `η` for
Worker 61's degree-zero smooth Godement functor `Godement.smoothZeroFunctor R G X` and its
coaugmentation `Godement.smoothCoaugmentation R G X : 𝟭 ⟶ D`; and
`ε := CokernelComplex.augmentationMap D η F` for the augmentation from `F`, placed in degree
zero, to the smooth Godement complex `K := Godement.smoothComplex R G X F`. Its degree-zero
component is `η.app F` (`CokernelComplex.augmentationMap_f_zero`).

## Theorem

`Langlands.Cohomology.SmoothGodementComparison.smoothGodementComparisonZero R G X :
SmoothGodementComparisonZeroStatement R G X`, with the single universe parameter `u` free and no
hypotheses beyond those of the statement. Spelled out:

Let `R` be a commutative ring, `G` a topological group (`Group G`, `TopologicalSpace G`,
`IsTopologicalGroup G`) and `X` a topological space, all three in one universe `u`, with
`MulAction G X`, `ContinuousConstSMul G X` and `HasStableNeighbourhoods G X`. No separation or
local compactness of `X` is assumed. Let `F : SmoothTopologicalSheaf R G X`, let `I` be an
injective resolution of `F` in the abelian category of smooth sheaves, and let
`φ : K ⟶ I.cocomplex` be a cochain map with `ε ≫ φ = I.ι`. Then

`comparisonMap R G X I φ 0 =
(SmoothGodementCohomology.smoothGodementCompactCohomologyZeroIso R G X).hom.app F ≫
(SmoothSheafCohomology.compactDerivedZeroIso R G X).inv.app F`.

Here `comparisonMap R G X I φ 0` is the map induced by `φ` on degree-zero homology of `Γc`
applied termwise, followed by the inverse of `compactDerivedIso R G X I 0`, Mathlib's
`I.isoRightDerivedObj Γc 0`. On the right, `smoothGodementCompactCohomologyZeroIso` identifies
the degree-zero homology of `Γc K` with `Γc F`, and `compactDerivedZeroIso` is Mathlib's
`Γc.rightDerivedZeroIsoSelf`, whose inverse has components `Γc.toRightDerivedZero.app F`. The
latter is Mathlib's form of the map `τ : T → R⁰T` induced by the augmentation of an injective
resolution, Cartan–Eilenberg, *Homological Algebra* (1956), Chapter V, §5, printed p.89, which is
an isomorphism for left exact `T` (their Proposition 5.1). So the theorem says that in degree
zero the comparison map is `τ` for `Γc`, transported along the identification of
`H⁰(Γc K)` with `Γc F`. The source correspondence of the statement (Berkovich's Corollary
1.5.2(i), case `q = 0`, and Harris 1999, (2.3)) is recorded in the statement's Markdown.

## Proof

The proof follows the route suggested in the task.

1. Worker 61's `AcyclicResolution.toRightDerivedZero_eq_comparison` applied to `Γc`, `ε`, `I`,
   `φ` and the hypothesis `ε ≫ φ = I.ι` gives

   `Γc.toRightDerivedZero.app F =
   AcyclicResolution.toCyclesZero Γc ε ≫ (Γc K).homologyπ 0 ≫ AcyclicResolution.comparison Γc I φ 0`.

   Here `toCyclesZero Γc ε : Γc F ⟶ (Γc K).cycles 0` is the lift of `Γc (ε.f 0)` to the
   degree-zero cycles, and `comparison Γc I φ 0` is by definition the same map as
   `comparisonMap R G X I φ 0`. This lemma needs neither a quasi-isomorphism hypothesis on `ε`
   nor left exactness of `Γc`. (It is proved from Mathlib's
   `InjectiveResolution.toRightDerivedZero_eq`, `toRightDerivedZero'_comp_iCycles` and
   `HomologicalComplex.homologyπ_naturality`.)
2. `toCyclesZero Γc ε` equals `(EquivariantGodementCohomology.cyclesIso D η Γc F).hom`, Worker
   13's identification of `Γc F` with the degree-zero cycles of `Γc K`. Both are maps into the
   cycles, so it suffices to compare them after the monomorphism
   `HomologicalComplex.iCycles _ 0` (`cancel_mono`). By `AcyclicResolution.toCyclesZero_iCycles`
   and `CokernelComplex.augmentationMap_f_zero` the first becomes `Γc.map (η.app F)`; by
   `EquivariantGodementCohomology.cyclesIso_hom_iCycles` the second becomes
   `Γc.map (CokernelComplex.augmentation D η F)`, and `CokernelComplex.augmentation D η F` is by
   definition `η.app F`.
3. By definition `smoothGodementCompactCohomologyZeroIso R G X` is
   `EquivariantGodementCohomology.homologyZeroIso D η Γc`, the inverse of the natural isomorphism
   with components `homologyIso D η Γc F = cyclesIso D η Γc F ≪≫ (Γc K).isoHomologyπ₀`, and the
   inverse of `compactDerivedZeroIso R G X` has components `Γc.toRightDerivedZero.app F`. A
   `change` therefore rewrites the goal as
   `comparisonMap R G X I φ 0 = (homologyIso D η Γc F).inv ≫ Γc.toRightDerivedZero.app F`.
   Rewriting with steps 1 and 2 and expanding `homologyIso` gives

   `comparisonMap R G X I φ 0 = (Γc K).isoHomologyπ₀.inv ≫ (cyclesIso D η Γc F).inv ≫
   (cyclesIso D η Γc F).hom ≫ (Γc K).homologyπ 0 ≫ comparisonMap R G X I φ 0`.

   `Iso.inv_hom_id_assoc` cancels the `cyclesIso` pair. Mathlib's `CochainComplex.isoHomologyπ₀`
   is `asIso` of `homologyπ 0`, so its hom is definitionally `homologyπ 0`, and a second
   `Iso.inv_hom_id_assoc`, read from right to left, cancels `isoHomologyπ₀.inv ≫ homologyπ 0` and
   closes the goal.

No property of `X` beyond the hypotheses of the statement, and no unproved statement, is used.
`lean_check` reports that the theorem depends only on the axioms `propext`, `Classical.choice`
and `Quot.sound`.

## Sources

- Cartan and Eilenberg, *Homological Algebra* (1956), registered as
  `provided-4e029ea5216cb6ce6bfc05060277910b86f223b69bc92c508711e3760612bd4e` (retained file
  `literature/Cartan-Eilenberg 1956 original- resolution comparison and derived functors.pdf`),
  Chapter V, §5, printed p.89 (PDF p.111): the augmentation of an injective resolution induces
  `τ : T → R⁰T`, and Proposition 5.1 says `τ` is a natural equivalence if and only if `T` is left
  exact. Used only to explain the right-hand side; the Lean proof uses Mathlib's
  `Functor.toRightDerivedZero`.

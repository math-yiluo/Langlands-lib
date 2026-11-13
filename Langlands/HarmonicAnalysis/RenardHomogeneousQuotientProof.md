# Renard II.3.9: quotient, compact-induction and module comparisons

Helper module for the proof of
`Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard.Statements`
(Worker 67, Task 5524). It proves the last three conjuncts:
`quotientTest : QuotientTestStatement`,
`compactInduction : CompactInductionStatement` and
`pointwiseModuleSheaf : PointwiseModuleSheafStatement`, each at the full
universe parameter `uG`. It also supplies topological facts about the twisted
spaces `space H χ` that the averaging module reuses.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
II.3.9 is on printed pp.48–50 / PDF pp.54–56; the Remark on printed p.50 /
PDF p.56 refers to the module-to-sheaf construction of II.2.4–II.2.5. The
source treats these comparisons as evident, so the arguments below are
internal deductions from the Library definitions.

## Cosets and supports

Throughout, `quotientMap H : G → H\G` is the published projection for the
right relation. The existing `Langlands.Induction.quotientMap_eq_iff`, imported
from `Langlands.Representation.Induction.OpenAdjunction`, says
`Hx = Hy ↔ y x⁻¹ ∈ H`. The
lemmas `quotientMap_mul_left`, `mem_mul_iff_quotientMap` and
`preimage_image_quotientMap` identify the saturation of a set `S` with
`H * S`.

Fix a positive character `χ : H →* ℝ≥0` and `f ∈ space H χ`. Each value
`χ h` is a unit, so covariance shows that the support of `f` is
`H`-saturated (`preimage_image_support`). The support is clopen because `f`
is locally constant. Hence its image in `H\G` is closed, since the quotient
map is a quotient map, and open, since it is an open map
(`isClosed_image_support`, `isOpen_image_support`). The image is contained in
the image of the compact set `K` from the support condition `supp f ⊆ H K`, so
it is compact (`isCompact_image_support`).

Under the standing hypotheses (Hausdorff, locally compact, totally
disconnected), `exists_compactOpenSubgroup` obtains a compact open subgroup
from the Library result `Hecke.TestFunction.commonCompactOpenBiInvariance`.
`exists_compact_lift` lifts a compact set `C ⊆ H\G` to a compact `K ⊆ G`
with `C ⊆ quotientMap H '' K`. It covers `C` by the open images of the
translates `g K₀` and takes the union of finitely many of them.
`compactModulo_of_image` turns compactness of the projected support into the
`CompactModulo` condition.

`exists_uniform_stabilizer` gives one compact open subgroup `K` with
`f(xk) = f(x)` for all `x` and all `k ∈ K`. The proof multiplies `f` by the
characteristic function of the compact open set `U = K_f K₀`. This gives a
test function on `G`, and `commonCompactOpenBiInvariance` supplies a right
stabilizer `K ⊆ K₀` for it. For `y ∈ K_f` both `y` and `yk` lie in `U`, so
`f(yk) = f(y)`. Covariance extends this equality to every point of the
support `H K_f`. A point outside the support whose right translate lies in
the support is ruled out by applying the same identity to `k⁻¹`.
`isLocallyConstant_of_stabilizer` turns such a uniform stabilizer into local
constancy.

## Conjunct 3: quotient tests

When `χ` is trivial, `pullbackTest` sends a test function `f` on `H\G` to
`x ↦ f(quotientMap H x)`. Local constancy is preserved by composition, and
the support condition follows from `exists_compact_lift` applied to the
compact support of `f`. `descendTest` goes the other way through the Library
map `QuotientIntegration.descend`. Its local constancy uses that the
projection is a quotient map. Its compact support uses
`isCompact_image_support` and `isClosed_image_support`. The two maps are
mutually inverse by evaluation on representatives. `quotientTestEquiv` is the
resulting linear equivalence, and `quotientTest` instantiates it with
`χ = relativeModular H hH`; the displayed pointwise formula holds by `rfl`.

## Conjunct 4: compact induction

For a unit-valued character `ψ` with the same values as `χ`, `toCompact`
packages `f` as an element of the published
`Induction.CompactFunctions H (characterRepresentation ψ)` through
`compactFunctionOf`. The equivariance comes from covariance, the open right
stabilizer from `exists_uniform_stabilizer`, and compact projected support
from `isCompact_image_support`. `ofCompact` reads a compactly induced function
back through `Induction.eval`. It is locally constant by its stabilizer, and
it lies in the twisted space by `compactModulo_of_image`. Both maps are the
identity on values, so `compactEquiv` is a linear equivalence whose
right-action compatibility holds definitionally (`compactEquiv_rightAction`).

`relativeCharacter` is the smooth character with values
`((relativeModular H hH h : ℝ) : ℂ)`. Its kernel is open because
`relativeModular` is locally constant. That follows from the local constancy
of Renard's modular characters of `G` and of the closed (hence locally
compact) subgroup `H`, both from `Distribution.RenardModular.regularity`.
`compactInduction` assembles these pieces.

## Conjunct 5: the pointwise module and its sheaf

`pointwiseSMul a f` multiplies `f` by the pullback `x ↦ a(quotientMap H x)` of
a pointwise test `a` on `H\G`. It preserves covariance because the pullback
is left `H`-invariant. It preserves the support condition because the support
can only shrink. `pointwiseModule` records the non-unital module axioms
pointwise. It is nondegenerate (`pointwise_nondegenerate`): `f` is fixed by
the characteristic idempotent of the compact open image of its support.
`action_eq_self_iff` shows that the projector of a compact open `U` fixes `f`
exactly when `supp f ⊆ quotientMap H ⁻¹' U`. Local profiniteness of `H\G` is
the Library result `Sheaf.Renard.HomogeneousSections.quotient_isLocallyProfinite`.
In `pointwiseModuleSheaf`, the pointwise formula and the restriction formula
of the published `ProjectorBasisSheaf.basisSheaf` both hold definitionally.

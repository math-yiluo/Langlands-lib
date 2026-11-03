# Geometry and scalar-extension helpers for finite Galois torus splitting

This module constructs an actual scalar-extension comparison and supplies
six complete internal helpers for the published
proposition `Langlands.GroupScheme.TorusFiniteGaloisSplittingStatement`.
It reuses the published smoothness theorem and proves finiteness descent for actual field tori,
scalar-extension comparisons, preservation under algebraic extension, and
enlargement of an existing finite separable splitting field to a finite
Galois splitting field. The existence of the initial finite separable
splitting field remains a separate obligation.

The imported `IsTorus.smooth` from [Geometry](Geometry.md) descends smoothness
from the supplied splitting field K/k.
The map Spec K → Spec k is flat and surjective because the field extension
is faithfully flat, and it is quasi-compact because both schemes are affine.
Mathlib's fpqc descent instance for smooth morphisms therefore applies to the
second projection of the base-change pullback, which is smooth by the
published `IsSplitTorus.smooth` theorem. In particular, local finite
presentation follows from smoothness. This uses the original arbitrary
splitting witness and imposes no finiteness or separability on K/k.

`IsTorus.quasiCompact` uses the same arbitrary field extension. Its base change
is affine by the published `IsSplitTorus.isAffineHom`, hence its underlying
space is compact. The first pullback projection onto the original torus is
surjective, because Spec K → Spec k is surjective. Its continuous image is
compact, which makes the structure morphism to the affine field spectrum
quasi-compact. `IsTorus.quasiSeparated` uses smoothness to obtain local finite
type over the Noetherian field spectrum. The torus is therefore locally
Noetherian and quasi-separated by Mathlib's existing theorem. These two
deductions supply the finiteness hypotheses for the later limit step without
assuming affine descent.

`baseChangeFieldTowerIso` constructs an isomorphism of actual group schemes
between the direct extension from k to K and the iterated extension through L.
It identifies the composite of the two morphisms of spectra with the morphism
from k → K, then applies the published `baseChangeCompIso`. The construction
applies to any compatible tower of commutative rings in the common universe,
and retains the full group structure.

`IsSplitTorus.baseChange_fieldTower_iff` transports splitting through this
isomorphism. `IsSplitTorus.baseChange_fieldTower` then transports a splitting
over L through the second base change. Their names retain “fieldTower” for
their intended use, although the hypotheses permit commutative rings.

`IsSplitTorus.exists_finiteGalois_of_finiteSeparable` starts with an actual group
scheme over Spec k and an actual splitting over a finite separable extension
L/k, all in an arbitrary common universe. It embeds L into `SeparableClosure k`
using `IsSepClosed.lift`, equips the closure with the corresponding L-algebra
structure, and takes `IntermediateField.normalClosure k L (SeparableClosure k)`.
Mathlib provides finiteness and Galoisness of this normal closure. The preceding
tower lemma propagates the splitting to it. No perfectness assumption is used,
and the argument applies without choosing a positive rank.

These helpers are internal consequences of the published base-change
comparisons and Mathlib's normal closure and separable closure results. The normal-closure helper supplies the final enlargement step for the
published target. No source proposition is transcribed here: these are
internal deductions from the imported Library and Mathlib results.
The affine descent, coalgebra spanning, and finite-presentation limit steps
remain separate obligations.

`IsTorus.baseChange_of_isAlgebraic` proves that being a torus persists after
an algebraic extension L/k. Given the original, possibly transcendental or
inseparable splitting witness K₀/k, use E = AlgebraicClosure K₀. Since L/k is
algebraic, it embeds as a k-algebra into E. The original split torus remains
split over E; the tower comparison identifies this with a splitting witness
for the base change to L. In particular this applies to SeparableClosure k.
This is an amalgamation argument, not a separability assertion about K₀.

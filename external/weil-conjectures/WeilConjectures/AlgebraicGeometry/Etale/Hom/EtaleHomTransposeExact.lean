/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomTransposeExactShiftData
import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomTransposeExactCommShift

/-! # Exactness of the evaluation-defined étale scalar Hom comparison

Source: Stacks Project, Cohomology on Sites, Tags 08JA and 08JC; blueprint
`lemma-change-coefficients-internal-hom--1`, proof paragraph 2.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The evaluation transpose commutes with the normalized reversed Hom shifts and
maps distinguished triangles to morphisms of distinguished triangles.
Source: Stacks 08JA and 08JC; blueprint lemma-change-coefficients-internal-hom--1, proof paragraph 2
(blueprint: lem-coef-etale-hom-transpose-exact).

Proof: compute derived Hom using a K-injective replacement of M and K-flat
flat-term representatives of the source. The ordinary Hom complex has differential
postcomposition minus signed precomposition. Source reindexing by -n, with the
factor (-1)^(n*j+n*(n+1)/2) in Hom degree j, is a chain isomorphism. Transposition
against evaluation gives exactly EtaleHomShiftNormalization. The quadratic factor
satisfies epsilon(a+b)=(-1)^(a*b)epsilon(a)epsilon(b); the extra factor cancels the
interchange of the two tensor shifts. Thus the reindexings are a coherent CommShift.
Hom takes a cone in the source to the reversed cone, including the negative
connecting projection, so these same shifts make the contravariant Hom functors
triangulated. Scalar extension preserves cones on K-flat models. Its shift is the
mate of the exact restriction shift, since both satisfy the scalar-adjunction
counit equation. Compose these structures to obtain precisely chiPhi and chiPsi
in the conclusion. Finally transpose the shift square for v: the assumed equation
for v turns its two sides into evaluation after scalar balancing. The normalized
binary tensor comparison identifies these maps on flat-term K-flat models.
For this application also replace the Hom complex by a flat-term K-flat Q and
compose Q to Hom(P,I) with evaluation; flatness of the Hom complex itself is
not assumed. The counit equation identifies this composite with the published
evaluation map after localization. Degree-zero scalar coefficients introduce
no further sign. The tensor-Hom
bijection gives the shift square itself. Localization and naturality extend all
these identities from representatives to every object and every distinguished
triangle. No flatness of B over A or boundedness of M is used. -/
theorem etaleHomComparison_reversedExact
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M)
    (hv : IsEtaleHomTranspose X φ M v) : IsEtaleHomReversedExact X φ M v  := by
  let _ := etaleHomScalarCommShift X φ
  obtain ⟨sA, sB, chiPhi, chiPsi, hA, hB, hPhi, hPsi, hTriA, hTriB⟩ :=
    etaleHomComparison_reversedExact_shiftData X φ M
  have hComm := etaleHomComparison_reversedExact_commShift X φ M v hv sA sB
    chiPhi chiPsi hA hB hPhi hPsi
  exact ⟨sA, sB, chiPhi, chiPsi, hA, hB, hPhi, hPsi, hTriA, hTriB, hComm⟩

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonEvaluationIsIso

/-! # Invertibility of the restricted derived-Hom evaluation map

Source: Stacks Project, Tags 03Q8, 072W, 0BKV and 0D6F.
(blueprint: lem-sbc-raw-restricted-cohomology-comparison-is-iso).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Evaluation at the represented identity induces an isomorphism in every degree.
Source: Stacks Project, Tag 03Q8 and Cohomology on Sites, Tags 072W, 0BKV and 0D6F.
(blueprint: lem-sbc-raw-restricted-cohomology-comparison-is-iso).

Proof: Put V = U times_S Y and r : V -> Y. The free abelian Yoneda and
sheafification adjunctions, followed by h^* adjoint to h_*, identify maps from
h^* of the free represented sheaf of U to any sheaf G with G(V). The identity
under this identification is exactly the section called generator in the map
construction. Restriction r^* preserves injectives: its left adjoint r_! is exact,
since stalks are direct sums over lifts and geometric stalks detect exactness.
Take a bounded-below injective resolution I of F. Maps from the single free
sheaf to I[p], modulo homotopy, are the p-th cohomology of the complex of sections
I(V), by the preceding additive sections adjunction. Restriction computes the
same complex on V and remains K-injective. The localization bijection for a
K-injective target and full faithfulness of D+ into D identify these homotopy
classes with the raw derived Hom source. The comparison map applies restricted
derived sections to the class and evaluates at generator; on I this sends a
class represented by a chain map to its corresponding section cocycle, so it
is the above bijection. The zeroIso and shiftIso factors are precisely the
single-complex and shift identifications in this computation. Thus the map is
an additive bijection, hence an isomorphism. For p=0 the argument is the ordinary
sections adjunction. For empty V both the sections complex and the raw Hom
complex vanish; the same computation applies without a nonemptiness assumption. -/
theorem isIso_rawRestrictedCohomologyComparison {S Y : Scheme.{v}} (h : Y ⟶ S)
    (p : ℕ) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) (U : S.Etale) :
    IsIso (rawRestrictedCohomologyComparison h p F U) := by
  let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let A := (upperStar AddCommGrpCat.{v + 1} h).obj
    (RawRestrictedComparison.freeSheaf S U)
  let x := (RawRestrictedComparison.zeroIso W A).inv
    (RawRestrictedComparison.generator h U)
  let T := RawRestrictedComparison.sectionsFunctor W ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
  have he : IsIso (RawRestrictedComparison.Evaluation.evaluate T x) :=
    isIso_rawRestrictedCohomologyComparisonEvaluation h p F U
  dsimp [rawRestrictedCohomologyComparison, W, A, x, T]
  infer_instance

end AlgebraicGeometry.Etale

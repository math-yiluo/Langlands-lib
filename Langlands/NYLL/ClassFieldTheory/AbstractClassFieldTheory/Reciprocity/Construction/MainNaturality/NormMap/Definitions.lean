/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.U012.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.GroupOnly.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.U015.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.RelativeNorm.U019.Proofs

/-!
# NYLL norm map on finite norm quotients

Modified by Worker 196, 16 November 2026: extract M066.014 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, expand `extensionSubgroup` to `Subgroup.subgroupOf`, and
refer to the published source-private tower-finiteness proof as
`Langlands.NYLL.PortInternal.M066.d013`. All data, binders, local instances
and proof steps in the definition are retained. The focused imports supply
published prerequisites. See the paired Markdown and `licenses/NYLL/`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

-- The source chooses a universe-zero group through IntegralRepGroupType.
-- The representation's module universe remains arbitrary.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The right vertical map in the first diagram of norm--conjugation naturality.  It is
the actual norm `N_{K'/K}`, descended to the actual finite norm quotients. -/
def finiteReciprocityNaturalityNormMap
    (A : Rep ℤ G) (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLKfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    [hL'K'finite : Finite
      (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup)]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup)] :
    FiniteNormQuotient A K' L' hL'K' →+
      FiniteNormQuotient A K L hLK := by
  letI hL'Kfinite : Finite (K.toSubgroup ⧸
      L'.toSubgroup.subgroupOf K.toSubgroup) :=
    Langlands.NYLL.PortInternal.M066.d013 K K' L' hK'K hL'K'
  letI hL'Lfinite : Finite
      (L.toSubgroup ⧸ L'.toSubgroup.subgroupOf L.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le
      (hL'L.trans hLK) hLK hL'L
  let f : ambientFixedAddSubgroup A K' →+ FiniteNormQuotient A K L hLK :=
    (finiteNormClassHom A K L hLK).comp (relativeNorm A K K' hK'K)
  apply finiteNormQuotientLift A K' L' hL'K' f
  rintro _ ⟨a, rfl⟩
  let TLL' : DegreeData.FiniteTower G :=
    { top := L'
      middle := L
      base := K
      top_le_middle := hL'L
      middle_le_base := hLK
      finiteTopQuotient := hL'Lfinite
      finiteBaseQuotient := hLKfinite }
  let TKK' : DegreeData.FiniteTower G :=
    { top := L'
      middle := K'
      base := K
      top_le_middle := hL'K'
      middle_le_base := hK'K
      finiteTopQuotient := hL'K'finite
      finiteBaseQuotient := hK'Kfinite }
  apply (finiteNormClass_eq_zero_iff A K L hLK _).2
  refine ⟨relativeNorm A L L' hL'L a, ?_⟩
  calc
    relativeNorm A K L hLK (relativeNorm A L L' hL'L a) =
        relativeNorm A K L' (hL'L.trans hLK) a :=
      TLL'.norm_trans_apply A a
    _ = relativeNorm A K L' (hL'K'.trans hK'K) a := by
      congr 2
    _ = relativeNorm A K K' hK'K (relativeNorm A K' L' hL'K' a) :=
      (TKK'.norm_trans_apply A a).symm

end
end Langlands.NYLL.ClassFormation

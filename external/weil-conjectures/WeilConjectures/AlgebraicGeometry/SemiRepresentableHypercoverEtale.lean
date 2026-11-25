/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject
import WeilConjectures.AlgebraicGeometry.SRMatchingObjectOneMember
import WeilConjectures.AlgebraicGeometry.EtaleSimplicialMatching

/-! Conversion of the semi-representable hypercover condition to the scheme form. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A semi-representable hypercover in the singleton étale family has the ordinary
scheme matching-object hypercover property.  The proof compares the singleton
matching object with the proper-face matching limit in each degree, extends a
compatible proper-face family along epi-mono factorization, and transports the
covering condition across the resulting isomorphism.
Source: Stacks Project, Hypercoverings, Tags 01G2, 01G3, 01G5.
(auxiliary; not a blueprint node) -/
theorem semiRepresentableHypercover_isEtaleHypercover
    {X : Scheme.{u}}
    (K : SimplicialObject X.Etale)
    (hK : X.IsSemiRepresentableHypercover
      (K ⋙ FormalCoproduct.incl.{u} X.Etale)) :
    IsEtaleHypercover K := by
  classical
  obtain ⟨M, π, μ, _, hlim, hμ, _, _, heq⟩ := sr_matching_object_one_member.{u} X K
  apply EtaleSimplicialMatching.isEtaleHypercover_of_matchingCover
  intro n
  let c : Cone (K.properFaceDiagram n) := Cone.mk (M n) (π n)
  let hc : IsLimit c := isLimitOfReflects (Etale.forget X) (hlim n).some
  let e : M n ≅ EtaleSimplicialMatching.matching K n :=
    hc.conePointUniqueUpToIso (EtaleSimplicialMatching.properConeIsLimit K n)
  have hm : μ n ≫ e.hom = EtaleSimplicialMatching.matchingMap K n := by
    apply (EtaleSimplicialMatching.properConeIsLimit K n).hom_ext
    intro a
    change (μ n ≫ e.hom) ≫ EtaleSimplicialMatching.projection K n _ _ a.unop.obj.hom =
      EtaleSimplicialMatching.matchingMap K n ≫
        EtaleSimplicialMatching.projection K n _ _ a.unop.obj.hom
    rw [Category.assoc,
      show e.hom ≫ EtaleSimplicialMatching.projection K n _ _ a.unop.obj.hom =
        (π n).app a from hc.conePointUniqueUpToIso_hom_comp
          (EtaleSimplicialMatching.properConeIsLimit K n) a,
      hμ, EtaleSimplicialMatching.matchingMap_projection]
  let _ : Surjective (μ n).left := ((heq.mp hK) n).2
  let _ : IsIso e.hom.left := inferInstanceAs
    (IsIso ((Etale.forget X ⋙ Over.forget X).map e.hom))
  rw [← hm]
  change Surjective ((μ n).left ≫ e.hom.left)
  infer_instance

end AlgebraicGeometry.Scheme

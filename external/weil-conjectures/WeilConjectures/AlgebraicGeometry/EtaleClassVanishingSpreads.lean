/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyLocalRingColimit
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap

/-! # Spreading vanishing from the local scheme

Source: Stacks Project, Tags 09AX, 03Q6, 09YQ and 03F3.
(blueprint: lem-weil-pbc-etale-class-vanishing-spreads) -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- A class which dies over the local scheme dies on some Zariski neighborhood.

Source: Stacks Project, Etale Cohomology, Lemma 09AX, proof, using continuity
(Tags 03Q6 and 09YQ) and Cohomology on Sites, Tag 03F3.
(blueprint: lem-weil-pbc-etale-class-vanishing-spreads)

Proof: Present the object cohomology presheaf on the small etale site by Ext
from the sheafified free abelian presheaves on representables. Restrict it to
open neighborhoods of x. The local-ring colimit theorem identifies its value
on each open with cohomology of the restricted sheaf, compatibly with pullback
and inverse-image composition. Its colimit is cohomology over Spec O_X,x, with
legs given by the canonical pullbacks. Represent the given global class at the
top neighborhood. Its colimit image is zero by the hypothesis. The elementwise
filtered-colimit criterion supplies a smaller neighborhood where its restriction
is zero. The comparison identifies this restriction with pullback along the
open immersion, followed by an isomorphism of coefficient sheaves. That induced
map on cohomology is injective, so the untransported pullback is zero as well.
No positive-degree or henselian hypothesis is used in this continuity step. -/
theorem etale_class_vanishing_spreads {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (ξ : Sheaf.H F q) (x : X)
    (hξ : cohomologyMap (X.fromSpecStalk x) F q ξ = 0) :
    ∃ U : X.Opens, x ∈ U ∧ cohomologyMap U.ι F q ξ = 0 := by
  let i : X.Opens ⥤ X.Etale := MorphismProperty.Comma.lift X.restrictFunctor
    (fun U ↦ (inferInstance : Etale U.ι)) (fun _ ↦ trivial) (fun _ ↦ trivial)
  let P := (Functor.flip ((uliftYoneda.{u + 1} ⋙
    (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).op ⋙
      Abelian.extFunctor q)).obj F
  let D := (OpenNhds.inclusion x ⋙ i).op ⋙ P
  obtain ⟨e, he, g, hg, _, B, b, hb, _, hzero⟩ :=
    etaleCohomology_localRing_colimit F x q P rfl D
      (fun U ↦ Iso.refl _) (by intro U V f; simp only [D, Functor.comp_map, Functor.op_map,
        Iso.refl_hom, Category.id_comp]; rfl)
  let T : OpenNhds (X := X.toLocallyRingedSpace.toTopCat) x := ⟨⊤, trivial⟩
  let η := (e ⊤).inv (cohomologyMap (⊤ : X.Opens).ι F q ξ)
  have hη : (B.ι.app (op T) ≫ b.hom) η = 0 := by
    rw [hb T]
    change Sheaf.H.map _ q
      (cohomologyMap (g T) _ q ((e ⊤).hom η)) = 0
    have heη : (e ⊤).hom η = cohomologyMap (⊤ : X.Opens).ι F q ξ := by
      exact ConcreteCategory.congr_hom (e ⊤).inv_hom_id
        (cohomologyMap (⊤ : X.Opens).ι F q ξ)
    rw [heη]
    have hc := (Etale.cohomologyPullbackFunctorial (g T) (⊤ : X.Opens).ι F q).2.1 ξ
    have hz : cohomologyMap (g T ≫ (⊤ : X.Opens).ι) F q ξ = 0 := by
      exact (congrArg (fun k ↦ cohomologyMap k F q ξ = 0) (hg T)).mp hξ
    rw [hz, map_zero] at hc
    rw [hc, map_zero]
  obtain ⟨V, f, hf⟩ := hzero T η hη
  have hr := ConcreteCategory.congr_hom (he ⊤ V.1 f.le) η
  change (e V.1).hom (D.map f.op η) = _ at hr
  rw [hf, map_zero] at hr
  have heη : (e ⊤).hom η = cohomologyMap (⊤ : X.Opens).ι F q ξ := by
    exact ConcreteCategory.congr_hom (e ⊤).inv_hom_id
        (cohomologyMap (⊤ : X.Opens).ι F q ξ)
  change 0 = Sheaf.H.map _ q
    (cohomologyMap (X.homOfLE f.le) _ q ((e ⊤).hom η)) at hr
  rw [heη] at hr
  have hz := (Etale.injective_sheafHMap_of_isIso _ q)
    (hr.symm.trans (map_zero _).symm)
  have hc := (Etale.cohomologyPullbackFunctorial
    (X.homOfLE f.le) (⊤ : X.Opens).ι F q).2.1 ξ
  rw [hz] at hc
  have hz' := (Etale.injective_sheafHMap_of_isIso _ q)
    (hc.symm.trans (map_zero _).symm)
  refine ⟨V.1, V.2, ?_⟩
  exact (congrArg (fun k ↦ cohomologyMap k F q ξ = 0)
    (X.homOfLE_ι f.le)).mp hz' 

end AlgebraicGeometry.Etale

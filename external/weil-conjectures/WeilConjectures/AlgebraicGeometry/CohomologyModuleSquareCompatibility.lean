/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

/-!
# Forgetting module coefficients in a commuting inverse-image square

Source: Stacks Project, Tags 03FD and 095T, the coefficient comparison and
the functorial restriction-map calculation, respectively.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

private theorem square_iso_cancel {C D E : Type*} [Category C] [Category D]
    [Category E] (T : C ⥤ E) (S : D ⥤ E) {V W : D} {X Y : C} {Z : E}
    (α : V ≅ W) (β : X ≅ Y) (e₁ : Z ≅ T.obj Y) (e₂ : Z ≅ S.obj W) :
    e₁.hom ≫ T.map β.inv ≫
        (T.mapIso β ≪≫ e₁.symm ≪≫ e₂ ≪≫ S.mapIso α.symm).hom =
      e₂.hom ≫ S.map α.inv := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.inv_hom_id_map_assoc, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Coefficient-forgetting isomorphisms respect a commuting cohomology square.

Source: Stacks Project, proof of Tag 095T, the final map-on-stalks calculation,
and Tag 03FD for the underlying abelian cohomology convention.
(blueprint: lem-weil-pbc-cohomology-module-square-compatibility)

Proof: use pullback_forget_modules_iso to choose alpha:
(i^* F)_ab -> i^* F_ab and beta: (g^* F)_ab -> g^* F_ab.
Let e1 be the inverse-image composition isomorphism for j,g and e2
that for k,i with common composite j >> g. Define gamma by
j^* beta, e1 inverse, e2, then k^* alpha inverse.
Applying Sheaf.functorH to alpha inverse, beta inverse, and gamma
produces c₁, c₂, c₃. These are additive equivalences because the
cohomology functor preserves isomorphisms. Naturality of cohomologyMap
moves beta inverse and alpha inverse past the respective pullbacks.
Its composition law expresses the two successive pullbacks using e1
after H(j >> g) and e2 after that same map, respectively.
Compose the cohomology morphisms. The factors j^* beta inverse and
j^* beta cancel, as do e1 and e1 inverse. Both sides are therefore
H(e2 followed by k^* alpha inverse) applied to H(j >> g)(x).
This proves the equation without requiring coherent choices of alpha
and beta: gamma was defined to incorporate the chosen comparisons.
There are no bijectivity, properness, torsion, or cartesianness assumptions;
the assertion holds for q = 0 and for empty schemes or zero coefficients. -/
theorem Etale.exists_addEquiv_cohomology_moduleSquare
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' X₀ X₀' : Scheme.{u}} (g : X' ⟶ X) (i : X₀ ⟶ X)
    (j : X₀' ⟶ X') (k : X₀' ⟶ X₀) (h : j ≫ g = k ≫ i)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    ∃ (c₁ : Sheaf.H ((i)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) q ≃+
        Sheaf.H
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} Λ].obj F)) q)
      (c₂ : Sheaf.H ((g)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) q ≃+
        Sheaf.H
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((g)^*[ModuleCat.{u + 1} Λ].obj F)) q)
      (c₃ : Sheaf.H ((j)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((g)^*[ModuleCat.{u + 1} Λ].obj F))) q ≃+
        Sheaf.H ((k)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} Λ].obj F))) q),
      ∀ x, c₃ (Etale.cohomologyMap j
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((g)^*[ModuleCat.{u + 1} Λ].obj F)) q
          (c₂ (Etale.cohomologyMap g
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
            q x))) =
        Etale.cohomologyMap k
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} Λ].obj F)) q
          (c₁ (Etale.cohomologyMap i
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
            q x)) := by
  obtain ⟨α⟩ := Etale.pullback_forget_modules_iso Λ i F
  obtain ⟨β⟩ := Etale.pullback_forget_modules_iso Λ g F
  let G := (sheafCompose _
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  let e₁ := (Etale.upperStarComp AddCommGrpCat.{u + 1} j g).app G
  let e₂ := (Etale.upperStarComp AddCommGrpCat.{u + 1} k i (j ≫ g) h).app G
  let γ := ((j)^*[AddCommGrpCat.{u + 1}]).mapIso β ≪≫ e₁.symm ≪≫ e₂ ≪≫
    ((k)^*[AddCommGrpCat.{u + 1}]).mapIso α.symm
  have hα : Function.Bijective (Sheaf.H.map α.inv q) :=
    ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ q).map α.inv)
  have hβ : Function.Bijective (Sheaf.H.map β.inv q) :=
    ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ q).map β.inv)
  have hγ : Function.Bijective (Sheaf.H.map γ.hom q) :=
    ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ q).map γ.hom)
  refine ⟨AddEquiv.ofBijective (Sheaf.H.map α.inv q) hα,
    AddEquiv.ofBijective (Sheaf.H.map β.inv q) hβ,
    AddEquiv.ofBijective (Sheaf.H.map γ.hom q) hγ, ?_⟩
  intro x
  change Sheaf.H.map γ.hom q
      (Etale.cohomologyMap j _ q (Sheaf.H.map β.inv q (Etale.cohomologyMap g G q x))) =
    Etale.cohomologyMap k _ q (Sheaf.H.map α.inv q (Etale.cohomologyMap i G q x))
  rw [Etale.cohomologyMap_map, Etale.cohomologyMap_map]
  rw [(Etale.cohomologyPullbackFunctorial j g G q).2.1]
  have hk := (Etale.cohomologyPullbackFunctorial k i G q).2.1 x
  have hk' : Etale.cohomologyMap k _ q (Etale.cohomologyMap i G q x) =
      Sheaf.H.map e₂.hom q (Etale.cohomologyMap (j ≫ g) G q x) := by
    have aux (l : X₀' ⟶ X) (hl : l = k ≫ i) :
        Etale.cohomologyMap k _ q (Etale.cohomologyMap i G q x) =
          Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} k i l hl).hom.app G)
            q (Etale.cohomologyMap l G q x) := by
      subst l
      exact hk
    exact aux (j ≫ g) h
  rw [hk']
  change Sheaf.H.map γ.hom q
      (Sheaf.H.map (((j)^*[AddCommGrpCat.{u + 1}]).map β.inv) q
        (Sheaf.H.map e₁.hom q (Etale.cohomologyMap (j ≫ g) G q x))) =
    Sheaf.H.map (((k)^*[AddCommGrpCat.{u + 1}]).map α.inv) q
      (Sheaf.H.map e₂.hom q (Etale.cohomologyMap (j ≫ g) G q x))
  simp only [← Sheaf.H.map_comp_apply]
  have he : e₁.hom ≫ ((j)^*[AddCommGrpCat.{u + 1}]).map β.inv ≫ γ.hom =
      e₂.hom ≫ ((k)^*[AddCommGrpCat.{u + 1}]).map α.inv := by
    exact square_iso_cancel ((j)^*[AddCommGrpCat.{u + 1}])
      ((k)^*[AddCommGrpCat.{u + 1}]) α β e₁ e₂
  calc
    _ = Sheaf.H.map (e₁.hom ≫
        (((j)^*[AddCommGrpCat.{u + 1}]).map β.inv ≫ γ.hom)) q
        (Etale.cohomologyMap (j ≫ g) G q x) :=
      (Sheaf.H.map_comp_apply e₁.hom
        (((j)^*[AddCommGrpCat.{u + 1}]).map β.inv ≫ γ.hom) _).symm
    _ = Sheaf.H.map (e₂.hom ≫ ((k)^*[AddCommGrpCat.{u + 1}]).map α.inv) q
        (Etale.cohomologyMap (j ≫ g) G q x) := by rw [he]
    _ = _ := Sheaf.H.map_comp_apply e₂.hom
      (((k)^*[AddCommGrpCat.{u + 1}]).map α.inv) _

end AlgebraicGeometry

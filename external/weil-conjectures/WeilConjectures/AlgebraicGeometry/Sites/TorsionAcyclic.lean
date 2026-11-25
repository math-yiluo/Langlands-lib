/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Acyclic envelopes of étale sheaves killed by an integer

Let `n ≠ 0`. Every abelian étale sheaf `G` on a scheme `X` with `n • 𝟙 G = 0` embeds into an
abelian sheaf `J` with `n • 𝟙 J = 0` which has no cohomology in positive degrees, and which stays
acyclic after pushforward along any morphism and after restriction along any étale morphism:
take for `J` the `n`-torsion subsheaf `I[n]` of an injective sheaf `I ⊇ G`. Pushforward and étale
restriction preserve injective sheaves and commute with taking `n`-torsion, and the `n`-torsion
of an injective sheaf is acyclic (`CategoryTheory.Sheaf.subsingleton_H_kernel_nsmul_of_injective`).
This allows dimension shifting within sheaves killed by `n`.

## Main statements

- `AlgebraicGeometry.Etale.injective_upperStar_obj_of_etale_addCommGrp`: restriction along an
  étale morphism preserves injective abelian sheaves.
- `AlgebraicGeometry.Etale.exists_mono_acyclic_of_nsmul_eq_zero`: the acyclic envelope.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Etale

variable {W X : Scheme.{u}}

/-- **Étale restriction preserves injective abelian sheaves**: for an étale `v : W ⟶ X`, the
pullback `v^*` has the exact left adjoint `v_!` (the extension by zero, left Kan extension along
the localization functor followed by sheafification). -/
theorem injective_upperStar_obj_of_etale_addCommGrp (v : W ⟶ X) [AlgebraicGeometry.Etale v]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] :
    Injective ((v)^*[AddCommGrpCat.{u + 1}].obj I) := by
  have h : AlgebraicGeometry.Etale v := inferInstance
  have : (MorphismProperty.Over.map ⊤ h).IsContinuous W.smallEtaleTopology
      X.smallEtaleTopology :=
    inferInstanceAs ((MorphismProperty.Over.map ⊤ h).IsContinuous
      (W.smallGrothendieckTopology @AlgebraicGeometry.Etale)
      (X.smallGrothendieckTopology @AlgebraicGeometry.Etale))
  let adj := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.map ⊤ h) AddCommGrpCat.{u + 1} W.smallEtaleTopology
      X.smallEtaleTopology).ofNatIsoRight
      (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} v h).symm
  have : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.map ⊤ h) AddCommGrpCat.{u + 1} W.smallEtaleTopology
        X.smallEtaleTopology) := by
    have heq : Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.map ⊤ h)
        AddCommGrpCat.{u + 1} W.smallEtaleTopology X.smallEtaleTopology =
        sheafToPresheaf W.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          (MorphismProperty.Over.map ⊤ h).op.lan ⋙
            presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      rfl
    have : PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ h).op.lan :
        (W.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
      SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian _ h
    rw [heq]
    exact comp_preservesFiniteLimits _ _
  exact adj.map_injective I inferInstance

variable (X) in
/-- **Acyclic envelopes of sheaves killed by `n`.** Let `n ≠ 0` and `G` an abelian étale sheaf on
`X` with `n • 𝟙 G = 0`. Then `G` embeds into a sheaf `J` with `n • 𝟙 J = 0` such that `J`, its
pushforward along any morphism `j : X ⟶ Y` and its restriction along any étale `w : W ⟶ X` have
no cohomology in positive degrees: `J` is the `n`-torsion `I[n]` of an injective sheaf `I ⊇ G`. -/
theorem exists_mono_acyclic_of_nsmul_eq_zero {n : ℕ} (hn : n ≠ 0)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : n • 𝟙 G = 0) :
    ∃ (J : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (ι : G ⟶ J), Mono ι ∧
      n • 𝟙 J = 0 ∧ (∀ q, Subsingleton (Sheaf.H J (q + 1))) ∧
      (∀ {Y : Scheme.{u}} (j : X ⟶ Y) q,
        Subsingleton (Sheaf.H ((j)_*[AddCommGrpCat.{u + 1}].obj J) (q + 1))) ∧
      (∀ {W : Scheme.{u}} (w : W ⟶ X) [AlgebraicGeometry.Etale w] q,
        Subsingleton (Sheaf.H ((w)^*[AddCommGrpCat.{u + 1}].obj J) (q + 1))) := by
  let I := Injective.under G
  let J := kernel (n • 𝟙 I)
  have hι : Injective.ι G ≫ (n • 𝟙 I) = 0 := by
    rw [Preadditive.comp_nsmul, Category.comp_id, ← Category.id_comp (Injective.ι G),
      ← Preadditive.nsmul_comp, hG, zero_comp]
  refine ⟨J, kernel.lift _ (Injective.ι G) hι, ?_, ?_, ?_, fun {Y} j q ↦ ?_, fun {W} w _ q ↦ ?_⟩
  · exact mono_of_mono_fac (kernel.lift_ι _ _ hι)
  · rw [← cancel_mono (kernel.ι (n • 𝟙 I)), Preadditive.nsmul_comp, Category.id_comp,
      zero_comp, ← Category.comp_id (kernel.ι _), ← Preadditive.comp_nsmul, kernel.condition]
  · exact fun q ↦ Sheaf.subsingleton_H_kernel_nsmul_of_injective.{_, u + 1, u, u + 1} I hn q
  · let P := (j)_*[AddCommGrpCat.{u + 1}]
    have : Injective (P.obj I) :=
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).map_injective I inferInstance
    have e : P.obj J ≅ kernel (n • 𝟙 (P.obj I)) :=
      PreservesKernel.iso P (n • 𝟙 I) ≪≫ kernel.mapIso _ _ (Iso.refl _) (Iso.refl _)
        (by simp)
    have : Subsingleton ((Sheaf.functorH _ (q + 1)).obj (kernel (n • 𝟙 (P.obj I)))) :=
      Sheaf.subsingleton_H_kernel_nsmul_of_injective.{_, u + 1, u, u + 1} (P.obj I) hn q
    exact ((Sheaf.functorH _ (q + 1)).mapIso e).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  · let P := (w)^*[AddCommGrpCat.{u + 1}]
    have : Injective (P.obj I) := injective_upperStar_obj_of_etale_addCommGrp w I
    have e : P.obj J ≅ kernel (n • 𝟙 (P.obj I)) :=
      PreservesKernel.iso P (n • 𝟙 I) ≪≫ kernel.mapIso _ _ (Iso.refl _) (Iso.refl _)
        (by simp)
    have : Subsingleton ((Sheaf.functorH _ (q + 1)).obj (kernel (n • 𝟙 (P.obj I)))) :=
      Sheaf.subsingleton_H_kernel_nsmul_of_injective.{_, u + 1, u, u + 1} (P.obj I) hn q
    exact ((Sheaf.functorH _ (q + 1)).mapIso e).addCommGroupIsoToAddEquiv.toEquiv.subsingleton

open Opposite in
/-- **Lifting sections along an epimorphism.** Let `0 → S.X₁ → S.X₂ → S.X₃ → 0` be a short exact
sequence of abelian étale sheaves on `X` and `W` an étale `X`-scheme such that the restriction of
`S.X₁` to `W` has no `H¹`. Then every section of `S.X₃` over `W` lifts to `S.X₂`: on the small
étale site of `W` this is the long exact cohomology sequence in degree zero. -/
theorem surjective_app_of_subsingleton_H_one
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (W : X.Etale) [Subsingleton (Sheaf.H ((W.hom)^*[AddCommGrpCat.{u + 1}].obj S.X₁) 1)] :
    Function.Surjective (S.g.hom.app (op W)) := by
  have h : AlgebraicGeometry.Etale W.hom := W.prop
  let P := (W.hom)^*[AddCommGrpCat.{u + 1}]
  have hS' := hS.map_of_exact P
  have hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale W.left
  -- surjectivity over the terminal object of the small étale site of `W`
  have h₁ : Function.Surjective ((P.map S.g).hom.app (op (MorphismProperty.Over.mk ⊤
      (𝟙 W.left) (MorphismProperty.ContainsIdentities.id_mem _)))) := by
    intro y
    have : y ∈ ((S.map P).g.hom.app (op _)).hom.range := by
      rw [← Sheaf.H.ker_δ hS' hT, AddMonoidHom.mem_ker]
      exact Subsingleton.elim (h := (inferInstance :
        Subsingleton (Sheaf.H ((W.hom)^*[AddCommGrpCat.{u + 1}].obj S.X₁) 1))) _ _
    exact this
  -- transport along `W.hom^* ≅ localizationRestriction` and the isomorphism of objects
  let e := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.hom h
  let O := (MorphismProperty.Over.map ⊤ h).obj (MorphismProperty.Over.mk ⊤ (𝟙 W.left)
    (MorphismProperty.ContainsIdentities.id_mem _))
  have h₂ : Function.Surjective (S.g.hom.app (op O)) := by
    intro y
    obtain ⟨x, hx⟩ := h₁ ((e.inv.app S.X₃).hom.app (op _) y)
    refine ⟨(e.hom.app S.X₂).hom.app (op _) x, ?_⟩
    have := congrArg (fun φ ↦ φ.hom.app (op (MorphismProperty.Over.mk ⊤ (𝟙 W.left)
      (MorphismProperty.ContainsIdentities.id_mem _)))) (e.hom.naturality S.g)
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, NatTrans.comp_app] at this
    have h' := congrArg (fun f ↦ f x) (congrArg ConcreteCategory.hom this)
    simp only [ConcreteCategory.comp_apply] at h'
    rw [Etale.localizationRestriction_map_hom_app] at h'
    erw [← h', hx]
    change ((e.inv ≫ e.hom).app S.X₃).hom.app _ y = y
    rw [e.inv_hom_id]
    rfl
  let i : O ≅ W := MorphismProperty.Over.isoMk (Iso.refl _)
    (by
      simp only [Functor.const_obj_obj, Iso.refl_hom, Category.id_comp]
      exact (Category.id_comp _).symm)
  intro y
  obtain ⟨x, hx⟩ := h₂ (S.X₃.obj.map i.hom.op y)
  refine ⟨S.X₂.obj.map i.inv.op x, ?_⟩
  rw [NatTrans.naturality_apply, hx, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, i.inv_hom_id, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

end Etale

end AlgebraicGeometry

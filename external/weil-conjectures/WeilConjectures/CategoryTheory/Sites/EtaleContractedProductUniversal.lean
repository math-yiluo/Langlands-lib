/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.EtaleContractedProductData

/-! # Universal property of the sheafified orbit quotient -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

/-- Invariant natural maps factor uniquely through the actual sheafified orbit quotient.
Source: Stacks Project, Tags 03AH and 03AJ, contracted-product quotient construction;
the set quotient universal property and the sheafification adjunction.
(blueprint: lem-sc-etale-contracted-product-exists-universal)

Proof: Invariance makes the function on pairs constant on every generating relation,
so Quot.lift defines its map on orbit sections. Naturality on representatives gives a
presheaf morphism by quotient induction. Apply sheafifyLift to that morphism into F;
the unit equation proves the required values on every pair. For uniqueness, those values
determine the composite with the sheafification unit by quotient induction. The
sheafification hom-ext theorem then makes the two sheaf morphisms equal. -/
theorem contracted_product_universal (S : Scheme.{u})
    {G G' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : G ⟶ G') (T : Torsor G)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (a : ∀ U : S.Etaleᵒᵖ, T.sheaf.obj.obj U → G'.obj.obj U → F.obj.obj U)
    (hn : ∀ ⦃U V : S.Etaleᵒᵖ⦄ (f : U ⟶ V) t h,
      F.obj.map f (a U t h) = a V (T.sheaf.obj.map f t) (G'.obj.map f h))
    (hi : ∀ U g t h, a U (T.vadd U g t) (h - φ.hom.app U g) = a U t h) :
    ∃! l : contractedOrbitSheaf S φ T ⟶ F, ∀ U t h,
      l.hom.app U (contractedOrbitQuotient S φ T U t h) = a U t h := by
  let η : contractedOrbitPresheaf S φ T ⟶ F.obj :=
    { app := fun U ↦ ↾(Quot.lift (fun x ↦ a U x.1 x.2) (by
        intro x y h
        obtain ⟨g, rfl⟩ := h
        exact (hi U g x.1 x.2).symm))
      naturality := by
        intro U V f
        apply ConcreteCategory.hom_ext
        intro x
        induction x using Quot.ind with
        | mk x => exact (hn f x.1 x.2).symm }
  let l : contractedOrbitSheaf S φ T ⟶ F :=
    ⟨sheafifyLift S.smallEtaleTopology η F.property⟩
  have hl : (toSheafify S.smallEtaleTopology (contractedOrbitPresheaf S φ T)) ≫
      l.hom = η := toSheafify_sheafifyLift _ _ _
  refine ⟨l, ?_, ?_⟩
  · intro U t h
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hl U) (Quot.mk _ (t, h))
  · intro m hm
    apply Sheaf.hom_ext
    apply sheafify_hom_ext S.smallEtaleTopology m.hom l.hom F.property
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    induction x using Quot.ind with
    | mk x =>
      change m.hom.app U (contractedOrbitQuotient S φ T U x.1 x.2) = _
      rw [hm]
      exact (ConcreteCategory.congr_hom (NatTrans.congr_app hl U)
        (Quot.mk _ x)).symm

end CategoryTheory.Sheaf.Torsor

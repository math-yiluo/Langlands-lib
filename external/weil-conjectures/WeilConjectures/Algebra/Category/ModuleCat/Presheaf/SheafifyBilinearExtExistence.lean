/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
/-!
# Existence of bilinear extensions through module sheafification

Source: Stacks Project, Modules on Sites, Tag 0GMW.
-/

@[expose] public section
universe u v w
open CategoryTheory
namespace PresheafOfModules
set_option backward.isDefEq.respectTransparency false in
-- The local gluing argument checks compatibility and four linearity laws in one declaration.
/-- A restriction-compatible bilinear family extends to the module sheafifications.
Source: Stacks Project, Modules on Sites, Tag 0GMW, the sheafification step of the
construction of tensor products.
(blueprint: lem-pc-sites-module-sheafification-bilinear-extension-existence)

Proof: Forget the module structures. The underlying maps of the two module
sheafification units are locally bijective maps of presheaves of sets, so their
product is locally bijective. Since the underlying presheaf of sets of `H` is a
sheaf, the natural map `(x,y) ↦ β X x y` extends uniquely to a natural map from
the product of the underlying sheafifications to `H`. Its unit equation is the
factorization equation. To prove additivity in the first variable, compare its
value on `(x + x', y)` with the sum of its values on `(x,y)` and `(x',y)`.
On a common covering sieve, all three sections lift along the module units;
naturality, the unit equation, and additivity of `β` make their restrictions
agree. Separatedness of `H` gives equality. The second-variable argument uses
lifts of `x,y,y'` in the same way. For scalar compatibility, also lift the scalar
along the locally surjective ring map `α`, on a common refinement of the covers
lifting the module sections. The units respect the scalar actions; linearity of
`β` over `O` proves both scalar identities on this cover, and separatedness gives
the identities over `R`. Thus the natural set map defines a curried `R`-linear
map at every object, with exactly the required naturality and unit equations. -/
theorem exists_bilinear_sheafification_extension
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (O : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (R : Sheaf J CommRingCat.{max u v w})
    (α : (O ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R).obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (F G : PresheafOfModules.{max u v w} (O ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}))
    (H : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R))
    (β : ∀ X : Cᵒᵖ, F.obj X →ₗ[O.obj X] G.obj X →ₗ[O.obj X]
      ((restrictScalars α).obj H.val).obj X)
    (hβ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X) (y : G.obj X),
      β Y (F.map f x) (G.map f y) = H.val.map f (β X x y)) :
    ∃ γ : ∀ X : Cᵒᵖ,
      ((sheafification α).obj F).val.obj X →ₗ[R.obj.obj X]
        ((sheafification α).obj G).val.obj X →ₗ[R.obj.obj X] H.val.obj X,
      (∀ {X Y : Cᵒᵖ} (f : X ⟶ Y)
        (x : ((sheafification α).obj F).val.obj X)
        (y : ((sheafification α).obj G).val.obj X),
        γ Y (((sheafification α).obj F).val.map f x)
          (((sheafification α).obj G).val.map f y) = H.val.map f (γ X x y)) ∧
      (∀ (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X),
        γ X (((sheafificationAdjunction α).unit.app F).app X x)
          (((sheafificationAdjunction α).unit.app G).app X y) = β X x y) := by
  classical
  let A := ((sheafification α).obj F).val
  let B := ((sheafification α).obj G).val
  let ηF := CategoryTheory.toSheafify J F.presheaf
  let ηG := CategoryTheory.toSheafify J G.presheaf
  have eq_lifts (X : Cᵒᵖ) (a a' : F.obj X) (b b' : G.obj X)
      (ha : ηF.app X a = ηF.app X a') (hb : ηG.app X b = ηG.app X b') :
      β X a b = β X a' b' := by
    apply H.isSheaf.isSeparated _
      (Presheaf.equalizerSieve (F := F.presheaf) a a' ⊓
        Presheaf.equalizerSieve (F := G.presheaf) b b')
      (J.intersection_covering (Presheaf.equalizerSieve_mem J ηF a a' ha)
        (Presheaf.equalizerSieve_mem J ηG b b' hb))
    intro Y f hf
    change H.val.map f.op (β X a b) = H.val.map f.op (β X a' b')
    rw [← hβ, ← hβ]
    exact congrArg₂ (fun a b ↦ β (Opposite.op Y) a b) hf.1 hf.2
  let S := fun (X : Cᵒᵖ) (x : A.obj X) (y : B.obj X) ↦
    Presheaf.imageSieve ηF x ⊓ Presheaf.imageSieve ηG y
  have hS (X : Cᵒᵖ) (x : A.obj X) (y : B.obj X) : S X x y ∈ J X.unop :=
    J.intersection_covering (Presheaf.imageSieve_mem J ηF x)
      (Presheaf.imageSieve_mem J ηG y)
  let t : ∀ (X : Cᵒᵖ) (x : A.obj X) (y : B.obj X),
      Presieve.FamilyOfElements (H.val.presheaf ⋙ forget _) (S X x y).arrows :=
    fun X x y ↦
    (fun Y f hf ↦ β (Opposite.op Y)
      (Presheaf.localPreimage ηF x f hf.1)
      (Presheaf.localPreimage ηG y f hf.2) :
      Presieve.FamilyOfElements (H.val.presheaf ⋙ forget _) (S X x y).arrows)
  have ht (X : Cᵒᵖ) (x : A.obj X) (y : B.obj X) : (t X x y).Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ fac
    change H.val.map g₁.op (β _ _ _) = H.val.map g₂.op (β _ _ _)
    rw [← hβ, ← hβ]
    apply eq_lifts
    · change ηF.app _ (F.presheaf.map g₁.op _) = ηF.app _ (F.presheaf.map g₂.op _)
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply,
        Presheaf.app_localPreimage, Presheaf.app_localPreimage]
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, fac]
    · change ηG.app _ (G.presheaf.map g₁.op _) = ηG.app _ (G.presheaf.map g₂.op _)
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply,
        Presheaf.app_localPreimage, Presheaf.app_localPreimage]
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, fac]
  have hH : Presieve.IsSheaf J (H.val.presheaf ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type J _).mp
      ((sheafCompose J (forget _)).obj ((SheafOfModules.toSheaf _).obj H)).property
  have hglue (X : Cᵒᵖ) (x : A.obj X) (y : B.obj X) :
      ∃ z : H.val.obj X, (t X x y).IsAmalgamation z :=
    ⟨(hH (S X x y) (hS X x y)).amalgamate (t X x y) (ht X x y),
      fun _ f hf ↦ (hH (S X x y) (hS X x y)).valid_glue (ht X x y) f hf⟩
  choose δ hδ using hglue
  have lift_value {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : A.obj X) (y : B.obj X)
      (a : F.obj Y) (b : G.obj Y)
      (ha : ηF.app Y a = A.map f x) (hb : ηG.app Y b = B.map f y) :
      H.val.map f (δ X x y) = β Y a b := by
    have hf : S X x y f.unop := ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact (hδ X x y f.unop hf).trans
      (eq_lifts Y _ a _ b ((Presheaf.app_localPreimage ηF x f.unop hf.1).trans ha.symm)
        ((Presheaf.app_localPreimage ηG y f.unop hf.2).trans hb.symm))
  have δ_unit (X : Cᵒᵖ) (a : F.obj X) (b : G.obj X) :
      δ X (ηF.app X a) (ηG.app X b) = β X a b := by
    simpa using lift_value (𝟙 X) (ηF.app X a) (ηG.app X b) a b
      (by simp) (by simp)
  have δ_natural {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : A.obj X) (y : B.obj X) :
      δ Y (A.map f x) (B.map f y) = H.val.map f (δ X x y) := by
    apply H.isSheaf.isSeparated _ _ (hS Y (A.map f x) (B.map f y))
    rintro Z g ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    change H.val.map g.op (δ Y (A.map f x) (B.map f y)) =
      H.val.map g.op (H.val.map f (δ X x y))
    rw [lift_value g.op _ _ a b ha hb]
    change β _ a b = H.val.presheaf.map g.op (H.val.presheaf.map f (δ X x y))
    rw [← Functor.map_comp_apply]
    exact (lift_value (f ≫ g.op) x y a b
      (by change ηF.app _ a = A.presheaf.map (f ≫ g.op) x
          rw [Functor.map_comp_apply]; exact ha)
      (by change ηG.app _ b = B.presheaf.map (f ≫ g.op) y
          rw [Functor.map_comp_apply]; exact hb)).symm
  have add_left (X : Cᵒᵖ) (x x' : A.obj X) (y : B.obj X) :
      δ X (x + x') y = δ X x y + δ X x' y := by
    apply H.isSheaf.isSeparated _
      (Presheaf.imageSieve ηF x ⊓ Presheaf.imageSieve ηF x' ⊓ Presheaf.imageSieve ηG y)
      (J.intersection_covering
        (J.intersection_covering (Presheaf.imageSieve_mem J ηF x)
          (Presheaf.imageSieve_mem J ηF x')) (Presheaf.imageSieve_mem J ηG y))
    rintro Y f ⟨⟨⟨a, ha⟩, ⟨a', ha'⟩⟩, ⟨b, hb⟩⟩
    change H.val.map f.op (δ X (x + x') y) =
      H.val.map f.op (δ X x y + δ X x' y)
    rw [map_add, lift_value f.op x y a b ha hb,
      lift_value f.op x' y a' b ha' hb,
      lift_value f.op (x + x') y (a + a') b
        (by change ηF.app _ (a + a') = A.presheaf.map f.op (x + x')
            rw [map_add, map_add, ha, ha']; rfl) hb, map_add, LinearMap.add_apply]
  have add_right (X : Cᵒᵖ) (x : A.obj X) (y y' : B.obj X) :
      δ X x (y + y') = δ X x y + δ X x y' := by
    apply H.isSheaf.isSeparated _
      (Presheaf.imageSieve ηF x ⊓ Presheaf.imageSieve ηG y ⊓ Presheaf.imageSieve ηG y')
      (J.intersection_covering
        (J.intersection_covering (Presheaf.imageSieve_mem J ηF x)
          (Presheaf.imageSieve_mem J ηG y)) (Presheaf.imageSieve_mem J ηG y'))
    rintro Y f ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨b', hb'⟩⟩
    change H.val.map f.op (δ X x (y + y')) =
      H.val.map f.op (δ X x y + δ X x y')
    rw [map_add, lift_value f.op x y a b ha hb,
      lift_value f.op x y' a b' ha hb',
      lift_value f.op x (y + y') a (b + b') ha
        (by change ηG.app _ (b + b') = B.presheaf.map f.op (y + y')
            rw [map_add, map_add, hb, hb']; rfl), map_add]
  have smul_left (X : Cᵒᵖ) (r : R.obj.obj X) (x : A.obj X) (y : B.obj X) :
      δ X (r • x) y = r • δ X x y := by
    apply H.isSheaf.isSeparated _
      (Presheaf.imageSieve α r ⊓ Presheaf.imageSieve ηF x ⊓ Presheaf.imageSieve ηG y)
      (J.intersection_covering
        (J.intersection_covering (Presheaf.imageSieve_mem J α r)
          (Presheaf.imageSieve_mem J ηF x)) (Presheaf.imageSieve_mem J ηG y))
    rintro Y f ⟨⟨⟨s, hs⟩, ⟨a, ha⟩⟩, ⟨b, hb⟩⟩
    change H.val.map f.op (δ X (r • x) y) = H.val.map f.op (r • δ X x y)
    rw [H.val.map_smul, lift_value f.op x y a b ha hb]
    rw [lift_value f.op (r • x) y (s • a) b
      (Sheafify.map_smul_eq α ηF r x f.op s hs a ha).symm hb]
    have heq := congrArg
      (fun l : G.obj (Opposite.op Y) →ₗ[O.obj (Opposite.op Y)]
        ((restrictScalars α).obj H.val).obj (Opposite.op Y) ↦ l b)
      ((β (Opposite.op Y)).map_smul s a)
    change β (Opposite.op Y) (s • a) b =
      (α.app _ s) • (show H.val.obj (Opposite.op Y) from β _ a b) at heq
    exact heq.trans (congrArg
      (fun q : R.obj.obj (Opposite.op Y) ↦ q •
        (show H.val.obj (Opposite.op Y) from β _ a b)) hs)
  have smul_right (X : Cᵒᵖ) (r : R.obj.obj X) (x : A.obj X) (y : B.obj X) :
      δ X x (r • y) = r • δ X x y := by
    apply H.isSheaf.isSeparated _
      (Presheaf.imageSieve α r ⊓ Presheaf.imageSieve ηF x ⊓ Presheaf.imageSieve ηG y)
      (J.intersection_covering
        (J.intersection_covering (Presheaf.imageSieve_mem J α r)
          (Presheaf.imageSieve_mem J ηF x)) (Presheaf.imageSieve_mem J ηG y))
    rintro Y f ⟨⟨⟨s, hs⟩, ⟨a, ha⟩⟩, ⟨b, hb⟩⟩
    change H.val.map f.op (δ X x (r • y)) = H.val.map f.op (r • δ X x y)
    rw [H.val.map_smul, lift_value f.op x y a b ha hb]
    rw [lift_value f.op x (r • y) a (s • b) ha
      (Sheafify.map_smul_eq α ηG r y f.op s hs b hb).symm]
    have heq := (β (Opposite.op Y) a).map_smul s b
    change β (Opposite.op Y) a (s • b) =
      (α.app _ s) • (show H.val.obj (Opposite.op Y) from β _ a b) at heq
    exact heq.trans (congrArg
      (fun q : R.obj.obj (Opposite.op Y) ↦ q •
        (show H.val.obj (Opposite.op Y) from β _ a b)) hs)
  let γ : ∀ X : Cᵒᵖ, A.obj X →ₗ[R.obj.obj X] B.obj X →ₗ[R.obj.obj X] H.val.obj X :=
    fun X ↦
      { toFun := fun x ↦
          { toFun := δ X x
            map_add' := add_right X x
            map_smul' := fun r y ↦ smul_right X r x y }
        map_add' := fun x x' ↦ by ext y; exact add_left X x x' y
        map_smul' := fun r x ↦ by ext y; exact smul_left X r x y }
  exact ⟨γ, fun f x y ↦ δ_natural f x y, δ_unit⟩
end PresheafOfModules

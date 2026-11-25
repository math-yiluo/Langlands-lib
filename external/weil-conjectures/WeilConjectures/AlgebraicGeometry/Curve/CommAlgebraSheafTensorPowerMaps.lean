/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Tensor-power maps into an algebra sheaf

Source: Stacks Project, Modules, Section 01CF; Tag 09MS.
(blueprint: lem-sc-algebra-sheaf-tensor-power-maps).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

private noncomputable def algebraUnit {X : Scheme.{u}} (B : X.CommAlgebraSheaf) :
    𝟙_ X.Modules ⟶ commAlgebraSheafModule X.sheaf B where
  val.app U := ModuleCat.homMk
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
      (B.hom.hom.app U)) (fun r ↦ by
      ext x
      exact ((B.hom.hom.app U).hom.map_mul r x).symm)
  val.naturality f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (B.hom.hom.naturality f) x

private noncomputable def presheafProduct {X : Scheme.{u}} {M N : X.Modules}
    (B : X.CommAlgebraSheaf) (f : M ⟶ commAlgebraSheafModule X.sheaf B)
    (g : N ⟶ commAlgebraSheafModule X.sheaf B) :
    M.val ⊗ N.val ⟶ (forgetToPresheafOfModules X).obj
      (commAlgebraSheafModule X.sheaf B) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun s t ↦ (show B.right.obj.obj U from f.val.app U s) *
      (show B.right.obj.obj U from g.val.app U t))
    (by intros; simp [map_add, add_mul])
    (by
      intro r s t
      change (show B.right.obj.obj U from f.val.app U (r • s)) *
        (show B.right.obj.obj U from g.val.app U t) =
        (B.hom.hom.app U r) * ((show B.right.obj.obj U from f.val.app U s) *
          (show B.right.obj.obj U from g.val.app U t))
      rw [(f.val.app U).hom.map_smul]
      exact mul_assoc _ _ _)
    (by intros; simp [map_add, mul_add])
    (by
      intro r s t
      change (show B.right.obj.obj U from f.val.app U s) *
        (show B.right.obj.obj U from g.val.app U (r • t)) =
        (B.hom.hom.app U r) * ((show B.right.obj.obj U from f.val.app U s) *
          (show B.right.obj.obj U from g.val.app U t))
      rw [(g.val.app U).hom.map_smul]
      exact mul_left_comm _ _ _)
  naturality {U V} h := ModuleCat.MonoidalCategory.tensor_ext (fun s t ↦ by
    symm
    change B.right.obj.map h ((show B.right.obj.obj U from f.val.app U s) *
      (show B.right.obj.obj U from g.val.app U t)) =
        (show B.right.obj.obj V from f.val.app V (M.val.map h s)) *
          (show B.right.obj.obj V from g.val.app V (N.val.map h t))
    rw [map_mul]
    congr 1
    · exact (PresheafOfModules.naturality_apply f.val h s).symm
    · exact (PresheafOfModules.naturality_apply g.val h t).symm)

@[irreducible] private noncomputable def sectionProduct {X : Scheme.{u}} {M N : X.Modules}
    (B : X.CommAlgebraSheaf) (f : M ⟶ commAlgebraSheafModule X.sheaf B)
    (g : N ⟶ commAlgebraSheafModule X.sheaf B) :
    M ⊗ N ⟶ commAlgebraSheafModule X.sheaf B :=
  (SheafOfModules.tensorObjIsoSheafification M N).hom ≫
    ((sheafificationAdjunction X).homEquiv _ _).symm (presheafProduct B f g)

private lemma sectionProduct_tmul {X : Scheme.{u}} {M N : X.Modules}
    (B : X.CommAlgebraSheaf) (f : M ⟶ commAlgebraSheafModule X.sheaf B)
    (g : N ⟶ commAlgebraSheafModule X.sheaf B) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (sectionProduct B f g).app U (tmulSection s t) =
      (show B.right.obj.obj (op U) from f.app U s) *
        (show B.right.obj.obj (op U) from g.app U t) := by
  have h := ((sheafificationAdjunction X).homEquiv _ _).apply_symm_apply
    (presheafProduct B f g)
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun k ↦ k.app (op U) (s ⊗ₜ t)) h
  unfold sectionProduct tmulSection
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
  exact hh

private lemma tensorSection_ext {X : Scheme.{u}} {M N P : X.Modules}
    (f g : M ⊗ N ⟶ P)
    (h : ∀ (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)),
      f.app U (tmulSection s t) = g.app U (tmulSection s t)) : f = g := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((sheafificationAdjunction X).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact h U.unop s t

private lemma tensorSection_ext_three {X : Scheme.{u}} {M N P Q : X.Modules}
    [M.IsInvertible] (f g : (M ⊗ N) ⊗ P ⟶ Q)
    (h : ∀ (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) (w : Γ(P, U)),
      f.app U (tmulSection (tmulSection s t) w) =
        g.app U (tmulSection (tmulSection s t) w)) : f = g := by
  classical
  have := IsInvertible.sheafOfModules_isInvertible M
  apply tensorSection_ext
  intro U z w
  choose V hx hVU e he using fun x : U ↦ exists_isFreeGenerator M x.2
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨Q.presheaf, Q.isSheaf⟩
  apply F.eq_of_locally_eq' (fun x : U ↦ (V x).1) U (fun x ↦ homOfLE (hVU x))
  · intro x hxU
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩
  · intro x
    rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map, tmulSection_map]
    obtain ⟨t, ht⟩ := ((he x).bijective_tmulSection_left (N := N) le_rfl).2
      ((M ⊗ N).presheaf.map (homOfLE (hVU x)).op z)
    simp only [presheaf_map_id_apply] at ht
    rw [← ht]
    exact h (V x).1 (e x) t _

private noncomputable def algebraPowers {X : Scheme.{u}} (L : X.Modules)
    (B : X.CommAlgebraSheaf) (j : L ⟶ commAlgebraSheafModule X.sheaf B) :
    ∀ d : ℕ, L.tensorPow d ⟶ commAlgebraSheafModule X.sheaf B
  | 0 => algebraUnit B
  | n + 1 => sectionProduct B j (algebraPowers L B j n)

private lemma algebraPowers_transport {X : Scheme.{u}} (L : X.Modules)
    (B : X.CommAlgebraSheaf) (j : L ⟶ commAlgebraSheafModule X.sheaf B)
    {m n : ℕ} (h : m = n) :
    eqToHom (congrArg L.tensorPow h) ≫ algebraPowers L B j n = algebraPowers L B j m := by
  cases h
  simp

/-- A map from an invertible module into an algebra sheaf extends to all tensor powers.

Source: Stacks Project, Modules, Section 01CF (tensor and symmetric algebras); Tag 09MS.
(blueprint: lem-sc-algebra-sheaf-tensor-power-maps).
Proof: Multiplication of sections is bilinear over the structure sheaf and commutes with
restriction. The presheaf tensor-product universal property, followed by the module
sheafification adjunction, gives a map U(B) tensor U(B) to U(B). Define b_0 by the
structure map and b_(n+1) by j tensor b_n followed by this multiplication map. The unit
law identifies b_1 with j after the right unitor. Induct on a in the multiplication
formula: a=0 is the left unit law, including the zero_add transport in tensorPowAddIso;
the successor case uses its recursive associator formula and associativity of section
multiplication. Equality of maps from sheaf tensor products can be tested on elementary
tensors before sheafification. For three factors, locally choose a frame of L; every
section of L tensor N is then an elementary tensor, and sheaf separation globalizes
the calculation. The zero algebra, degree zero and empty open obey the same laws. -/
theorem exists_commAlgebraSheaf_tensorPower_maps {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible]
    (B : X.CommAlgebraSheaf) (j : L ⟶ commAlgebraSheafModule X.sheaf B) :
    ∃ b : ∀ d : ℕ, L.tensorPow d ⟶ commAlgebraSheafModule X.sheaf B,
      (∀ (U : X.Opens) (r : Γ(X, U)),
        (b 0).app U (unitSectionsEquiv U r) = B.hom.hom.app (op U) r) ∧
      b 1 = (ρ_ L).hom ≫ j ∧
      ∀ (U : X.Opens) (a d : ℕ) (s : Γ(L.tensorPow a, U))
        (t : Γ(L.tensorPow d, U)),
        (show B.right.obj.obj (op U) from (b a).app U s) *
          (show B.right.obj.obj (op U) from (b d).app U t) =
          (show B.right.obj.obj (op U) from
            (b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t))) := by
  refine ⟨algebraPowers L B j, ?_, ?_, ?_⟩
  · intro U r
    rfl
  · apply tensorSection_ext
    intro U s t
    change (sectionProduct B j (algebraUnit B)).app U (tmulSection s t) = _
    change Γ(𝟙_ X.Modules, U) at t
    rw [sectionProduct_tmul, Hom.comp_app, ConcreteCategory.comp_apply]
    have ht := rightUnitor_hom_app_tmulSection' s t
    erw [ht]
    let r : Γ(X, U) := (unitSectionsEquiv U).symm t
    change (show B.right.obj.obj (op U) from j.app U s) * B.hom.hom.app (op U) r =
      j.app U (r • s)
    erw [Hom.app_smul]
    change _ = B.hom.hom.app (op U) r * (show B.right.obj.obj (op U) from j.app U s)
    exact mul_comm _ _
  · have hmap (a d : ℕ) :
        (L.tensorPowAddIso a d).inv ≫ algebraPowers L B j (a + d) =
          sectionProduct B (algebraPowers L B j a) (algebraPowers L B j d) := by
      induction a with
      | zero =>
        simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv]
        rw [Category.assoc, algebraPowers_transport L B j (Nat.zero_add d).symm]
        apply tensorSection_ext
        intro U s t
        change Γ(𝟙_ X.Modules, U) at s
        rw [Hom.comp_app, ConcreteCategory.comp_apply]
        erw [leftUnitor_hom_app_tmulSection', sectionProduct_tmul, Hom.app_smul]
        rfl
      | succ a ih =>
        simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv]
        rw [Category.assoc, Category.assoc,
          algebraPowers_transport L B j (Nat.succ_add a d).symm]
        apply tensorSection_ext_three
        intro U s t w
        simp only [tensorIso_inv, Iso.refl_inv, Hom.comp_app, ConcreteCategory.comp_apply,
          associator_hom_app_tmulSection]
        have htens := tensorHom_app_tmulSection (𝟙 L) (L.tensorPowAddIso a d).inv
          s (tmulSection t w)
        erw [htens]
        simp only [Hom.id_app, ConcreteCategory.id_apply, algebraPowers]
        have hi := congrArg (fun k ↦ k.app U (tmulSection t w)) ih
        rw [Hom.comp_app, ConcreteCategory.comp_apply, sectionProduct_tmul] at hi
        let q : B.right.obj.obj (op U) := j.app U s
        let r : B.right.obj.obj (op U) := (algebraPowers L B j a).app U t
        let v : B.right.obj.obj (op U) := (algebraPowers L B j d).app U w
        calc
          _ = q * (show B.right.obj.obj (op U) from
              (algebraPowers L B j (a + d)).app U
                ((L.tensorPowAddIso a d).inv.app U (tmulSection t w))) :=
            sectionProduct_tmul B j (algebraPowers L B j (a + d)) U s _
          _ = q * (r * v) := congrArg (fun x : B.right.obj.obj (op U) ↦ q * x) hi
          _ = (q * r) * v := (mul_assoc q r v).symm
          _ = (show B.right.obj.obj (op U) from
              (sectionProduct B j (algebraPowers L B j a)).app U (tmulSection s t)) * v :=
            congrArg (fun x : B.right.obj.obj (op U) ↦ x * v)
              (sectionProduct_tmul B j (algebraPowers L B j a) U s t).symm
          _ = _ := (sectionProduct_tmul B
            (sectionProduct B j (algebraPowers L B j a))
            (algebraPowers L B j d) U (tmulSection s t) w).symm
    intro U a d s t
    have hh := congrArg (fun k ↦ k.app U (tmulSection s t)) (hmap a d)
    rw [Hom.comp_app, ConcreteCategory.comp_apply, sectionProduct_tmul] at hh
    exact hh.symm

end
end AlgebraicGeometry.Scheme.Modules

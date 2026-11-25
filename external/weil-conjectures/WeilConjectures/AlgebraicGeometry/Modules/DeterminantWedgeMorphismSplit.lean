/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitComparison

/-!
# Bijectivity of the wedge morphism on a splitting open
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem exterior_sheafification_unit_map {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    {U V : X.Opens} (f : V ⟶ U) (z : (M.val.exteriorPower (R := X.presheaf) n).obj (op U)) :
    (exteriorPower M n).val.map f.op (((PresheafOfModules.sheafificationAdjunction.{v}
      (𝟙 X.ringCatSheaf.obj)).unit.app (M.val.exteriorPower (R := X.presheaf) n)).app (op U) z) =
      ((PresheafOfModules.sheafificationAdjunction.{v}
        (𝟙 X.ringCatSheaf.obj)).unit.app (M.val.exteriorPower (R := X.presheaf) n)).app (op V)
          ((M.val.exteriorPower (R := X.presheaf) n).map f.op z) := by
  exact (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction.{v}
      (𝟙 X.ringCatSheaf.obj)).unit.app (M.val.exteriorPower (R := X.presheaf) n)) f.op z).symm

private theorem generated_sheafification_induction {X : Scheme.{v}}
    (Q : _root_.PresheafOfModules.{v} X.ringCatSheaf.obj)
    (G : ∀ U : X.Opens, Set (Q.obj (op U)))
    (hG : ∀ U, Submodule.span (X.presheaf.obj (op U)) (G U) = ⊤)
    (P : ∀ U : X.Opens,
      ((PresheafOfModules.sheafification.{v} (𝟙 X.ringCatSheaf.obj)).obj Q).val.obj
        (op U) → Prop)
    (hzero : ∀ U, P U 0)
    (hadd : ∀ U x y, P U x → P U y → P U (x + y))
    (hsmul : ∀ U (c : X.presheaf.obj (op U)) x, P U x → P U (c • x))
    (hgen : ∀ U a, a ∈ G U → P U
      (((PresheafOfModules.sheafificationAdjunction.{v}
        (𝟙 X.ringCatSheaf.obj)).unit.app Q).app (op U) a))
    (hlocal : ∀ U x (S : Sieve U), S ∈ Opens.grothendieckTopology X U →
      (∀ (V : X.Opens) (f : V ⟶ U), S f →
        P V (((PresheafOfModules.sheafification.{v}
          (𝟙 X.ringCatSheaf.obj)).obj Q).val.map f.op x)) → P U x) :
    ∀ U x, P U x := by
  intro U x
  let η := (PresheafOfModules.sheafificationAdjunction.{v}
    (𝟙 X.ringCatSheaf.obj)).unit.app Q
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map η) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective
  apply hlocal U x (Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map η) x)
    (Presheaf.imageSieve_mem _ _ _)
  intro V f hf
  obtain ⟨z, hz⟩ := hf
  change η.app (op V) z =
    ((PresheafOfModules.sheafification.{v}
      (𝟙 X.ringCatSheaf.obj)).obj Q).val.map f.op x at hz
  rw [← hz]
  have hzspan : z ∈ Submodule.span (X.presheaf.obj (op V))
      (G V) := by
    rw [hG V]
    trivial
  clear hz
  induction hzspan using Submodule.span_induction with
  | mem z hz =>
    exact hgen V z hz
  | zero => rw [map_zero]; exact hzero V
  | add x y _ _ hx hy => rw [map_add]; exact hadd V _ _ hx hy
  | smul c x _ hx =>
    rw [(η.app (op V)).hom.map_smul]
    exact hsmul V c _ hx

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_section_map {X : Scheme.{v}} {M N : X.Modules}
    {U V : X.Opens} (f : V ⟶ U) (x : M.val.obj (op U)) (y : N.val.obj (op U)) :
    (M ⊗ N).val.map f.op (tmulSection x y) =
      tmulSection (M.val.map f.op x) (N.val.map f.op y) := by
  have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
  have hm := tmulSection_map (M := M) (N := N) (leOfHom f) x y
  rw [hf] at hm
  exact hm

private theorem tensor_section_induction {X : Scheme.{v}} (M N : X.Modules)
    (P : ∀ U : X.Opens, (M ⊗ N).val.obj (op U) → Prop)
    (_hzero : ∀ U, P U 0)
    (hadd : ∀ U x y, P U x → P U y → P U (x + y))
    (htmul : ∀ U x y, P U (tmulSection x y))
    (hlocal : ∀ U x (S : Sieve U), S ∈ Opens.grothendieckTopology X U →
      (∀ (V : X.Opens) (f : V ⟶ U), S f →
        P V ((M ⊗ N).val.map f.op x)) → P U x) :
    ∀ U x, P U x := by
  intro U x
  let e := SheafOfModules.tensorObjIsoSheafification M N
  let η := toSheafifyTensor M N
  let k := η ≫ e.inv.val
  have hη : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map η) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map k) := by
    dsimp only [k]
    rw [Functor.map_comp]
    have : IsIso ((PresheafOfModules.toPresheaf _).map e.inv.val) := by
      change IsIso ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf _).map e.inv)
      infer_instance
    infer_instance
  apply hlocal U x (Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map k) x)
    (Presheaf.imageSieve_mem _ _ _)
  intro V f hf
  obtain ⟨z, hz⟩ := hf
  change k.app (op V) z = (M ⊗ N).val.map f.op x at hz
  rw [← hz]
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul a b => exact htmul V a b
  | add a b ha hb => rw [map_add]; exact hadd V _ _ ha hb

set_option backward.isDefEq.respectTransparency false in
private theorem local_comparison_eq {X : Scheme.{v}} {A D : X.Modules}
    (φ : A ⟶ D) (T : X.Opens)
    (d : ∀ W : X.Opens, W ≤ T →
      A.val.obj (op W) ≃ₗ[X.presheaf.obj (op W)] D.val.obj (op W))
    (hd : ∀ (W V : X.Opens) (hW : W ≤ T) (hVW : V ≤ W) x,
      D.val.map (homOfLE hVW).op (d W hW x) =
        d V (hVW.trans hW) (A.val.map (homOfLE hVW).op x))
    (W : X.Opens) (hW : W ≤ T) (x : A.val.obj (op W))
    (S : Sieve W) (hS : S ∈ Opens.grothendieckTopology X W)
    (h : ∀ (V : X.Opens) (f : V ⟶ W), S f →
      φ.val.app (op V) (A.val.map f.op x) =
        d V ((leOfHom f).trans hW) (A.val.map f.op x)) :
    φ.val.app (op W) x = d W hW x := by
  apply (D.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext
  intro V f hf
  have hf' : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
  have hd' := hd W V hW (leOfHom f) x
  rw [hf'] at hd'
  change D.presheaf.map f.op (φ.app W x) = D.presheaf.map f.op (d W hW x)
  rw [← Hom.app_presheaf_map]
  exact (h V f hf).trans hd'.symm

set_option backward.isDefEq.respectTransparency false in
private theorem split_quotient_section_surjective {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (W : X.Opens) (hW : W ≤ U) : Function.Surjective (S.g.app W) := by
  let t : S.X₃.restrict U.ι ⟶ S.X₂.restrict U.ι := biprod.inr ≫ e.inv
  have ht : t ≫ (restrictFunctor U.ι).map S.g = 𝟙 _ := by
    rw [← hg]
    simp [t]
  have hs (V : U.toScheme.Opens) :
      Function.Surjective (((restrictFunctor U.ι).map S.g).app V) := by
    intro b
    refine ⟨t.app V b, ?_⟩
    have h := congrArg (fun k ↦ k.app V b) ht
    simpa only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app,
      ConcreteCategory.id_apply] using h
  have h := hs (U.ι ⁻¹ᵁ W)
  change Function.Surjective (S.g.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ W))) at h
  have hi : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  rwa [hi] at h

set_option backward.isDefEq.respectTransparency false in
private theorem bijective_of_locally_bijective {X : Scheme.{v}} {A D : X.Modules}
    (φ : A ⟶ D) (U : X.Opens)
    (h : ∀ x ∈ U, ∃ V : X.Opens, V ≤ U ∧ x ∈ V ∧
      ∀ W ≤ V, Function.Bijective (φ.app W)) :
    ∀ W ≤ U, Function.Bijective (φ.app W) := by
  have hinj (W : X.Opens) (hW : W ≤ U) : Function.Injective (φ.app W) := by
    intro a b hab
    apply A.isSheaf.section_ext
    intro x hx
    obtain ⟨V, hV, hxV, hb⟩ := h x (hW hx)
    refine ⟨W ⊓ V, inf_le_left, ⟨hx, hxV⟩, ?_⟩
    apply (hb (W ⊓ V) inf_le_right).1
    rw [Hom.app_presheaf_map, Hom.app_presheaf_map, hab]
  intro W hW
  refine ⟨hinj W hW, ?_⟩
  intro y
  let T : Sieve W :=
    { arrows := fun V _ ↦ ∀ Z ≤ V, Function.Bijective (φ.app Z)
      downward_closed := by
        intro V Z f hf g Q hQ
        exact hf Q (hQ.trans (leOfHom g)) }
  have hT : T ∈ Opens.grothendieckTopology X W := by
    intro x hx
    obtain ⟨V, hV, hxV, hb⟩ := h x (hW hx)
    refine ⟨W ⊓ V, homOfLE inf_le_left, ?_, ⟨hx, hxV⟩⟩
    intro Z hZ
    exact hb Z (hZ.trans inf_le_right)
  let z : Presieve.FamilyOfElements (A.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
      T.arrows := fun V f hf ↦ Function.surjInv (hf V le_rfl).2 (D.presheaf.map f.op y)
  have hz {V : X.Opens} (f : V ⟶ W) (hf : T f) :
      φ.app V (z f hf) = D.presheaf.map f.op y :=
    Function.surjInv_eq (hf V le_rfl).2 _
  have hc : z.Compatible := by
    intro V₁ V₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ heq
    apply hinj Z ((leOfHom (g₁ ≫ f₁)).trans hW)
    change φ.app Z (A.presheaf.map g₁.op (z f₁ hf₁)) =
      φ.app Z (A.presheaf.map g₂.op (z f₂ hf₂))
    rw [Hom.app_presheaf_map, Hom.app_presheaf_map, hz f₁ hf₁, hz f₂ hf₂,
      presheaf_map_map_apply, presheaf_map_map_apply, heq]
  let hA := A.isSheaf_presheaf_comp_forget _ hT
  refine ⟨hA.amalgamate z hc, ?_⟩
  apply (D.isSheaf_presheaf_comp_forget _ hT).isSeparatedFor.ext
  intro V f hf
  change D.presheaf.map f.op (φ.app W _) = D.presheaf.map f.op y
  rw [← Hom.app_presheaf_map]
  exact (congrArg (φ.app V) (hA.valid_glue hc f hf)).trans (hz f hf)

set_option backward.isDefEq.respectTransparency false in
private theorem bijective_of_comparison {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    (φ : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶ exteriorPower S.X₂ r₂)
    (hφ : ∀ (V : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op V))
      (b : Fin r₃ → S.X₃.val.obj (op V)) (c : Fin r₃ → S.X₂.val.obj (op V)),
      (∀ i, S.g.val.app (op V) (c i) = b i) →
      φ.val.app (op V)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := V) a)
          (wedge (M := S.X₃) (r := r₃) (U := V) b)) =
        wedge (M := S.X₂) (r := r₂) (U := V)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op V) (a j)) c (Fin.cast hr i)))
    (U : X.Opens)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b)
    (d : ∀ (W : X.Opens), W ≤ U →
      (exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.obj (op W)
        ≃ₗ[X.presheaf.obj (op W)] (exteriorPower S.X₂ r₂).val.obj (op W))
    (hdwedge : ∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
      (b : Fin r₃ → S.X₃.val.obj (op W)),
      d W hW (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) a)
        (wedge (M := S.X₃) (r := r₃) (U := W) b)) =
      wedge (M := S.X₂) (r := r₂) (U := W)
        (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
          (fun j ↦ l W hW (b j)) (Fin.cast hr i)))
    (hdmap : ∀ (W V : X.Opens) (hW : W ≤ U) (hVW : V ≤ W) x,
      (exteriorPower S.X₂ r₂).val.map (homOfLE hVW).op (d W hW x) =
        d V (hVW.trans hW)
          ((exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.map
            (homOfLE hVW).op x)) :
    ∀ W ≤ U, Function.Bijective (φ.app W) := by
  have hpure (W : X.Opens) (hW : W ≤ U)
      (a : Fin r₁ → S.X₁.val.obj (op W)) (b : Fin r₃ → S.X₃.val.obj (op W)) :
      φ.val.app (op W) (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) a)
        (wedge (M := S.X₃) (r := r₃) (U := W) b)) =
      d W hW (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) a)
        (wedge (M := S.X₃) (r := r₃) (U := W) b)) := by
    exact (hφ W a b (fun i ↦ l W hW (b i)) (fun i ↦ hl W hW (b i))).trans
      (hdwedge W hW a b).symm
  have hsecond := generated_sheafification_induction (S.X₃.val.exteriorPower (R := X.presheaf) r₃)
    (fun W ↦ Set.range (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r₃))
    (fun W ↦ _root_.exteriorPower.ιMulti_span _ _ _)
    (fun W y ↦ ∀ hW : W ≤ U, ∀ a : Fin r₁ → S.X₁.val.obj (op W),
      φ.val.app (op W) (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) a) y) =
        d W hW (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) a) y))
    (by intro W hW a; simp only [tmulSection_zero, map_zero])
    (by
      intro W x y hx hy hW a
      rw [tmulSection_add (M := exteriorPower S.X₁ r₁) (N := exteriorPower S.X₃ r₃),
        map_add, map_add, hx hW a, hy hW a])
    (by
      intro W c x hx hW a
      rw [tmulSection_smul, (φ.val.app (op W)).hom.map_smul,
        (d W hW).map_smul, hx hW a])
    (by intro W z hz; obtain ⟨b, rfl⟩ := hz; intro hW a; exact hpure W hW a b)
    (by
      intro W y T hT ht hW a
      apply local_comparison_eq φ U d hdmap W hW _ T hT
      intro V f hf
      rw [tensor_section_map]
      have hm := exterior_sheafification_unit_map S.X₁ r₁ f
        (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r₁ a)
      have hr :=
        (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := X.presheaf) S.X₁.val r₁ f.op) a
      have hm' : (exteriorPower S.X₁ r₁).val.map f.op
          (wedge (M := S.X₁) (r := r₁) (U := W) a) =
        wedge (M := S.X₁) (r := r₁) (U := V) (fun i ↦ S.X₁.val.map f.op (a i)) :=
        hm.trans (congrArg
          (((PresheafOfModules.sheafificationAdjunction.{v}
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (S.X₁.val.exteriorPower (R := X.presheaf) r₁)).app (op V)) hr)
      rw [hm']
      exact ht V f hf ((leOfHom f).trans hW) (fun i ↦ S.X₁.val.map f.op (a i)))
  have hfirst := generated_sheafification_induction (S.X₁.val.exteriorPower (R := X.presheaf) r₁)
    (fun W ↦ Set.range (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r₁))
    (fun W ↦ _root_.exteriorPower.ιMulti_span _ _ _)
    (fun W x ↦ ∀ hW : W ≤ U, ∀ y : (exteriorPower S.X₃ r₃).val.obj (op W),
      φ.val.app (op W) (tmulSection x y) = d W hW (tmulSection x y))
    (by intro W hW y; simp only [zero_tmulSection, map_zero])
    (by
      intro W x y hx hy hW z
      rw [add_tmulSection (M := exteriorPower S.X₁ r₁) (N := exteriorPower S.X₃ r₃),
        map_add, map_add, hx hW z, hy hW z])
    (by
      intro W c x hx hW y
      rw [smul_tmulSection, (φ.val.app (op W)).hom.map_smul,
        (d W hW).map_smul, hx hW y])
    (by intro W z hz; obtain ⟨a, rfl⟩ := hz; intro hW y; exact hsecond W y hW a)
    (by
      intro W x T hT ht hW y
      apply local_comparison_eq φ U d hdmap W hW _ T hT
      intro V f hf
      rw [tensor_section_map]
      exact ht V f hf ((leOfHom f).trans hW) ((exteriorPower S.X₃ r₃).val.map f.op y))
  have hall := tensor_section_induction (exteriorPower S.X₁ r₁)
    (exteriorPower S.X₃ r₃)
    (fun W x ↦ ∀ hW : W ≤ U, φ.val.app (op W) x = d W hW x)
    (by intro W hW; simp only [map_zero])
    (by intro W x y hx hy hW; rw [map_add, map_add, hx hW, hy hW])
    (by intro W x y hW; exact hfirst W x hW y)
    (by
      intro W x T hT ht hW
      apply local_comparison_eq φ U d hdmap W hW x T hT
      intro V f hf
      exact ht V f hf ((leOfHom f).trans hW))
  intro W hW
  have heq : (fun x ↦ φ.app W x) = (fun x ↦ d W hW x) :=
    funext (fun x ↦ hall W x hW)
  rw [show Function.Bijective (φ.app W) =
    Function.Bijective (fun x ↦ φ.app W x) from rfl, heq]
  exact (d W hW).bijective

set_option backward.isDefEq.respectTransparency false in
/-- A morphism satisfying the wedge formula is bijective on sections over every open
contained in an open on which the sequence splits. No global exactness is needed here. -/
theorem determinant_wedgeMorphism_bijective_of_split {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (φ : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶ exteriorPower S.X₂ r₂)
    (hφ : ∀ (V : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op V))
      (b : Fin r₃ → S.X₃.val.obj (op V)) (c : Fin r₃ → S.X₂.val.obj (op V)),
      (∀ i, S.g.val.app (op V) (c i) = b i) →
      φ.val.app (op V)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := V) a)
          (wedge (M := S.X₃) (r := r₃) (U := V) b)) =
        wedge (M := S.X₂) (r := r₂) (U := V)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op V) (a j)) c (Fin.cast hr i)))
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g) :
    ∀ W ≤ U, Function.Bijective (φ.app W) := by
  classical
  let l (W : X.Opens) (hW : W ≤ U) :=
    Function.surjInv (split_quotient_section_surjective S U e hg W hW)
  have hl (W : X.Opens) (hW : W ≤ U) (b : S.X₃.val.obj (op W)) :
      S.g.val.app (op W) (l W hW b) = b :=
    Function.surjInv_eq (split_quotient_section_surjective S U e hg W hW) b
  apply bijective_of_locally_bijective φ U
  intro x hx
  obtain ⟨V, hVU, hxV, d, hdwedge, hdmap⟩ :=
    determinant_split_comparison_exists S r₁ r₂ r₃ hr U e hf hg l hl x hx
  refine ⟨V, hVU, hxV, ?_⟩
  exact bijective_of_comparison S r₁ r₂ r₃ hr φ hφ V
    (fun W hW ↦ l W (hW.trans hVU))
    (fun W hW b ↦ hl W (hW.trans hVU) b) d hdwedge hdmap

end AlgebraicGeometry.Scheme.Modules

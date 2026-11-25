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
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorLocalPairing
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero
import Mathlib.Data.Finset.Piecewise

/-!
# Linear part of the split determinant construction
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem unit_bijective {X : Scheme.{v}} (M : X.Modules)
    (U W : X.Opens) (hW : W ≤ U) :
    Function.Bijective (((restrictAdjunction U.ι).unit.app M).val.app (op W)) := by
  change Function.Bijective (((restrictAdjunction U.ι).unit.app M).app W)
  rw [restrictAdjunction_unit_app_app]
  have hi : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  have : IsIso (homOfLE (U.ι.image_preimage_le W)) :=
    ⟨⟨homOfLE (by rw [hi]), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  exact (ConcreteCategory.bijective_of_isIso (M.presheaf.map
    (homOfLE (U.ι.image_preimage_le W)).op))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def localEval {X : Scheme.{v}} {M N : X.Modules}
    (U : X.Opens) (t : M.restrict U.ι ⟶ N.restrict U.ι)
    (W : X.Opens) (hW : W ≤ U) :
    M.val.obj (op W) →ₗ[X.presheaf.obj (op W)] N.val.obj (op W) :=
  ((LinearEquiv.ofBijective (((restrictAdjunction U.ι).unit.app N).val.app
    (op W)).hom (unit_bijective N U W hW)).symm.toLinearMap).comp
    ((((restrictAdjunction U.ι).unit.app M) ≫ (pushforward U.ι).map t).val.app (op W)).hom

set_option backward.isDefEq.respectTransparency false in
private theorem localEval_unit {X : Scheme.{v}} {M N : X.Modules}
    (U : X.Opens) (t : M.restrict U.ι ⟶ N.restrict U.ι)
    (W : X.Opens) (hW : W ≤ U) (x : M.val.obj (op W)) :
    ((restrictAdjunction U.ι).unit.app N).val.app (op W)
      (localEval U t W hW x) =
    ((((restrictAdjunction U.ι).unit.app M) ≫ (pushforward U.ι).map t).val.app (op W)) x := by
  exact (LinearEquiv.ofBijective _ (unit_bijective N U W hW)).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
private theorem localEval_map {X : Scheme.{v}} {M N : X.Modules}
    (U : X.Opens) (t : M.restrict U.ι ⟶ N.restrict U.ι)
    (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) (x : M.val.obj (op W)) :
    N.val.map (homOfLE hZW).op (localEval U t W hW x) =
      localEval U t Z (hZW.trans hW) (M.val.map (homOfLE hZW).op x) := by
  apply (unit_bijective N U Z (hZW.trans hW)).1
  have hn := PresheafOfModules.naturality_apply
    ((restrictAdjunction U.ι).unit.app N).val (homOfLE hZW).op
    (localEval U t W hW x)
  apply hn.trans
  exact (congrArg (fun y ↦
    ((restrictFunctor U.ι ⋙ pushforward U.ι).obj N).val.map (homOfLE hZW).op y)
    (localEval_unit U t W hW x)).trans
    ((PresheafOfModules.naturality_apply
    (((restrictAdjunction U.ι).unit.app M) ≫ (pushforward U.ι).map t).val
    (homOfLE hZW).op x).symm.trans
      (localEval_unit U t Z (hZW.trans hW) _).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem localEval_comp {X : Scheme.{v}} {M N P : X.Modules}
    (U : X.Opens) (t : M.restrict U.ι ⟶ N.restrict U.ι)
    (s : N.restrict U.ι ⟶ P.restrict U.ι)
    (W : X.Opens) (hW : W ≤ U) (x : M.val.obj (op W)) :
    localEval U (t ≫ s) W hW x = localEval U s W hW (localEval U t W hW x) := by
  apply (unit_bijective P U W hW).1
  rw [localEval_unit, localEval_unit]
  change ((pushforward U.ι).map (t ≫ s)).val.app (op W)
      (((restrictAdjunction U.ι).unit.app M).val.app (op W) x) =
    ((pushforward U.ι).map s).val.app (op W)
      (((restrictAdjunction U.ι).unit.app N).val.app (op W) (localEval U t W hW x))
  rw [localEval_unit, Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem localEval_restrict {X : Scheme.{v}} {M N : X.Modules}
    (U : X.Opens) (f : M ⟶ N)
    (W : X.Opens) (hW : W ≤ U) (x : M.val.obj (op W)) :
    localEval U ((restrictFunctor U.ι).map f) W hW x = f.val.app (op W) x := by
  apply (unit_bijective N U W hW).1
  rw [localEval_unit]
  have h := congrArg (fun k ↦ k.val.app (op W) x)
    ((restrictAdjunction U.ι).unit.naturality f)
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
private theorem localEval_id {X : Scheme.{v}} (M : X.Modules)
    (U W : X.Opens) (hW : W ≤ U) (x : M.val.obj (op W)) :
    localEval U (𝟙 (M.restrict U.ι)) W hW x = x := by
  apply (unit_bijective M U W hW).1
  rw [localEval_unit]
  have h : ((restrictAdjunction U.ι).unit.app M) ≫
      (pushforward U.ι).map (𝟙 (M.restrict U.ι)) =
      (restrictAdjunction U.ι).unit.app M := by simp
  exact congrArg (fun k ↦ k.val.app (op W) x) h

set_option backward.isDefEq.respectTransparency false in
private theorem localEval_add {X : Scheme.{v}} {M N : X.Modules}
    (U : X.Opens) (t s : M.restrict U.ι ⟶ N.restrict U.ι)
    (W : X.Opens) (hW : W ≤ U) (x : M.val.obj (op W)) :
    localEval U (t + s) W hW x = localEval U t W hW x + localEval U s W hW x := by
  apply (unit_bijective N U W hW).1
  rw [map_add, localEval_unit, localEval_unit, localEval_unit]
  change ((pushforward U.ι).map (t + s)).val.app (op W)
      (((restrictAdjunction U.ι).unit.app M).val.app (op W) x) = _
  rw [Functor.map_add]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem splitting_identity {X : Scheme.{v}}
    {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C) (U : X.Opens)
    (e : B.restrict U.ι ≅ A.restrict U.ι ⊞ C.restrict U.ι)
    (hf : (restrictFunctor U.ι).map f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map g) :
    (e.hom ≫ biprod.fst) ≫ (restrictFunctor U.ι).map f +
      (restrictFunctor U.ι).map g ≫ (biprod.inr ≫ e.inv) = 𝟙 _ := by
  have hf' : (restrictFunctor U.ι).map f = biprod.inl ≫ e.inv := by
    rw [← hf, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [hf', ← hg]
  calc
    _ = e.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ e.inv := by
      simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
    _ = 𝟙 _ := by rw [biprod.total]; simp

set_option backward.isDefEq.respectTransparency false in
private theorem splitting_lift {X : Scheme.{v}} {A B C : X.Modules}
    (g : B ⟶ C) (U : X.Opens)
    (e : B.restrict U.ι ≅ A.restrict U.ι ⊞ C.restrict U.ι)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map g)
    (W : X.Opens) (hW : W ≤ U) (b : C.val.obj (op W)) :
    g.val.app (op W) (localEval U (biprod.inr ≫ e.inv) W hW b) = b := by
  rw [← localEval_restrict U g W hW, ← localEval_comp]
  have ht : (biprod.inr ≫ e.inv) ≫ (restrictFunctor U.ι).map g = 𝟙 _ := by
    rw [← hg]
    simp
  rw [ht, localEval_id]

set_option backward.isDefEq.respectTransparency false in
private theorem splitting_kernel {X : Scheme.{v}} {A B C : X.Modules}
    (f : A ⟶ B) (g : B ⟶ C) (U : X.Opens)
    (e : B.restrict U.ι ≅ A.restrict U.ι ⊞ C.restrict U.ι)
    (hf : (restrictFunctor U.ι).map f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map g)
    (W : X.Opens) (hW : W ≤ U) (b : B.val.obj (op W))
    (hb : g.val.app (op W) b = 0) :
    f.val.app (op W) (localEval U (e.hom ≫ biprod.fst) W hW b) = b := by
  have h := congrArg (fun t ↦ localEval U t W hW b) (splitting_identity f g U e hf hg)
  rw [localEval_add, localEval_comp, localEval_comp,
    localEval_restrict, localEval_restrict, hb, map_zero, add_zero, localEval_id] at h
  exact h

private theorem locally_surjective_generated_induction {X : Scheme.{v}}
    (Q : _root_.PresheafOfModules.{v} X.ringCatSheaf.obj)
    (E : X.Modules) (η : Q ⟶ E.val)
    (hη : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map η))
    (G : ∀ U : X.Opens, Set (Q.obj (op U)))
    (hG : ∀ U, Submodule.span (X.presheaf.obj (op U)) (G U) = ⊤)
    (P : ∀ U : X.Opens, E.val.obj (op U) → Prop)
    (hzero : ∀ U, P U 0)
    (hadd : ∀ U x y, P U x → P U y → P U (x + y))
    (hsmul : ∀ U (c : X.presheaf.obj (op U)) x, P U x → P U (c • x))
    (hgen : ∀ U a, a ∈ G U → P U (η.app (op U) a))
    (hlocal : ∀ U x (S : Sieve U), S ∈ Opens.grothendieckTopology X U →
      (∀ (V : X.Opens) (f : V ⟶ U), S f →
        P V (E.val.map f.op x)) → P U x) :
    ∀ U x, P U x := by
  intro U x
  let := hη
  apply hlocal U x (Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map η) x)
    (Presheaf.imageSieve_mem _ _ _)
  intro V f hf
  obtain ⟨z, hz⟩ := hf
  change η.app (op V) z = E.val.map f.op x at hz
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
private theorem local_family_eq {X : Scheme.{v}} {A D : X.Modules}
    (U : X.Opens)
    (d e : ∀ W : X.Opens, W ≤ U →
      A.val.obj (op W) →ₗ[X.presheaf.obj (op W)] D.val.obj (op W))
    (hd : ∀ (W V : X.Opens) (hW : W ≤ U) (hVW : V ≤ W) x,
      D.val.map (homOfLE hVW).op (d W hW x) =
        d V (hVW.trans hW) (A.val.map (homOfLE hVW).op x))
    (he : ∀ (W V : X.Opens) (hW : W ≤ U) (hVW : V ≤ W) x,
      D.val.map (homOfLE hVW).op (e W hW x) =
        e V (hVW.trans hW) (A.val.map (homOfLE hVW).op x))
    (W : X.Opens) (hW : W ≤ U) (x : A.val.obj (op W))
    (S : Sieve W) (hS : S ∈ Opens.grothendieckTopology X W)
    (h : ∀ (V : X.Opens) (f : V ⟶ W), S f →
      d V ((leOfHom f).trans hW) (A.val.map f.op x) =
        e V ((leOfHom f).trans hW) (A.val.map f.op x)) :
    d W hW x = e W hW x := by
  apply (D.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext
  intro V f hf
  have hf' : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
  have hd' := hd W V hW (leOfHom f) x
  have he' := he W V hW (leOfHom f) x
  rw [hf'] at hd' he'
  exact hd'.trans ((h V f hf).trans he'.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem local_wedge_family_ext {X : Scheme.{v}} (A C D : X.Modules)
    (r s : ℕ) (U : X.Opens)
    (d e : ∀ W : X.Opens, W ≤ U →
      (exteriorPower A r ⊗ exteriorPower C s).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] D.val.obj (op W))
    (hdmap : ∀ (W V : X.Opens) (hW : W ≤ U) (hVW : V ≤ W) x,
      D.val.map (homOfLE hVW).op (d W hW x) =
        d V (hVW.trans hW)
          ((exteriorPower A r ⊗ exteriorPower C s).val.map (homOfLE hVW).op x))
    (hemap : ∀ (W V : X.Opens) (hW : W ≤ U) (hVW : V ≤ W) x,
      D.val.map (homOfLE hVW).op (e W hW x) =
        e V (hVW.trans hW)
          ((exteriorPower A r ⊗ exteriorPower C s).val.map (homOfLE hVW).op x))
    (hpure : ∀ W hW (a : Fin r → A.val.obj (op W))
      (b : Fin s → C.val.obj (op W)),
      d W hW (tmulSection (wedge (M := A) (r := r) (U := W) a)
        (wedge (M := C) (r := s) (U := W) b)) =
      e W hW (tmulSection (wedge (M := A) (r := r) (U := W) a)
        (wedge (M := C) (r := s) (U := W) b))) : d = e := by
  have hsecond := locally_surjective_generated_induction (C.val.exteriorPower (R := X.presheaf) s)
    (exteriorPower C s)
    ((PresheafOfModules.sheafificationAdjunction.{v}
      (𝟙 X.ringCatSheaf.obj)).unit.app (C.val.exteriorPower (R := X.presheaf) s))
    (by
      rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
      exact (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective)
    (fun W ↦ Set.range (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) s))
    (fun W ↦ _root_.exteriorPower.ιMulti_span _ _ _)
    (fun W y ↦ ∀ hW : W ≤ U, ∀ a : Fin r → A.val.obj (op W),
      d W hW (tmulSection (wedge (M := A) (r := r) (U := W) a) y) =
        e W hW (tmulSection (wedge (M := A) (r := r) (U := W) a) y))
    (by intro W hW a; simp only [tmulSection_zero, map_zero])
    (by
      intro W x y hx hy hW a
      rw [tmulSection_add (M := exteriorPower A r) (N := exteriorPower C s),
        map_add, map_add, hx hW a, hy hW a])
    (by
      intro W c x hx hW a
      rw [tmulSection_smul, (d W hW).map_smul,
        (e W hW).map_smul, hx hW a])
    (by intro W z hz; obtain ⟨b, rfl⟩ := hz; intro hW a; exact hpure W hW a b)
    (by
      intro W y T hT ht hW a
      apply local_family_eq U d e hdmap hemap W hW _ T hT
      intro V f hf
      have hf' : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
      rw [← hf']
      erw [tmulSection_map (M := exteriorPower A r) (N := exteriorPower C s)]
      rw [hf']
      have hm := (PresheafOfModules.naturality_apply
        ((PresheafOfModules.sheafificationAdjunction.{v}
          (𝟙 X.ringCatSheaf.obj)).unit.app (A.val.exteriorPower (R := X.presheaf) r)) f.op
        (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r a)).symm
      have hr :=
        (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := X.presheaf) A.val r f.op) a
      have hm' : (exteriorPower A r).val.map f.op
          (wedge (M := A) (r := r) (U := W) a) =
        wedge (M := A) (r := r) (U := V) (fun i ↦ A.val.map f.op (a i)) :=
        hm.trans (congrArg
          (((PresheafOfModules.sheafificationAdjunction.{v}
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (A.val.exteriorPower (R := X.presheaf) r)).app (op V)) hr)
      erw [hm']
      exact ht V f hf ((leOfHom f).trans hW) (fun i ↦ A.val.map f.op (a i)))
  have hfirst := locally_surjective_generated_induction (A.val.exteriorPower (R := X.presheaf) r)
    (exteriorPower A r)
    ((PresheafOfModules.sheafificationAdjunction.{v}
      (𝟙 X.ringCatSheaf.obj)).unit.app (A.val.exteriorPower (R := X.presheaf) r))
    (by
      rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
      exact (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective)
    (fun W ↦ Set.range (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r))
    (fun W ↦ _root_.exteriorPower.ιMulti_span _ _ _)
    (fun W x ↦ ∀ hW : W ≤ U, ∀ y : (exteriorPower C s).val.obj (op W),
      d W hW (tmulSection x y) = e W hW (tmulSection x y))
    (by intro W hW y; simp only [zero_tmulSection, map_zero])
    (by
      intro W x y hx hy hW z
      rw [add_tmulSection (M := exteriorPower A r) (N := exteriorPower C s),
        map_add, map_add, hx hW z, hy hW z])
    (by
      intro W c x hx hW y
      rw [smul_tmulSection, (d W hW).map_smul,
        (e W hW).map_smul, hx hW y])
    (by intro W z hz; obtain ⟨a, rfl⟩ := hz; intro hW y; exact hsecond W y hW a)
    (by
      intro W x T hT ht hW y
      apply local_family_eq U d e hdmap hemap W hW _ T hT
      intro V f hf
      have hf' : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
      rw [← hf']
      erw [tmulSection_map (M := exteriorPower A r) (N := exteriorPower C s)]
      rw [hf']
      exact ht V f hf ((leOfHom f).trans hW) ((exteriorPower C s).val.map f.op y))
  let M := exteriorPower A r
  let N := exteriorPower C s
  let k := toSheafifyTensor M N ≫ (SheafOfModules.tensorObjIsoSheafification M N).inv.val
  have hk : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map k) := by
    have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor M N)) := by
      rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
      exact (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective
    dsimp only [k]
    rw [Functor.map_comp]
    have : IsIso ((PresheafOfModules.toPresheaf _).map
        (SheafOfModules.tensorObjIsoSheafification M N).inv.val) := by
      change IsIso ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf _).map
          (SheafOfModules.tensorObjIsoSheafification M N).inv)
      infer_instance
    infer_instance
  have hall := locally_surjective_generated_induction (M.val ⊗ N.val) (M ⊗ N) k hk
    (fun W ↦ {z | ∃ x y, x ⊗ₜ[X.presheaf.obj (op W)] y = z})
    (fun W ↦ TensorProduct.span_tmul_eq_top _ _ _)
    (fun W x ↦ ∀ hW : W ≤ U, d W hW x = e W hW x)
    (by intro W hW; simp only [map_zero])
    (by intro W x y hx hy hW; rw [map_add, map_add, hx hW, hy hW])
    (by
      intro W c x hx hW
      rw [(d W hW).map_smul, (e W hW).map_smul, hx hW])
    (by
      intro W z hz
      obtain ⟨x, y, rfl⟩ := hz
      intro hW
      exact hfirst W x hW y)
    (by
      intro W x T hT ht hW
      apply local_family_eq U d e hdmap hemap W hW x T hT
      intro V f hf
      exact ht V f hf ((leOfHom f).trans hW))
  funext W hW
  apply LinearMap.ext
  intro x
  exact hall W x hW

private theorem append_update {M : Type v} (r s : ℕ) (a : Fin r → M)
    (c : Fin s → M) (j : Fin s) (x : M) :
    Fin.append a (Function.update c j x) =
      Function.update (Fin.append a c) (j.natAdd r) x := by
  classical
  funext i
  refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) i
  · rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp at this; omega)]
    simp
  · simp [Function.update_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem wedge_update_add {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (r s : ℕ) (W : X.Opens) (a : Fin r → A.val.obj (op W))
    (c : Fin s → B.val.obj (op W)) (j : Fin s) (x y : B.val.obj (op W)) :
    wedge (M := B) (r := (r + s)) (U := W)
      (Fin.append (fun k ↦ f.val.app (op W) (a k)) (Function.update c j (x + y))) =
    wedge (M := B) (r := (r + s)) (U := W)
      (Fin.append (fun k ↦ f.val.app (op W) (a k)) (Function.update c j x)) +
    wedge (M := B) (r := (r + s)) (U := W)
      (Fin.append (fun k ↦ f.val.app (op W) (a k)) (Function.update c j y)) := by
  classical
  simp only [append_update, wedge]
  rw [AlternatingMap.map_update_add, map_add]

set_option backward.isDefEq.respectTransparency false in
private theorem wedge_lifts_eq {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (r n s : ℕ) (hr : n = r + s) [A.IsFiniteLocallyFreeOfRank r]
    (W : X.Opens) (a : Fin r → A.val.obj (op W))
    (c c' : Fin s → B.val.obj (op W))
    (hc : ∀ j, ∃ z : A.val.obj (op W), c j = c' j + f.val.app (op W) z) :
    wedge (M := B) (r := n) (U := W)
      (fun i ↦ Fin.append (fun k ↦ f.val.app (op W) (a k)) c (Fin.cast hr i)) =
    wedge (M := B) (r := n) (U := W)
      (fun i ↦ Fin.append (fun k ↦ f.val.app (op W) (a k)) c' (Fin.cast hr i)) := by
  classical
  subst n
  simp only [Fin.cast_refl]
  have h (T : Finset (Fin s)) :
      wedge (M := B) (r := (r + s)) (U := W)
        (Fin.append (fun k ↦ f.val.app (op W) (a k)) (T.piecewise c c')) =
      wedge (M := B) (r := (r + s)) (U := W)
        (Fin.append (fun k ↦ f.val.app (op W) (a k)) c') := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert j T hj ih =>
      obtain ⟨z, hz⟩ := hc j
      rw [Finset.piecewise_insert, hz, wedge_update_add]
      have hz0 := exteriorSheaf_rank_wedge_eq_zero f r (r + s) s rfl W a
        (Function.update (T.piecewise c c') j (f.val.app (op W) z)) j z
        (Function.update_self ..)
      simp only [Fin.cast_refl, id_eq] at hz0
      erw [hz0]
      rw [add_zero]
      have he : Function.update (T.piecewise c c') j (c' j) = T.piecewise c c' := by
        have hv : T.piecewise c c' j = c' j := by simp [Finset.piecewise, hj]
        rw [← hv, Function.update_eq_self]
      rw [he]
      exact ih
  simpa using h Finset.univ

set_option backward.isDefEq.respectTransparency false in
/-- Construct linear wedge maps without asserting invertibility or a rank for the quotient. -/
theorem determinant_split_linear_maps_exists {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b) :
    ∃! (d : ∀ (W : X.Opens), W ≤ U →
      (exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorPower S.X₂ r₂).val.obj (op W)),
      (∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) a)
          (wedge (M := S.X₃) (r := r₃) (U := W) b)) =
        wedge (M := S.X₂) (r := r₂) (U := W)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W hW (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) y,
        (exteriorPower S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.map
              (homOfLE hZW).op y)) := by
  let t := localEval U (biprod.inr ≫ e.inv)
  obtain ⟨d, hdwedge, hdmap⟩ :=
    exteriorTensor_local_pairing S.f r₁ r₂ r₃ hr U t
      (localEval_map U (biprod.inr ≫ e.inv))
  have hformula : ∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
      (b : Fin r₃ → S.X₃.val.obj (op W)),
      d W hW (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) a)
        (wedge (M := S.X₃) (r := r₃) (U := W) b)) =
      wedge (M := S.X₂) (r := r₂) (U := W)
        (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
          (fun j ↦ l W hW (b j)) (Fin.cast hr i)) := by
    intro W hW a b
    apply (hdwedge W hW a b).trans
    apply wedge_lifts_eq S.f r₁ r₂ r₃ hr W a
    intro j
    let z := t W hW (b j) - l W hW (b j)
    have hz : S.g.val.app (op W) z = 0 := by
      change S.g.val.app (op W) (t W hW (b j) - l W hW (b j)) = 0
      rw [map_sub, splitting_lift S.g U e hg, hl, sub_self]
    refine ⟨localEval U (e.hom ≫ biprod.fst) W hW z, ?_⟩
    rw [splitting_kernel S.f S.g U e hf hg W hW z hz]
    dsimp only [z]
    abel
  refine ⟨d, ⟨hformula, hdmap⟩, ?_⟩
  intro d' hd'
  apply local_wedge_family_ext S.X₁ S.X₃ (exteriorPower S.X₂ r₂) r₁ r₃ U
    d' d hd'.2 hdmap
  intro W hW a b
  exact (hd'.1 W hW a b).trans (hformula W hW a b).symm

end AlgebraicGeometry.Scheme.Modules

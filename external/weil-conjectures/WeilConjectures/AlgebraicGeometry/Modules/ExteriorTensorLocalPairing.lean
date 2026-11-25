/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.Modules.LocalBilinearSheafificationTensor

/-!
# Exterior pairing induced by a linear map on an open
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem restriction_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    {U V : X.Opensᵒᵖ} (g : U ⟶ V) (a : Fin n → M.val.obj U) :
    (M.val.exteriorPower (R := X.presheaf) n).map g
        (_root_.exteriorPower.ιMulti (X.presheaf.obj U) n a) =
      (_root_.exteriorPower.ιMulti _ n (fun i ↦ M.val.map g (a i)) :
        (M.val.exteriorPower (R := X.presheaf) n).obj V) :=
  _root_.PresheafOfModules.exteriorPower_map_ιMulti (R := X.presheaf) M.val n g a

set_option backward.isDefEq.respectTransparency false in
private theorem exterior_section_map {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    {W Z : X.Opens} (g : Z ⟶ W) (a : Fin n → M.val.obj (op W)) :
    (exteriorPower M n).val.map g.op (wedge (M := M) (r := n) (U := W) a) =
      wedge (M := M) (r := n) (U := Z) (fun i ↦ M.val.map g.op (a i)) :=
  wedge_map g a

private noncomputable def wedgeMul {R M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] (r s : ℕ) :
    (⋀[R]^r M) →ₗ[R] (⋀[R]^s M) →ₗ[R] (⋀[R]^(r + s) M) where
  toFun x :=
    { toFun := fun y ↦ ⟨x.val * y.val, by
        change x.val * y.val ∈ LinearMap.range (ExteriorAlgebra.ι R) ^ (r + s)
        rw [pow_add]
        exact Submodule.mul_mem_mul x.property y.property⟩
      map_add' := by intro y z; apply Subtype.ext; exact mul_add _ _ _
      map_smul' := by intro c y; apply Subtype.ext; exact mul_smul_comm _ _ _ }
  map_add' := by intro x y; ext z; exact add_mul _ _ _
  map_smul' := by intro c x; ext y; exact smul_mul_assoc _ _ _

private theorem wedgeMul_wedge {R M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] (r s : ℕ) (a : Fin r → M) (c : Fin s → M) :
    wedgeMul r s (_root_.exteriorPower.ιMulti R r a) (_root_.exteriorPower.ιMulti R s c) =
      _root_.exteriorPower.ιMulti R (r + s) (Fin.append a c) := by
  apply Subtype.ext
  exact ExteriorAlgebra.ιMulti_mul_ιMulti a c

private theorem wedgeMul_map_wedge {R A B C : Type v} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (r s : ℕ) (f : A →ₗ[R] B) (t : C →ₗ[R] B)
    (a : Fin r → A) (c : Fin s → C) :
    wedgeMul r s (_root_.exteriorPower.map r f (_root_.exteriorPower.ιMulti R r a))
      (_root_.exteriorPower.map s t (_root_.exteriorPower.ιMulti R s c)) =
      _root_.exteriorPower.ιMulti R (r + s) (Fin.append (fun i ↦ f (a i))
        (fun i ↦ t (c i))) := by
  rw [_root_.exteriorPower.map_apply_ιMulti, _root_.exteriorPower.map_apply_ιMulti,
    wedgeMul_wedge]
  rfl

private theorem exterior_pairing_naturality_of_generators
    {R S A C P A' C' P' : Type v} [CommRing R] [CommRing S]
    [AddCommGroup A] [Module R A] [AddCommGroup C] [Module R C]
    [AddCommGroup P] [Module R P] [AddCommGroup A'] [Module S A']
    [AddCommGroup C'] [Module S C'] [AddCommGroup P'] [Module S P']
    {ι κ : Type v} {a : ι → A} {c : κ → C} {σ : R →+* S}
    (ha : Submodule.span R (Set.range a) = ⊤)
    (hc : Submodule.span R (Set.range c) = ⊤)
    (l : A →ₛₗ[σ] A') (m : C →ₛₗ[σ] C') (k : P →ₛₗ[σ] P')
    (b : A →ₗ[R] C →ₗ[R] P) (b' : A' →ₗ[S] C' →ₗ[S] P')
    (h : ∀ i j, b' (l (a i)) (m (c j)) = k (b (a i) (c j))) (x : A) (y : C) :
    b' (l x) (m y) = k (b x y) := by
  have hfirst (i : ι) : (b' (l (a i))).comp m = k.comp (b (a i)) :=
    LinearMap.ext_on_range hc (h i)
  have hsecond : (b'.flip (m y)).comp l = k.comp (b.flip y) :=
    LinearMap.ext_on_range ha (fun i ↦ LinearMap.congr_fun (hfirst i) y)
  exact LinearMap.congr_fun hsecond x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A natural family of linear maps on subopens induces a natural exterior tensor pairing. -/
theorem exteriorTensor_local_pairing {X : Scheme.{v}} {A B C : X.Modules}
    (f : A ⟶ B) (r n s : ℕ) (hr : n = r + s) (U : X.Opens)
    (t : ∀ W : X.Opens, W ≤ U →
      C.val.obj (op W) →ₗ[X.presheaf.obj (op W)] B.val.obj (op W))
    (ht : ∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) b,
      B.val.map (homOfLE hZW).op (t W hW b) =
        t Z (hZW.trans hW) (C.val.map (homOfLE hZW).op b)) :
    ∃ d : ∀ W : X.Opens, W ≤ U →
      (exteriorPower A r ⊗ exteriorPower C s).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorPower B n).val.obj (op W),
      (∀ W hW (a : Fin r → A.val.obj (op W)) (b : Fin s → C.val.obj (op W)),
        d W hW (tmulSection (wedge (M := A) (r := r) (U := W) a)
          (wedge (M := C) (r := s) (U := W) b)) =
        wedge (M := B) (r := n) (U := W)
          (fun i ↦ Fin.append (fun j ↦ f.val.app (op W) (a j))
            (fun j ↦ t W hW (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) y,
        (exteriorPower B n).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorPower A r ⊗ exteriorPower C s).val.map (homOfLE hZW).op y)) := by
  subst n
  let η := (PresheafOfModules.sheafificationAdjunction.{v}
    (𝟙 X.ringCatSheaf.obj)).unit
  let b : ∀ W : X.Opens, W ≤ U →
      (A.val.exteriorPower (R := X.presheaf) r).obj (op W) →ₗ[X.presheaf.obj (op W)]
        (C.val.exteriorPower (R := X.presheaf) s).obj (op W) →ₗ[X.presheaf.obj (op W)]
          (exteriorPower B (r + s)).val.obj (op W) := fun W hW ↦
    (LinearMap.llcomp (X.presheaf.obj (op W)) _ _ _
      ((η.app ((B.val.exteriorPower (R := X.presheaf) (r + s)))).app (op W)).hom).comp
      (((wedgeMul r s).compl₂ (_root_.exteriorPower.map (R := X.presheaf.obj (op W)) s
        (t W hW))).comp
        (_root_.exteriorPower.map (R := X.presheaf.obj (op W)) r (f.val.app (op W)).hom))
  have hb (W : X.Opens) (hW : W ≤ U) (a : Fin r → A.val.obj (op W))
      (c : Fin s → C.val.obj (op W)) :
      b W hW (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r a)
        (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) s c) =
      wedge (M := B) (r := (r + s)) (U := W)
        (Fin.append (fun j ↦ f.val.app (op W) (a j)) (fun j ↦ t W hW (c j))) := by
    exact congrArg ((η.app (B.val.exteriorPower (R := X.presheaf) (r + s))).app (op W))
      (wedgeMul_map_wedge (R := X.presheaf.obj (op W)) r s
        (f.val.app (op W)).hom (t W hW) a c)
  have hbmap : ∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) (x y),
      b Z (hZW.trans hW) ((A.val.exteriorPower (R := X.presheaf) r).map (homOfLE hZW).op x)
        ((C.val.exteriorPower (R := X.presheaf) s).map (homOfLE hZW).op y) =
      (exteriorPower B (r + s)).val.map (homOfLE hZW).op (b W hW x y) := by
    intro W Z hW hZW x y
    let g := (homOfLE hZW).op
    have hpure (a : Fin r → A.val.obj (op W)) (c : Fin s → C.val.obj (op W)) :
        b Z (hZW.trans hW) ((A.val.exteriorPower (R := X.presheaf) r).map g
          (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r a))
          ((C.val.exteriorPower (R := X.presheaf) s).map g
            (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) s c)) =
        (exteriorPower B (r + s)).val.map g
          (b W hW (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r a)
            (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) s c)) := by
      rw [restriction_wedge A r g a, restriction_wedge C s g c]
      erw [hb Z (hZW.trans hW) (fun i ↦ A.val.map g (a i))
        (fun i ↦ C.val.map g (c i)), hb W hW a c]
      rw [exterior_section_map]
      apply congrArg (wedge (M := B) (r := (r + s)) (U := Z))
      funext i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · simp only [Fin.append_left]
        exact PresheafOfModules.naturality_apply f.val g (a j)
      · simp only [Fin.append_right]
        exact (ht W Z hW hZW (c j)).symm
    exact exterior_pairing_naturality_of_generators
      (_root_.exteriorPower.ιMulti_span (X.presheaf.obj (op W)) r (A.val.obj (op W)))
      (_root_.exteriorPower.ιMulti_span (X.presheaf.obj (op W)) s (C.val.obj (op W)))
      ((A.val.exteriorPower (R := X.presheaf) r).restrictₛₗ g)
      ((C.val.exteriorPower (R := X.presheaf) s).restrictₛₗ g)
      ((exteriorPower B (r + s)).val.restrictₛₗ g) (b W hW) (b Z (hZW.trans hW))
      hpure x y
  obtain ⟨d, hd, hdn⟩ := local_bilinear_sheafification_tensor_extension
    (A.val.exteriorPower (R := X.presheaf) r) (C.val.exteriorPower (R := X.presheaf) s)
    (exteriorPower B (r + s)) U b hbmap
  refine ⟨d, ?_, hdn⟩
  intro W hW a c
  exact (hd W hW (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) r a)
    (_root_.exteriorPower.ιMulti (X.presheaf.obj (op W)) s c)).trans (hb W hW a c)


end AlgebraicGeometry.Scheme.Modules

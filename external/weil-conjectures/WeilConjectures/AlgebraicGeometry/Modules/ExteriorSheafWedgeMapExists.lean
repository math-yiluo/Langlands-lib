/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension

/-!
# Wedging two exterior sheaves before quotient descent
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

private theorem wedge_bilinear_naturality {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (r s : ℕ)
    (b : ∀ U : X.Opensᵒᵖ,
      (A.val.exteriorPower (R := X.presheaf) r).obj U →ₗ[X.presheaf.obj U]
        (B.val.exteriorPower (R := X.presheaf) s).obj U →ₗ[X.presheaf.obj U]
          (exteriorPower B (r + s)).val.obj U)
    (hb : ∀ (U : X.Opensᵒᵖ) (a : Fin r → A.val.obj U) (c : Fin s → B.val.obj U),
      b U (_root_.exteriorPower.ιMulti (X.presheaf.obj U) r a)
        (_root_.exteriorPower.ιMulti (X.presheaf.obj U) s c) =
      wedge (M := B) (r := r + s) (U := U.unop)
        (Fin.append (fun j ↦ f.val.app U (a j)) c)) :
    ∀ {U V : X.Opensᵒᵖ} (g : U ⟶ V) (x y),
      b V ((A.val.exteriorPower (R := X.presheaf) r).map g x)
        ((B.val.exteriorPower (R := X.presheaf) s).map g y) =
      (exteriorPower B (r + s)).val.map g (b U x y) := by
  intro U V g x y
  have hpure (a : Fin r → A.val.obj U) (c : Fin s → B.val.obj U) :
      b V ((A.val.exteriorPower (R := X.presheaf) r).map g
        (_root_.exteriorPower.ιMulti (X.presheaf.obj U) r a))
        ((B.val.exteriorPower (R := X.presheaf) s).map g
          (_root_.exteriorPower.ιMulti (X.presheaf.obj U) s c)) =
      (exteriorPower B (r + s)).val.map g
        (b U (_root_.exteriorPower.ιMulti (X.presheaf.obj U) r a)
          (_root_.exteriorPower.ιMulti (X.presheaf.obj U) s c)) := by
    rw [restriction_wedge A r g a, restriction_wedge B s g c]
    erw [hb V (fun i ↦ A.val.map g (a i)) (fun i ↦ B.val.map g (c i)), hb U a c]
    let d := Fin.append (fun j ↦ f.val.app U (a j)) c
    change wedge _ = (exteriorPower B (r + s)).presheaf.map g (wedge d)
    erw [wedge_map g.unop d]
    apply congrArg (wedge (M := B) (r := r + s) (U := V.unop))
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [d, Fin.append_left]
      exact PresheafOfModules.naturality_apply f.val g (a j)
    · simp only [d, Fin.append_right]
      rfl
  have hfirst (a : Fin r → A.val.obj U) : ∀ y,
      b V ((A.val.exteriorPower (R := X.presheaf) r).map g
        (_root_.exteriorPower.ιMulti (X.presheaf.obj U) r a))
        ((B.val.exteriorPower (R := X.presheaf) s).map g y) =
      (exteriorPower B (r + s)).val.map g
        (b U (_root_.exteriorPower.ιMulti (X.presheaf.obj U) r a) y) := by
    intro y
    have hy : y ∈ Submodule.span (X.presheaf.obj U)
        (Set.range (_root_.exteriorPower.ιMulti (X.presheaf.obj U) s)) := by
      rw [_root_.exteriorPower.ιMulti_span]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨c, rfl⟩ := hy; exact hpure a c
    | zero => simp only [map_zero]
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
    | smul k y _ hy =>
      rw [PresheafOfModules.map_smul, (b V _).map_smul,
        (b U _).map_smul, PresheafOfModules.map_smul, hy]
      rfl
  have hx : x ∈ Submodule.span (X.presheaf.obj U)
      (Set.range (_root_.exteriorPower.ιMulti (X.presheaf.obj U) r)) := by
    rw [_root_.exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hfirst a y
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x z _ _ hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | smul k x _ hx =>
    rw [PresheafOfModules.map_smul, (b V).map_smul, LinearMap.smul_apply,
      (b U).map_smul, LinearMap.smul_apply, PresheafOfModules.map_smul, hx]
    rfl

-- Comparing the scheme and ring-sheaf scalar structures requires additional elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- For `f : A ⟶ B` and `t = r + s`, there is a morphism `⋀ʳ A ⊗ ⋀ˢ B ⟶ ⋀ᵗ B` sending
`(a₁ ∧ ⋯ ∧ a_r) ⊗ (c₁ ∧ ⋯ ∧ c_s)` to `f(a₁) ∧ ⋯ ∧ f(a_r) ∧ c₁ ∧ ⋯ ∧ c_s` on sections. -/
theorem exteriorSheaf_wedgeMap_exists {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (r s t : ℕ) (ht : t = r + s) :
    ∃ ψ : exteriorPower A r ⊗ exteriorPower B s ⟶ exteriorPower B t,
      ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
        (c : Fin s → B.val.obj (op U)),
        ψ.val.app (op U)
          (tmulSection (wedge (M := A) (r := r) (U := U) a) (wedge (M := B) (r := s) (U := U) c)) =
          wedge (M := B) (r := t) (U := U)
            (fun i ↦ Fin.append (fun j ↦ f.val.app (op U) (a j)) c (Fin.cast ht i)) := by
  subst t
  let : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) :=
    Presheaf.isLocallyInjective_of_injective _ _ (fun _ ↦ Function.injective_id)
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) :=
    Presheaf.isLocallySurjective_of_surjective _ _ (fun _ ↦ Function.surjective_id)
  let η := (PresheafOfModules.sheafificationAdjunction.{v}
    (𝟙 X.ringCatSheaf.obj)).unit
  let b : ∀ U : X.Opensᵒᵖ,
      (A.val.exteriorPower (R := X.presheaf) r).obj U →ₗ[X.presheaf.obj U]
        (B.val.exteriorPower (R := X.presheaf) s).obj U →ₗ[X.presheaf.obj U]
          (exteriorPower B (r + s)).val.obj U := fun U ↦
    (LinearMap.llcomp (X.presheaf.obj U) _ _ _
      ((η.app ((B.val.exteriorPower (R := X.presheaf) (r + s)))).app U).hom).comp
      ((wedgeMul r s).comp
        (_root_.exteriorPower.map (R := X.presheaf.obj U) r (f.val.app U).hom))
  have hb (U : X.Opensᵒᵖ) (a : Fin r → A.val.obj U)
      (c : Fin s → B.val.obj U) :
      b U (_root_.exteriorPower.ιMulti (X.presheaf.obj U) r a)
        (_root_.exteriorPower.ιMulti (X.presheaf.obj U) s c) =
      wedge (M := B) (r := (r + s)) (U := U.unop)
        (Fin.append (fun j ↦ f.val.app U (a j)) c) := by
    change (η.app ((B.val.exteriorPower (R := X.presheaf) (r + s)))).app U
      (wedgeMul r s
        (_root_.exteriorPower.map (R := X.presheaf.obj U) r (f.val.app U).hom
          (_root_.exteriorPower.ιMulti (X.presheaf.obj U) r a))
        (_root_.exteriorPower.ιMulti (X.presheaf.obj U) s c)) = _
    rw [_root_.exteriorPower.map_apply_ιMulti, wedgeMul_wedge]
    rfl
  obtain ⟨β, ⟨hβ, hβunit⟩, _⟩ :=
    PresheafOfModules.existsUnique_bilinear_sheafification_extension
      X.presheaf X.sheaf (𝟙 X.ringCatSheaf.obj)
      (A.val.exteriorPower (R := X.presheaf) r) (B.val.exteriorPower (R := X.presheaf) s)
      (exteriorPower B (r + s)) b (wedge_bilinear_naturality f r s b hb)
  obtain ⟨ψ, hψ, _⟩ := SheafOfModules.tensor_bilinear_universal X.sheaf
    (exteriorPower A r) (exteriorPower B s) (exteriorPower B (r + s)) β hβ
  refine ⟨ψ, ?_⟩
  intro U a c
  exact (hψ (op U) (wedge (M := A) (r := r) (U := U) a)
    (wedge (M := B) (r := s) (U := U) c)).trans
      ((hβunit (op U) (_root_.exteriorPower.ιMulti (X.presheaf.obj (op U)) r a)
        (_root_.exteriorPower.ιMulti (X.presheaf.obj (op U)) s c)).trans (hb (op U) a c))

end AlgebraicGeometry.Scheme.Modules

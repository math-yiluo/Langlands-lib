/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Finite-product coordinates after an additive functor

Source: Stacks Project, Tag 02KE, the termwise Čech calculation. -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

private theorem additive_pi_sections_bijective {R : Type u} [CommRing R]
    {S : Scheme.{u}} {I : Type} [Finite I] (N : I → ModuleCat.{u} R)
    (H : ModuleCat.{u} R ⥤ S.Modules) [H.Additive] (B : S.Opens) :
    Function.Bijective (fun s : Γ(H.obj (ModuleCat.of R (∀ i, N i)), B) ↦
      fun i ↦ (H.map (ModuleCat.ofHom (LinearMap.proj i))).app B s) := by
  classical
  let E : ModuleCat.{u} R ⥤ ModuleCat.{u} Γ(S, B) :=
    H ⋙ SheafOfModules.evaluation S.ringCatSheaf (op B)
  have : E.Additive := by
    constructor
    intro M N f g
    change (H.map (f + g)).val.app (op B) = _
    rw [H.map_add]
    rfl
  let h := isLimitFanMkObjOfIsLimit E N
    (fun i ↦ ModuleCat.ofHom (LinearMap.proj i)) (ModuleCat.productConeIsLimit N)
  let e := h.conePointUniqueUpToIso
    (ModuleCat.productConeIsLimit (fun i ↦ E.obj (N i)))
  have he (s : Γ(H.obj (ModuleCat.of R (∀ i, N i)), B)) (i : I) :
      e.hom s i = (H.map (ModuleCat.ofHom (LinearMap.proj i))).app B s := by
    have hh := h.conePointUniqueUpToIso_hom_comp
      (ModuleCat.productConeIsLimit (fun i ↦ E.obj (N i))) (Discrete.mk i)
    exact congrArg (fun f ↦ f.hom s) hh
  have hf : (fun s : Γ(H.obj (ModuleCat.of R (∀ i, N i)), B) ↦
      fun i ↦ (H.map (ModuleCat.ofHom (LinearMap.proj i))).app B s) =
      (fun s ↦ e.hom s) := by
    funext s i
    exact (he s i).symm
  rw [hf]
  exact e.toLinearEquiv.bijective

/-- An additive functor applied to the extended alternating section complex has
finite-product coordinates. The differential in these coordinates is the signed sum
of the images of the coefficient restriction maps.
Source: Stacks Project, Tag 02KE, termwise finite Čech calculation; the definitions of
alternatingCechComplex and extension by zero.
(blueprint: lem-pc-additive-alternating-cech-coordinates).

Proof: For each p, the explicit function module alternatingCechTerms is the finite
product of the coefficient modules. An additive functor preserves finite biproducts,
hence finite products, including the empty product. Evaluate the resulting product
isomorphism on B; sections preserve products. Precompose with the image of extendXIso
at p to obtain a. Each coordinate is the section map of the image of the explicit
projection. Hence it commutes with restrictions of B and is linear over its section
ring. Expand alternatingCechDifferential as its finite signed sum of a coefficient
restriction composed with a projection. Additivity preserves that sum and its integer
scalars; the projection equation gives the displayed differential formula. The equation
extend_d_eq transports this calculation to integer degrees. -/
theorem additive_alternatingCech_coordinates {Y S : Scheme.{u}} {r : ℕ}
    (V : Fin r → Y.Opens)
    (G : Y.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(Y, ⊤))
    (H : ModuleCat.{u} Γ(Y, ⊤) ⥤ S.Modules) [H.Additive] :
    let L := (H.mapHomologicalComplex _).obj
      ((alternatingCechComplex V G).extend ComplexShape.embeddingUpNat)
    ∃ e : ∀ (p : ℕ) (B : S.Opens), Γ(L.X (p : ℤ), B) ≃+
        (∀ t : Fin (p + 1) ↪o Fin r,
          Γ(H.obj (G.obj (op (alternatingCechIntersection V t))), B)),
      (∀ (p : ℕ) {B C : S.Opens} (i : B ⟶ C)
        (s : Γ(L.X (p : ℤ), C)) (t : Fin (p + 1) ↪o Fin r),
        e p B ((L.X (p : ℤ)).presheaf.map i.op s) t =
          (H.obj (G.obj (op (alternatingCechIntersection V t)))).presheaf.map i.op
            (e p C s t)) ∧
      (∀ (p : ℕ) (B : S.Opens) (b : Γ(S, B))
        (s : Γ(L.X (p : ℤ), B)) (t : Fin (p + 1) ↪o Fin r),
        e p B (b • s) t = b • e p B s t) ∧
      (∀ (p : ℕ) (B : S.Opens) (s : Γ(L.X (p : ℤ), B))
        (t : Fin (p + 2) ↪o Fin r),
        e (p + 1) B ((L.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B s) t =
          ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
            (H.map (G.map (homOfLE
              (alternatingCechIntersection_face_le V p t j)).op)).app B
                (e p B s ((Fin.succAboveOrderEmb j).trans t))) := by
  classical
  let C := alternatingCechComplex V G
  let L := (H.mapHomologicalComplex _).obj (C.extend ComplexShape.embeddingUpNat)
  let A (p : ℕ) : L.X (p : ℤ) ≅ H.obj (C.X p) :=
    H.mapIso (C.extendXIso ComplexShape.embeddingUpNat (i := p) rfl)
  let q (p : ℕ) (t : Fin (p + 1) ↪o Fin r) :
      C.X p ⟶ G.obj (op (alternatingCechIntersection V t)) :=
    ModuleCat.ofHom (LinearMap.proj t)
  let m (p : ℕ) (t : Fin (p + 1) ↪o Fin r) := (A p).hom ≫ H.map (q p t)
  let e (p : ℕ) (B : S.Opens) : Γ(L.X (p : ℤ), B) ≃+
      (∀ t : Fin (p + 1) ↪o Fin r,
        Γ(H.obj (G.obj (op (alternatingCechIntersection V t))), B)) :=
    AddEquiv.ofBijective
      (AddMonoidHom.pi fun t ↦ ((m p t).app B).hom)
      ((additive_pi_sections_bijective
        (fun t : Fin (p + 1) ↪o Fin r ↦ G.obj (op (alternatingCechIntersection V t)))
        H B).comp (ConcreteCategory.bijective_of_isIso ((A p).hom.app B)))
  refine ⟨e, ?_, ?_, ?_⟩
  · intro p B D i s t
    change (m p t).app B ((L.X (p : ℤ)).presheaf.map i.op s) = _
    exact congrArg (fun a ↦ a s) ((m p t).mapPresheaf.naturality i.op)
  · intro p B b s t
    exact Hom.app_smul (m p t) b s
  · intro p B s t
    have hq : C.d p (p + 1) ≫ q (p + 1) t =
        ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
          (q p ((Fin.succAboveOrderEmb j).trans t) ≫
            G.map (homOfLE (alternatingCechIntersection_face_le V p t j)).op) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp only [C, alternatingCechComplex, CochainComplex.of_d]
      change (∀ q : Fin (p + 1) ↪o Fin r, G.obj (op (alternatingCechIntersection V q))) at x
      change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        (G.map (homOfLE (alternatingCechIntersection_face_le V p t j)).op).hom.comp
          (LinearMap.proj ((Fin.succAboveOrderEmb j).trans t))) x = _
      simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_comp,
        LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
      rfl
    have hd : L.d (p : ℤ) ((p + 1 : ℕ) : ℤ) ≫ m (p + 1) t =
        ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
          (m p ((Fin.succAboveOrderEmb j).trans t) ≫
            H.map (G.map (homOfLE (alternatingCechIntersection_face_le V p t j)).op)) := by
      change H.map ((C.extend ComplexShape.embeddingUpNat).d _ _) ≫ _ = _
      rw [C.extend_d_eq ComplexShape.embeddingUpNat (i := p) (j := p + 1)
        (i' := (p : ℤ)) (j' := ((p + 1 : ℕ) : ℤ)) rfl rfl]
      simp only [Functor.map_comp, m, Category.assoc]
      change (A p).hom ≫ H.map (C.d p (p + 1)) ≫
        (A (p + 1)).inv ≫ (A (p + 1)).hom ≫ H.map (q (p + 1) t) = _
      rw [Iso.inv_hom_id_assoc, ← H.map_comp, hq, H.map_sum]
      simp only [Functor.map_zsmul, Preadditive.comp_sum, Preadditive.comp_zsmul,
        Functor.map_comp]
    change (m (p + 1) t).app B ((L.d _ _).app B s) = _
    change ((L.d _ _ ≫ m (p + 1) t).app B) s = _
    rw [hd]
    let ev : (L.X (p : ℤ) ⟶ H.obj (G.obj (op (alternatingCechIntersection V t)))) →+
        (Γ(L.X (p : ℤ), B) →+ Γ(H.obj (G.obj
          (op (alternatingCechIntersection V t))), B)) :=
      { toFun := fun z ↦ (z.app B).hom
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    change ev (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      (m p ((Fin.succAboveOrderEmb j).trans t) ≫
        H.map (G.map (homOfLE (alternatingCechIntersection_face_le V p t j)).op))) s = _
    simp only [map_sum, map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply]
    rfl


end AlgebraicGeometry.Scheme.Modules

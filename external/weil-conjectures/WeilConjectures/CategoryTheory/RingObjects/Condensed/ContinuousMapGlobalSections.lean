/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections

/-!
# The global sections of the condensed ring `C(-, T)`

For a topological commutative ring `T`, the constant maps give a ring homomorphism
`T →+* Γ C(-, T)` to the global sections of the condensed ring `C(-, T)`
(`Profinite.continuousMapConstRingHom`), which is surjective
(`Profinite.continuousMapConstRingHom_surjective`): a global section is determined by its value
at the point.

The constant global sections of sheafified presheaves of rings are natural with respect to
morphisms of sheaves of rings (`CategoryTheory.Sheaf.Γ_map_ringHomΓSheafCompose`).
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory MonObj Opposite Limits

namespace CategoryTheory.Sheaf

attribute [local instance] Sheaf.monoidalCategory

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasSheafify J Ab.{w}]
  [(J.W (A := Ab.{w})).IsMonoidal] [J.HasSheafCompose (forget₂ RingCat.{w} Ab.{w})]

/-- The constant global sections of sheaves of rings are natural: a morphism of sheaves of rings
`g : S₁ ⟶ S₂` sending the constant section `φ₁ X r` to the constant section `φ₂ X r'` sends the
global section `r` of `S₁` to the global section `r'` of `S₂`. -/
lemma Γ_map_ringHomΓSheafCompose {S₁ S₂ : Sheaf J RingCat.{w}} (g : S₁ ⟶ S₂)
    {R R' : Type*} [Ring R] [Ring R'] (φ₁ : ∀ X, R →+* S₁.obj.obj X)
    (hφ₁ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R), S₁.obj.map f (φ₁ X r) = φ₁ Y r)
    (φ₂ : ∀ X, R' →+* S₂.obj.obj X)
    (hφ₂ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R'), S₂.obj.map f (φ₂ X r) = φ₂ Y r)
    {r : R} {r' : R'} (h : ∀ X, g.hom.app X (φ₁ X r) = φ₂ X r') :
    Γ.map ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).map g)
        (ringHomΓSheafCompose J S₁ φ₁ hφ₁ r) =
      ringHomΓSheafCompose J S₂ φ₂ hφ₂ r' := by
  ext1
  refine hom_ext_of_ε_comp ?_
  rw [Γ.map_hom, Functor.map_comp, ← Category.assoc, ε_comp_ringHomΓSheafCompose_hom,
    ε_comp_ringHomΓSheafCompose_hom]
  ext X n
  have key : g.hom.app X ((n.down : S₁.obj.obj X) * φ₁ X r) =
      (n.down : S₂.obj.obj X) * φ₂ X r' := by
    rw [map_mul, map_intCast, h]
  exact key

end CategoryTheory.Sheaf

namespace Profinite

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- The constant maps `S → T`, as sections of the condensed ring `C(-, T)` over `S`. -/
noncomputable def continuousMapConstSectionRingHom (S : Profinite.{u}ᵒᵖ) :
    T →+* (continuousMapRingPresheaf.{u} T).obj S where
  toFun t := ULift.up (ContinuousMap.const _ t)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The constant global sections of the condensed ring `C(-, T)`: the ring homomorphism
`T →+* Γ C(-, T)` sending `t` to the global section `1 ↦ t`. -/
noncomputable def continuousMapConstRingHom : T →+* Γ (continuousMapRingObj.{u} T) :=
  Sheaf.ringHomΓSheafCompose (coherentTopology Profinite.{u}) (continuousMapRingSheaf T)
    (continuousMapConstSectionRingHom T) fun _ _ ↦ rfl

/-- Every global section of the condensed ring `C(-, T)` is constant. -/
theorem continuousMapConstRingHom_surjective :
    Function.Surjective (continuousMapConstRingHom.{u} T) := by
  intro x
  let adj := sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}
  let x' := adj.homEquiv _ _
    (inv (Functor.LaxMonoidal.ε (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
      ≫ x.hom)
  let b := x'.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)
  refine ⟨b.down PUnit.unit, ?_⟩
  have hx : x' = (Functor.ringHomΓCompForget₂ (continuousMapRingSheaf T).obj
      (continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl) (b.down PUnit.unit)).hom := by
    ext S n
    obtain ⟨m⟩ := n
    have key : x'.app S (ULift.up 1) = (continuousMapRingObj T).obj.map
        (isTerminalPUnit.from S.unop).op b :=
      NatTrans.naturality_apply x' (isTerminalPUnit.from S.unop).op (ULift.up 1)
    have hm : (ULift.up m : ULift.{u + 1} ℤ) = m • ULift.up 1 := by
      ext
      simp
    refine (congrArg (x'.app S) hm).trans ?_
    rw [map_zsmul, key]
    exact (zsmul_eq_mul (α := (continuousMapRingPresheaf T).obj S) _ m).trans rfl
  ext1
  rw [continuousMapConstRingHom, Sheaf.ringHomΓSheafCompose, RingHom.comp_apply,
    RingHom.comp_apply, Γ.map_hom, Γ.mapFunctor_hom, ← hx, Category.assoc,
    Sheaf.sheafifyRingPresheafIso, asIso_hom, ← Adjunction.homEquiv_counit,
    Equiv.symm_apply_apply, IsIso.hom_inv_id_assoc]

end Profinite

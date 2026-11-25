/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapMulLeft
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# `F̲` is a finite free `E̲`-module

Let `ℓ` be a prime and `E ≤ F` finite subextensions of `ℚ̄_ℓ / ℚ_ℓ`. For a basis `b₁, …, bₙ` of
`F` over `E`, the map `E̲ⁿ ⟶ F̲`, `(xᵢ) ↦ ∑ xᵢ bᵢ`, is an isomorphism of condensed abelian groups
(`Profinite.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul`): its inverse is given
by the coordinates, which are continuous since `F` is a finite-dimensional `ℚ_ℓ`-vector space.
Here the multiplication by `bᵢ` is the action of the constant global section `bᵢ` of `F̲` on the
regular module (`Profinite.globalSmul_continuousMapConstRingHom`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace Profinite

section Coordinates

variable {T T' : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [TopologicalSpace T']
  [CommRing T'] [IsTopologicalRing T']

/-- Postcomposition with a continuous additive map `g : T →+ T'`, as a morphism of condensed
abelian groups `C(-, T) ⟶ C(-, T')`. -/
noncomputable def continuousMapRingObjAddMap (g : T →+ T') (hg : Continuous g) :
    continuousMapRingObj.{u} T ⟶ continuousMapRingObj T' :=
  ⟨{ app _ := AddCommGrpCat.ofHom
        { toFun a := ULift.up ⟨fun s ↦ g (a.down s), hg.comp a.down.continuous⟩
          map_zero' := ULift.ext (ContinuousMap.ext fun _ ↦ map_zero g)
          map_add' a b :=
            ULift.ext (ContinuousMap.ext fun s ↦ map_add g (a.down s) (b.down s)) }
     naturality _ _ _ := rfl }⟩

open _root_.PadicAlgCl

attribute [local instance] Abelian.hasFiniteBiproducts

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (hF : E ≤ F)

lemma exists_isIso_biproductDesc_padicSubfieldRingObjMap_mulLeft :
    ∃ (n : ℕ) (b : Fin n → F), IsIso (biproduct.desc fun i ↦
      padicSubfieldRingObjMap ℓ hF ≫ continuousMapRingObjMulLeft F (b i) :
        ⨁ (fun _ : Fin n ↦ continuousMapRingObj.{u} E) ⟶ continuousMapRingObj F) := by
  let : Algebra E F := (IntermediateField.inclusion hF).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[ℓ] E F := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : FiniteDimensional E F := FiniteDimensional.right ℚ_[ℓ] E F
  let b := Module.finBasis E F
  let c (i : Fin (Module.finrank E F)) : continuousMapRingObj.{u} F ⟶ continuousMapRingObj E :=
    continuousMapRingObjAddMap (b.coord i).toAddMonoidHom
      ((b.coord i).restrictScalars ℚ_[ℓ]).continuous_of_finiteDimensional
  refine ⟨_, fun i ↦ b i, ⟨biproduct.lift c, ?_, ?_⟩⟩
  · refine biproduct.hom_ext' _ _ fun j ↦ biproduct.hom_ext _ _ fun k ↦ ?_
    simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id,
      biproduct.ι_π]
    split_ifs with h
    · subst h
      rw [eqToHom_refl]
      ext S a
      apply ULift.ext
      refine ContinuousMap.ext fun s ↦ ?_
      change b.coord j (b j * algebraMap E F (a.down s)) = a.down s
      rw [mul_comm, ← Algebra.smul_def]
      simp
    · ext S a
      apply ULift.ext
      refine ContinuousMap.ext fun s ↦ ?_
      change b.coord k (b j * algebraMap E F (a.down s)) = 0
      rw [mul_comm, ← Algebra.smul_def]
      simp [h]
  · rw [biproduct.lift_desc]
    ext S a
    have h₁ := (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
      (evaluation _ _).obj S).map_sum (fun j ↦ c j ≫ padicSubfieldRingObjMap ℓ hF ≫
        continuousMapRingObjMulLeft F (b j)) Finset.univ
    refine ULift.ext (ContinuousMap.ext fun s ↦ ?_)
    let ev : (continuousMapRingObj.{u} F).obj.obj S →+ F :=
      { toFun y := (show ULift.{u + 1} C(S.unop, F) from y).down s
        map_zero' := rfl
        map_add' _ _ := rfl }
    have h₂ := congrArg (fun φ ↦ ev (AddCommGrpCat.homAddEquiv φ a)) h₁
    simp only [map_sum, AddMonoidHom.finsetSum_apply] at h₂
    refine h₂.trans ?_
    change ∑ j, b j * algebraMap E F (b.coord j (a.down s)) = a.down s
    simp only [mul_comm (b _), ← Algebra.smul_def, Module.Basis.coord_apply]
    exact b.sum_repr _

/-- **`F̲` is a finite free `E̲`-module**: for a basis `b` of `F` over `E`, the map `E̲ⁿ ⟶ F̲`,
`(xᵢ) ↦ ∑ xᵢ bᵢ`, is an isomorphism. -/
lemma exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul :
    ∃ (n : ℕ) (b : Fin n → F), IsIso (biproduct.desc fun i ↦
      padicSubfieldRingObjMap ℓ hF ≫ Mod.globalSmul (continuousMapConstRingHom F (b i)).hom
        (Mod.regular (continuousMapRingObj F)) :
        ⨁ (fun _ : Fin n ↦ continuousMapRingObj.{u} E) ⟶ continuousMapRingObj F) := by
  obtain ⟨n, b, h⟩ := exists_isIso_biproductDesc_padicSubfieldRingObjMap_mulLeft ℓ hF
  refine ⟨n, b, ?_⟩
  simpa only [globalSmul_continuousMapConstRingHom] using h

end Coordinates

end Profinite

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Fundamental groups of essentially small Galois categories

For a fibre functor `F` on a Galois category `C`, any fundamental group `G` of `F` is isomorphic
as a topological group to `Aut F` (`CategoryTheory.PreGaloisCategory.toAutContinuousMulEquiv`).
If `C` is essentially small, then `Aut F` is small, and transporting it along `Shrink` gives a
profinite fundamental group of `F` in the universe of the fibres
(`CategoryTheory.PreGaloisCategory.exists_isFundamentalGroup`).
-/

@[expose] public section

universe u₁ u₂ w

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

/-- The automorphism group of a functor from an essentially small category to finite sets is
small: an automorphism is determined by its components on a small model of the source. -/
lemma small_aut [EssentiallySmall.{w} C] : Small.{w} (Aut F) := by
  let e := equivSmallModel.{w} C
  let φ : Aut F → ∀ X : SmallModel.{w} C, Aut (F.obj (e.inverse.obj X)) :=
    fun σ X ↦ .of (σ.asIso.app _)
  refine small_of_injective (f := φ) fun σ τ h ↦ ?_
  refine Aut.ext (Iso.ext (NatTrans.ext (funext fun P ↦ ?_)))
  have hP := congr_arg (fun ρ ↦ (ρ (e.functor.obj P)).asIso.hom) h
  rw [← cancel_mono (F.map (e.unitIso.hom.app P)), ← NatTrans.naturality,
    ← NatTrans.naturality]
  exact congrArg (F.map (e.unitIso.hom.app P) ≫ ·) hP

variable [GaloisCategory C] [FiberFunctor F]

/-- The isomorphism of topological groups between a fundamental group `G` of a fibre functor `F`
and the automorphism group of `F`. -/
noncomputable def toAutContinuousMulEquiv (G : Type*) [Group G] [∀ X, MulAction G (F.obj X)]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup F G] :
    G ≃ₜ* Aut F :=
  { toAutMulEquiv F G with
    continuous_toFun := (toAutMulEquiv_isHomeomorph F G).continuous
    continuous_invFun := (toAutMulEquiv_isHomeomorph F G).homeomorph.symm.continuous }

/-- A fibre functor on an essentially small Galois category has a profinite fundamental group in
the universe of its fibres, obtained by shrinking `Aut F`. -/
theorem exists_isFundamentalGroup [EssentiallySmall.{w} C] :
    ∃ (G : ProfiniteGrp.{w}) (_ : ∀ X, MulAction G (F.obj X)), IsFundamentalGroup F G := by
  have := small_aut F
  let A := Aut F
  let e : Shrink.{w} A ≃* A := Shrink.mulEquiv
  let _ : TopologicalSpace (Shrink.{w} A) := .induced e inferInstance
  let h : Shrink.{w} A ≃ₜ A := e.toEquiv.toHomeomorphOfIsInducing ⟨rfl⟩
  let f : Shrink.{w} A ≃ₜ* A :=
    { toMulEquiv := e, continuous_toFun := h.continuous, continuous_invFun := h.symm.continuous }
  have : IsTopologicalGroup (Shrink.{w} A) :=
    { continuous_mul := by
        rw [h.isInducing.continuous_iff]
        have : (fun p : Shrink.{w} A × Shrink.{w} A ↦ e (p.1 * p.2)) =
            fun p ↦ e p.1 * e p.2 := funext fun p ↦ map_mul e _ _
        change Continuous fun p : Shrink.{w} A × Shrink.{w} A ↦ e (p.1 * p.2)
        rw [this]
        exact (h.continuous.comp continuous_fst).mul (h.continuous.comp continuous_snd)
      continuous_inv := by
        rw [h.isInducing.continuous_iff]
        have : (fun p : Shrink.{w} A ↦ e p⁻¹) = fun p ↦ (e p)⁻¹ :=
          funext fun p ↦ map_inv e _
        change Continuous fun p : Shrink.{w} A ↦ e p⁻¹
        rw [this]
        exact h.continuous.inv }
  let G := ProfiniteGrp.ofContinuousMulEquiv (G := ProfiniteGrp.of A) f.symm
  let _ (X : C) : MulAction G (F.obj X) := MulAction.compHom _ (e : Shrink.{w} A →* A)
  refine ⟨G, inferInstance, ?_⟩
  have hsmul (g : G) (X : C) (x : F.obj X) : g • x = e g • x := rfl
  exact
    { naturality g _ _ f x := by
        simp only [hsmul]
        exact IsNaturalSMul.naturality (e g) f x
      transitive_of_isGalois X _ := by
        refine ⟨fun x y ↦ ?_⟩
        obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq A x y
        refine ⟨e.symm σ, ?_⟩
        change e (e.symm σ) • x = y
        rwa [MulEquiv.apply_symm_apply]
      continuous_smul X := by
        refine ⟨?_⟩
        change Continuous fun p : G × F.obj X ↦ e p.1 • p.2
        have : Continuous fun p : G × F.obj X ↦ (e p.1, p.2) :=
          (h.continuous.comp continuous_fst).prodMk continuous_snd
        exact (continuousSMul_aut_fiber F X).continuous_smul.comp this
      non_trivial' g hg := by
        have := IsFundamentalGroup.non_trivial (F := F) (e g) fun X x ↦ hg X x
        exact e.injective (this.trans (map_one e).symm) }

/-- A continuous homomorphism `ρ : H →* G` from a compact group to a fundamental group `G` of a
fibre functor `F` is surjective as soon as `H` acts, through `ρ`, transitively on the fibres of
the Galois objects: `H` acting through `ρ` is then naturally and continuously on the fibres, so
`H ⟶ Aut F` is surjective, and it factors through `G ≃ Aut F`. -/
theorem surjective_of_forall_exists_smul_eq (G : Type*) [Group G] [∀ X, MulAction G (F.obj X)]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup F G]
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (ρ : H →* G) (hρ : Continuous ρ)
    (h : ∀ (X : C) [IsGalois X] (x y : F.obj X), ∃ g : H, ρ g • x = y) :
    Function.Surjective ρ := by
  let (X : C) : MulAction H (F.obj X) := MulAction.compHom _ ρ
  have hsmul (g : H) (X : C) (x : F.obj X) : g • x = ρ g • x := rfl
  have : IsNaturalSMul F H := ⟨fun g X Y f x ↦ by
    simp only [hsmul]
    exact IsNaturalSMul.naturality (ρ g) f x⟩
  have hc (X : C) : ContinuousSMul H (F.obj X) := by
    have : ContinuousSMul G (F.obj X) := IsFundamentalGroup.continuous_smul X
    refine ⟨?_⟩
    change Continuous fun p : H × F.obj X ↦ ρ p.1 • p.2
    exact (hρ.comp continuous_fst).smul continuous_snd
  have hs := toAut_surjective_of_isPretransitive F H fun X _ ↦ ⟨fun x y ↦ h X x y⟩
  intro g
  obtain ⟨g', hg'⟩ := hs (toAut F G g)
  refine ⟨g', (toAut_bijective F G).1 ?_⟩
  rw [← hg']
  ext X x
  rw [toAut_hom_app_apply, toAut_hom_app_apply]
  rfl

end CategoryTheory.PreGaloisCategory

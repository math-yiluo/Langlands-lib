/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.ProperIndConstructibleBoundedBelow
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientIndDerivedSums
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.SmoothPurity.TruncationsAndHomotopyColimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.ModuleObjectPostnikovRoos
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.RoosEventuallyConstant

/-!
# Proper direct image of arbitrary ind-constructible complexes

The two statements retain the actual condensed coefficients, respectively a finite
subextension of ℚ_ℓ and the finite-subextension-valued condensed algebraic closure.
IndCons is the recorded replete small filtered-colimit closure of finite constant-model
constructible modules. Dic is expressed as this property of every cohomology object.
The stabilization arrow is the cohomology of the direct image of the canonical truncation
projection, without replacing it by an unspecified isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

private theorem truncation_step_isIso
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]
    (P : ObjectProperty (DerivedCategory C))
    (hP : ∀ L, P L → ∀ j : ℤ,
      P ((DerivedCategory.TStructure.t.truncLE j).obj L) ∧
      P ((DerivedCategory.TStructure.t.truncGE j).obj L))
    (c : ℤ)
    (hF : ∀ L, P L → ∀ a : ℤ, L.IsGE a →
      ∀ b : ℤ, L.IsLE b → (F.obj L).IsLE (b + c))
    (K : DerivedCategory C) (hK : P K) (m q l : ℤ)
    (hl : -m + 1 = l) (hm : -m + c < q) :
    IsIso ((DerivedCategory.homologyFunctor D q).map (F.map
      ((DerivedCategory.TStructure.t.natTransTruncGEOfLE (-m) l
        (by omega)).app K))) := by
  subst l
  let t := DerivedCategory.TStructure.t (C := C)
  let A := (t.truncGE (-m)).obj K
  let B := (t.truncLE (-m)).obj A
  have hA : P A := (hP K hK (-m)).2
  have hB : P B := (hP A hA (-m)).1
  have hBge : B.IsGE (-m) := by dsimp [B, A]; infer_instance
  have hBle : B.IsLE (-m) := by dsimp [B]; infer_instance
  have hFB : (F.obj B).IsLE (-m + c) := hF B hB (-m) hBge (-m) hBle
  let T := F.mapTriangle.obj ((t.triangleLEGE (-m) (-m + 1) (by omega)).obj A)
  have hT : T ∈ distTriang _ :=
    F.map_distinguished _ (t.triangleLEGE_distinguished (-m) (-m + 1) (by omega) A)
  have hi : IsIso ((DerivedCategory.homologyFunctor D q).map
      (F.map ((t.truncGEπ (-m + 1)).app A))) :=
    DerivedCategory.isIso_homologyMap_mor₂ T hT q (q + 1) rfl
      (DerivedCategory.isZero_of_isLE (F.obj B) (-m + c) q hm)
      (DerivedCategory.isZero_of_isLE (F.obj B) (-m + c) (q + 1) (by omega))
  have hmap := t.isIso_truncGE_map_truncGEπ_app (-m + 1) (-m) (by omega) K
  let e : (t.truncGE (-m + 1)).obj A ≅ (t.truncGE (-m + 1)).obj K :=
    (asIso ((t.truncGE (-m + 1)).map ((t.truncGEπ (-m)).app K))).symm
  have hg : (t.truncGEπ (-m + 1)).app A ≫ e.hom =
      (t.natTransTruncGEOfLE (-m) (-m + 1) (by omega)).app K := by
    have : t.IsGE ((t.truncGE (-m + 1)).obj K) (-m) :=
      t.isGE_of_ge _ (-m) (-m + 1) (by omega)
    apply t.from_truncGE_obj_ext
    dsimp [e, A]
    have hn := (t.truncGEπ (-m + 1)).naturality ((t.truncGEπ (-m)).app K)
    dsimp only [Functor.id_map] at hn
    rw [← Category.assoc, hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    simp
  rw [← hg, F.map_comp, Functor.map_comp]
  infer_instance

private theorem unbounded_of_postnikov
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    [HasCountableProducts (DerivedCategory D)]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]
    (P : ObjectProperty (DerivedCategory C)) (Q : ObjectProperty D) [Q.IsClosedUnderIsomorphisms]
    (hP : ∀ L, P L → ∀ j : ℤ,
      P ((DerivedCategory.TStructure.t.truncLE j).obj L) ∧
      P ((DerivedCategory.TStructure.t.truncGE j).obj L))
    (c : ℤ)
    (hB : ∀ L, P L → (∃ a : ℤ, L.IsGE a) →
      (∀ q : ℤ, Q ((DerivedCategory.homologyFunctor D q).obj (F.obj L))) ∧
      (∀ a : ℤ, L.IsGE a → (F.obj L).IsGE a) ∧
      (∀ b : ℤ, L.IsLE b → (F.obj L).IsLE (b + c)))
    (K : DerivedCategory C) (hK : P K)
    (hc : Pretriangulated.IsHomotopyLimit (F.mapCone (DerivedCategory.lowerPostnikovCone K)))
    (hprod : ∀ j : ℤ, PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor D j)) :
    (∀ q : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor D q).map
        (F.map ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)))) ∧
    (∀ q : ℤ, Q ((DerivedCategory.homologyFunctor D q).obj (F.obj K))) ∧
    (∀ a : ℤ, K.IsGE a → (F.obj K).IsGE a) ∧
    (∀ b : ℤ, K.IsLE b → (F.obj K).IsLE (b + c)) := by
  have hF : ∀ L, P L → ∀ a : ℤ, L.IsGE a →
      ∀ b : ℤ, L.IsLE b → (F.obj L).IsLE (b + c) := by
    intro L hL a ha b hb
    exact (hB L hL ⟨a, ha⟩).2.2 b hb
  have hstab : ∀ q : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor D q).map
        (F.map ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) := by
    intro q
    let N : ℕ := (c - q + 1).toNat
    refine ⟨N, fun n hn ↦ ?_⟩
    apply DerivedCategory.isIso_homology_map_cone_leg_of_eventually_isIso
      (C := D) _ _ hc hprod q N ?_ n hn
    intro i hi
    constructor
    · simp only [Functor.comp_map, DerivedCategory.lowerPostnikovTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact truncation_step_isIso F P hP c hF K hK
        ((i + 1 : ℕ) : ℤ) q (-(i : ℤ)) (by omega)
        (by dsimp [N] at hi; omega)
    · simp only [Functor.comp_map, DerivedCategory.lowerPostnikovTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact truncation_step_isIso F P hP c hF K hK
        ((i + 1 : ℕ) : ℤ) (q - 1) (-(i : ℤ)) (by omega)
        (by dsimp [N] at hi; omega)
  have hbounded (n : ℕ) := hB ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)
    (hP K hK (-(n : ℤ))).2 ⟨-(n : ℤ), inferInstance⟩
  refine ⟨hstab, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨N, hN⟩ := hstab q
    have := hN N le_rfl
    exact Q.prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor D q).map
        (F.map ((DerivedCategory.TStructure.t.truncGEπ (-(N : ℤ))).app K)))).symm
      ((hbounded N).1 q)
  · intro a ha
    exact (hB K hK ⟨a, ha⟩).2.1 a ha
  · intro b hb
    apply (DerivedCategory.isLE_iff _ _).2
    intro q hq
    obtain ⟨N, hN⟩ := hstab q
    have := hN N le_rfl
    have : ((DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj K).IsLE b := inferInstance
    have : (F.obj ((DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj K)).IsLE
        (b + c) := (hbounded N).2.2 b this
    exact (DerivedCategory.isZero_of_isLE
      (F.obj ((DerivedCategory.TStructure.t.truncGE (-(N : ℤ))).obj K))
      (b + c) q hq).of_iso
      (asIso ((DerivedCategory.homologyFunctor D q).map
        (F.map ((DerivedCategory.TStructure.t.truncGEπ (-(N : ℤ))).app K))))

open AlgebraicGeometry.ProEtale in
private theorem coefficient_unbounded
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : AlgebraicGeometry.Scheme.{u}}
    (p : X ⟶ Y)
    (P : ObjectProperty
      (DerivedCategory (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))))
    (Q : ObjectProperty (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y))) [Q.IsClosedUnderIsomorphisms]
    (hP : ∀ L, P L → ∀ j : ℤ,
      P ((DerivedCategory.TStructure.t.truncLE j).obj L) ∧
      P ((DerivedCategory.TStructure.t.truncGE j).obj L))
    (c : ℤ)
    (hB : ∀ L, P L → (∃ a : ℤ, L.IsGE a) →
      (∀ q : ℤ, Q ((DerivedCategory.homologyFunctor (Mod
        (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) q).obj
        ((CondensedRing.moduleObjectDerivedPushforward Λ p).obj L))) ∧
      (∀ a : ℤ, L.IsGE a → ((CondensedRing.moduleObjectDerivedPushforward Λ p).obj L).IsGE a) ∧
      (∀ b : ℤ, L.IsLE b → ((CondensedRing.moduleObjectDerivedPushforward Λ p).obj L).IsLE (b + c)))
    (K : DerivedCategory (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) (hK : P K)
 :
    (∀ q : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor (Mod
        (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) q).map
        ((CondensedRing.moduleObjectDerivedPushforward Λ p).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)))) ∧
    (∀ q : ℤ, Q ((DerivedCategory.homologyFunctor (Mod
        (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) q).obj
      ((CondensedRing.moduleObjectDerivedPushforward Λ p).obj K))) ∧
    (∀ a : ℤ, K.IsGE a → ((CondensedRing.moduleObjectDerivedPushforward Λ p).obj K).IsGE a) ∧
    (∀ b : ℤ, K.IsLE b →
        ((CondensedRing.moduleObjectDerivedPushforward Λ p).obj K).IsLE (b + c)) := by
  let F := CondensedRing.moduleObjectDerivedPushforward Λ p
  let : F.CommShift ℤ := by
    dsimp only [F, CondensedRing.moduleObjectDerivedPushforward]
    infer_instance
  let : F.IsTriangulated := by
    dsimp only [F, CondensedRing.moduleObjectDerivedPushforward]
    infer_instance
  obtain ⟨hc, hprod⟩ :=
    CondensedRing.moduleObjectDerivedPushforward_postnikov_roos
      Λ p K
  let : HasCountableProducts
      (DerivedCategory (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y))) :=
    ⟨fun J ↦ DerivedCategory.hasLimitsOfShape_discrete _ J⟩
  exact unbounded_of_postnikov
    (C := Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))
    (D := Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) F P Q hP c hB K hK hc hprod

namespace AlgebraicGeometry.ProEtale

/-- Proper direct image for a finite subextension of ℚ_ℓ: eventual truncation stabilization,
ind-constructible cohomology, and both cohomological amplitude bounds, for arbitrary K.
-/
theorem proper_indConstructible_unbounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (d : ℤ)
    (hd : ∀ y : Y,
      topologicalKrullDim (pullback p
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
        if 0 ≤ d then (d.toNat : WithBot ℕ∞) else ⊥)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.continuousMapRingObj E) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj K))
    :
    (∀ q : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((CondensedRing.moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)))) ∧
    (∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).obj
        K))) ∧
    (∀ a : ℤ, K.IsGE a →
      ((CondensedRing.moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).obj
        K).IsGE a) ∧
    (∀ b : ℤ, K.IsLE b →
      ((CondensedRing.moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).obj
        K).IsLE
        (b + 2 * d + 1)) := by
  let F := CondensedRing.moduleObjectDerivedPushforward (Profinite.continuousMapRingObj.{u} E) p
  let : F.CommShift ℤ := by
    dsimp only [F, CondensedRing.moduleObjectDerivedPushforward]
    infer_instance
  let : F.IsTriangulated := by
    dsimp only [F, CondensedRing.moduleObjectDerivedPushforward]
    infer_instance
  let P : ObjectProperty _ := fun L ↦ ∀ j : ℤ, ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible (Profinite.continuousMapRingObj.{u} E) X)
    ((DerivedCategory.homologyFunctor _ j).obj L)
  let Q := ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible (Profinite.continuousMapRingObj.{u} E) Y)
  have hP : ∀ L, P L → ∀ j : ℤ,
      P ((DerivedCategory.TStructure.t.truncLE j).obj L) ∧
      P ((DerivedCategory.TStructure.t.truncGE j).obj L) := by
    intro L hL j
    exact (indConstructibleDerived_sums_and_truncations ℓ E
      k p₀ hp₀ hpℓ X).2.2.1 L j hL
  have hB : ∀ L, P L → (∃ a : ℤ, L.IsGE a) →
      (∀ q : ℤ, Q ((DerivedCategory.homologyFunctor _ q).obj (F.obj L))) ∧
      (∀ a : ℤ, L.IsGE a → (F.obj L).IsGE a) ∧
      (∀ b : ℤ, L.IsLE b → (F.obj L).IsLE (b + (2 * d + 1))) := by
    intro L hL hLge
    simpa only [F, CondensedRing.moduleObjectDerivedPushforward, add_assoc] using
      proper_indConstructible_boundedBelow ℓ E k p₀ hp₀ hpℓ X Y p d hd L hL hLge
  simpa only [Q, add_assoc] using
    coefficient_unbounded (Profinite.continuousMapRingObj.{u} E) p P Q hP (2 * d + 1) hB K hK

/-- Proper direct image for the condensed algebraic closure: eventual truncation stabilization,
ind-constructible cohomology, and both cohomological amplitude bounds, for arbitrary K.
-/
theorem proper_indConstructible_unbounded_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (d : ℤ)
    (hd : ∀ y : Y,
      topologicalKrullDim (pullback p
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
        if 0 ≤ d then (d.toNat : WithBot ℕ∞) else ⊥)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj K))
    :
    (∀ q : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) p).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)))) ∧
    (∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) p).obj
        K))) ∧
    (∀ a : ℤ, K.IsGE a →
      ((CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) p).obj
        K).IsGE a) ∧
    (∀ b : ℤ, K.IsLE b →
      ((CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) p).obj
        K).IsLE
        (b + 2 * d + 1)) := by
  let F := CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) p
  let : F.CommShift ℤ := by
    dsimp only [F, CondensedRing.moduleObjectDerivedPushforward]
    infer_instance
  let : F.IsTriangulated := by
    dsimp only [F, CondensedRing.moduleObjectDerivedPushforward]
    infer_instance
  let P : ObjectProperty _ := fun L ↦ ∀ j : ℤ, ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
    ((DerivedCategory.homologyFunctor _ j).obj L)
  let Q := ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
  have hP : ∀ L, P L → ∀ j : ℤ,
      P ((DerivedCategory.TStructure.t.truncLE j).obj L) ∧
      P ((DerivedCategory.TStructure.t.truncGE j).obj L) := by
    intro L hL j
    exact (indConstructibleDerived_sums_and_truncations_padicAlgCl ℓ
      k p₀ hp₀ hpℓ X).2.2.1 L j hL
  have hB : ∀ L, P L → (∃ a : ℤ, L.IsGE a) →
      (∀ q : ℤ, Q ((DerivedCategory.homologyFunctor _ q).obj (F.obj L))) ∧
      (∀ a : ℤ, L.IsGE a → (F.obj L).IsGE a) ∧
      (∀ b : ℤ, L.IsLE b → (F.obj L).IsLE (b + (2 * d + 1))) := by
    intro L hL hLge
    simpa only [F, CondensedRing.moduleObjectDerivedPushforward, add_assoc] using
      proper_indConstructible_boundedBelow_padicAlgCl ℓ k p₀ hp₀ hpℓ X Y p d hd L hL hLge
  simpa only [Q, add_assoc] using
    coefficient_unbounded (Profinite.padicAlgClRingObj ℓ) p P Q hP (2 * d + 1) hB K hK

end AlgebraicGeometry.ProEtale

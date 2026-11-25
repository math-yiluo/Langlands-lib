/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex

/-! # The singleton Čech augmentation

Source: Stacks Project, Tag 08C2, singleton-cover specialization of the alternating total.
(blueprint: lem-sc-singleton-cech-augmentation-iso).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- For the cover consisting of the whole scheme, the section-to-total augmentation
is already an isomorphism of complexes, without any acyclicity or boundedness assumption.
Source: Stacks Project, Tag 08C2, equation-global-sections-to-alternating-cech.
(blueprint: lem-sc-singleton-cech-augmentation-iso).

Proof: In Čech degree zero there is exactly one increasing tuple into Fin 1. Its
intersection is the whole scheme and the restriction is the identity. In every
positive Čech degree there are no increasing tuples into Fin 1, so that cochain
module is zero. The extended double complex therefore has only Čech column zero.
In each total degree its coproduct has exactly this one nonzero summand; evaluation
on the unique tuple identifies it with the ordinary section module. The vertical
sign is (-1)^0 = 1 and the horizontal differential is zero. These evaluation maps
commute with the differential and are inverse to the specified augmentation.
This works for the empty scheme and for unbounded or zero complexes as well. -/
theorem singletonCechAugmentation_isIso (X : Scheme.{u})
    (F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    IsIso ((alternatingCechAugmentation (fun _ : Fin 1 ↦ (⊤ : X.Opens))).app F) := by
  classical
  let U : Fin 1 → X.Opens := fun _ ↦ ⊤
  have hz (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
      IsIso (alternatingCechZero U M) := by
    unfold alternatingCechZero
    have hpres (P : X.Opensᵒᵖ ⥤
        ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) :
        IsIso (alternatingCechPresheafZero U P) := by
      let t₀ : Fin 1 ↪o Fin 1 := (OrderIso.refl (Fin 1)).toOrderEmbedding
      have ht (t : Fin 1 ↪o Fin 1) : t₀ = t := by
        apply DFunLike.ext
        intro k
        exact Subsingleton.elim _ _
      let ev : (alternatingCechComplex U P).X 0 ⟶
          P.obj (op (alternatingCechIntersection U t₀)) :=
        ModuleCat.ofHom (LinearMap.proj (R := ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
          (φ := fun t : Fin 1 ↪o Fin 1 ↦ P.obj (op (alternatingCechIntersection U t))) t₀)
      have : IsIso ev := by
        rw [ConcreteCategory.isIso_iff_bijective]
        constructor
        · intro a b h
          funext t
          obtain rfl := ht t
          exact h
        · intro x
          refine ⟨fun t ↦ cast (congrArg
            (fun t ↦ (P.obj (op (alternatingCechIntersection U t)) : Type u)) (ht t)) x, ?_⟩
          change cast (congrArg
            (fun t ↦ (P.obj (op (alternatingCechIntersection U t)) : Type u)) (ht t₀)) x = x
          simp
      have hi : alternatingCechIntersection U t₀ = ⊤ := by
        simp [alternatingCechIntersection, U]
      have hr : IsIso (P.map
          (homOfLE (le_top (a := alternatingCechIntersection U t₀))).op) := by
        have : IsIso (homOfLE (le_top (a := alternatingCechIntersection U t₀))) := by
          rw [hi]
          change IsIso (𝟙 (⊤ : X.Opens))
          infer_instance
        infer_instance
      have hc : alternatingCechPresheafZero U P ≫ ev =
          P.map (homOfLE (le_top (a := alternatingCechIntersection U t₀))).op := by
        rfl
      have : IsIso (alternatingCechPresheafZero U P ≫ ev) := by rw [hc]; infer_instance
      exact IsIso.of_isIso_comp_right _ ev
    have := hpres ((alternatingCechModulePresheaf (X := X)).obj M)
    infer_instance
  have hzero (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (p : ℤ) (hp : p ≠ 0) :
      IsZero (((alternatingCechModuleFunctor U).obj M).X p) := by
    let P := (alternatingCechModulePresheaf (X := X)).obj M
    change IsZero (((alternatingCechComplex U P).extend
      ComplexShape.embeddingUpNat).X p)
    by_cases hn : 0 ≤ p
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      have hk : k ≠ 0 := by exact_mod_cast hp
      have hempty : IsEmpty (Fin (k + 1) ↪o Fin 1) := ⟨fun t ↦ by
        have hc := Fintype.card_le_of_injective t t.injective
        simp only [Fintype.card_fin] at hc
        omega⟩
      have hz : IsZero ((alternatingCechComplex U P).X k) := by
        apply ModuleCat.isZero_iff_subsingleton.mpr
        change Subsingleton (∀ t : Fin (k + 1) ↪o Fin 1,
          P.obj (op (alternatingCechIntersection U t)))
        infer_instance
      exact hz.of_iso ((alternatingCechComplex U P).extendXIso
        ComplexShape.embeddingUpNat (i := k) rfl)
    · apply HomologicalComplex.isZero_extend_X
      intro k h
      change (k : ℤ) = p at h
      omega
  let B := (alternatingCechDoubleFunctor U).obj F
  have hι (n : ℤ) : IsIso (B.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n)) := by
    let v : (B.total (ComplexShape.up ℤ)).X n ⟶ (B.X 0).X n :=
      B.totalDesc (fun p q h ↦ if hp : p = 0 then
        eqToHom (by subst p; congr 1; simpa using h)
        else 0)
    refine ⟨v, ?_, ?_⟩
    · simp [v]
    · apply HomologicalComplex₂.total.hom_ext
      intro p q h
      by_cases hp : p = 0
      · subst p
        have hq : q = n := by simpa using h
        subst q
        simp [v]
      · have hZ : IsZero ((B.X p).X q) := hzero (F.X q) p hp
        exact hZ.eq_of_src _ _
  have hcomp (n : ℤ) : IsIso (((alternatingCechAugmentation U).app F).f n) := by
    change IsIso (alternatingCechZero U (F.X n) ≫
      B.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    have := hz (F.X n)
    have := hι n
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

end AlgebraicGeometry

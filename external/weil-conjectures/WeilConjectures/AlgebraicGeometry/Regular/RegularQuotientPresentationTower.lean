/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Strict.IntegralStrictAugmentation
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

import WeilConjectures.AlgebraicGeometry.Regular.RegularPrincipalQuotientTower

/-! # Transport of regular quotient presentations

## References

* Stacks Project, Tag 099M
-/

@[expose] public section
set_option autoImplicit false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.ProEtale

private theorem map_shortExact_replace_f
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type v'} [Category.{w'} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : ShortComplex A) (hS : S.ShortExact)
    (f : F.obj S.X₁ ⟶ F.obj S.X₂) (hf : F.map S.f = f)
    (z : f ≫ F.map S.g = 0) : (ShortComplex.mk f (F.map S.g) z).ShortExact := by
  have he : S.map F ≅ ShortComplex.mk f (F.map S.g) z :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id, ShortComplex.map_f]
        using hf.symm)
      (by simp)
  exact ShortComplex.shortExact_of_iso he (hS.map_of_exact F)

private theorem ordinary_quotient_shortExact
    {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) (O : DiagonalReductionPresentation ℓ (𝟭 A))
    (P : CochainComplex A ℤ)
    (hP : ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) (n : ℕ)
    (z : (ℓ ^ (n + 1) • 𝟙 P) ≫
      (NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P = 0) :
    (ShortComplex.mk _ _ z).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let T := (ShortComplex.mk _ _ z).map (HomologicalComplex.eval A (.up ℤ) i)
  have ht : IsColimit (CokernelCofork.ofπ T.g T.zero) := O.quotient n (P.X i)
  exact ShortComplex.ShortExact.mk' (T.exact_of_g_is_cokernel ht) (hP n i)
    (epi_of_isColimit_cofork ht)

private theorem mapped_ordinary_quotient_shortExact
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type v'} [Category.{w'} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (ℓ : ℕ) (O : DiagonalReductionPresentation ℓ (𝟭 A))
    (P : CochainComplex A ℤ)
    (hP : ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) (n : ℕ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj P)
    (hf : (F.mapHomologicalComplex (.up ℤ)).map (ℓ ^ (n + 1) • 𝟙 P) = f)
    (z : f ≫ (F.mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P) = 0) :
    (ShortComplex.mk _ _ z).ShortExact := by
  have hz : (ℓ ^ (n + 1) • 𝟙 P) ≫
      (NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    exact O.zero n (P.X i)
  exact map_shortExact_replace_f (F.mapHomologicalComplex (.up ℤ))
    (ShortComplex.mk _ _ hz) (ordinary_quotient_shortExact ℓ O P hP n hz) f hf z

private theorem mapped_ordinary_quotient_zero
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type v'} [Category.{w'} B] [Abelian B]
    (F : A ⥤ B) [F.Additive]
    (ℓ : ℕ) (O : DiagonalReductionPresentation ℓ (𝟭 A))
    (P : CochainComplex A ℤ) (n : ℕ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj P)
    (hf : (F.mapHomologicalComplex (.up ℤ)).map (ℓ ^ (n + 1) • 𝟙 P) = f) :
    f ≫ (F.mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P) = 0 := by
  have hz : (ℓ ^ (n + 1) • 𝟙 P) ≫
      (NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    exact O.zero n (P.X i)
  rw [← hf, ← Functor.map_comp, hz, Functor.map_zero]

private theorem mapped_ordinary_quotient_transition
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type v'} [Category.{w'} B] [Abelian B]
    (F : A ⥤ B) [F.Additive]
    (ℓ : ℕ) (O : DiagonalReductionPresentation ℓ (𝟭 A))
    (P : CochainComplex A ℤ) (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (O.π (n + 1)) (.up ℤ)).app P) ≫
      (F.mapHomologicalComplex (.up ℤ)).map
        (((O.E.mapHomologicalComplex (.up ℤ)).obj P).asFunctor.map
          (homOfLE (Nat.le_succ n)).op) =
    (F.mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P) := by
  rw [← Functor.map_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro i
  exact O.transition n (P.X i)

private theorem transport_quotient_tower
    {D : Type v} [Category.{w} D]
    (L M G : ℕᵒᵖ ⥤ D) (K : D)
    (p : ∀ n : ℕ, K ⟶ L.obj (op n))
    (a : ∀ n : ℕ, K ⟶ G.obj (op (n + 1)))
    (c : L ≅ M) (β : addOpFunctor 1 ⋙ G ≅ M)
    (h : ∀ n : ℕ, p n ≫ c.hom.app (op n) = a n ≫ β.hom.app (op n)) :
    ∃ α : L ≅ addOpFunctor 1 ⋙ G,
      ∀ n : ℕ, p n ≫ α.hom.app (op n) = a n := by
  let α := c ≪≫ β.symm
  refine ⟨α, ?_⟩
  intro n
  apply (Iso.cancel_iso_hom_right _ _ (β.app (op n))).1
  change (p n ≫ (c.hom.app (op n) ≫ β.inv.app (op n))) ≫ β.hom.app (op n) = _
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact h n

private theorem transport_derived_quotient_tower
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{u + 1} A]
    {B : Type v'} [Category.{w'} B] [Abelian B] [HasDerivedCategory.{u + 1} B]
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive]
    (P : CochainComplex A ℤ) (X : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (p : ∀ n : ℕ, P ⟶ X.obj (op n))
    (G : ℕᵒᵖ ⥤ DerivedCategory B)
    (a : ∀ n : ℕ, e.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj P) ⟶
      G.obj (op (n + 1)))
    (β : addOpFunctor 1 ⋙ G ≅
      X ⋙ e.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hβ : ∀ n : ℕ, a n ≫ β.hom.app (op n) =
      (e.functor.mapDerivedCategoryFactors.app P).hom ≫
        DerivedCategory.Q.map ((e.functor.mapHomologicalComplex (.up ℤ)).map (p n))) :
    ∃ α : X ⋙ DerivedCategory.Q ⋙ e.functor.mapDerivedCategory ≅ addOpFunctor 1 ⋙ G,
      ∀ n : ℕ,
        e.functor.mapDerivedCategory.map (DerivedCategory.Q.map (p n)) ≫
          α.hom.app (op n) = a n := by
  let L := X ⋙ DerivedCategory.Q ⋙ e.functor.mapDerivedCategory
  let M := X ⋙ e.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let c : L ≅ M := Functor.isoWhiskerLeft X e.functor.mapDerivedCategoryFactors
  exact transport_quotient_tower L M G _
    (fun n ↦ e.functor.mapDerivedCategory.map (DerivedCategory.Q.map (p n))) a c β
    (fun n ↦ (e.functor.mapDerivedCategoryFactors_hom_naturality (p n)).trans (hβ n).symm)

private theorem quotient_presentation_from_comparison
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{u + 1} A]
    {B : Type v'} [Category.{w'} B] [Abelian B] [HasDerivedCategory.{u + 1} B]
    (ℓ : ℕ) (O : DiagonalReductionPresentation ℓ (𝟭 A))
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive]
    (P : CochainComplex A ℤ)
    (hP : ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i)))
    (G : DerivedCategory B → ℕᵒᵖ ⥤ DerivedCategory B)
    (a : ∀ (K : DerivedCategory B) (n : ℕ), K ⟶ (G K).obj (op (n + 1)))
    (hc : ∀ (R : CochainComplex B ℤ) (Y : ℕᵒᵖ ⥤ CochainComplex B ℤ)
      (p : ∀ n : ℕ, R ⟶ Y.obj (op n))
      (hz : ∀ n : ℕ, (ℓ ^ (n + 1) • 𝟙 R) ≫ p n = 0)
      (_hT : ∀ n : ℕ, (ShortComplex.mk _ _ (hz n)).ShortExact)
      (_hp : ∀ n : ℕ, p (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op = p n)
      (K : DerivedCategory B) (g : K ≅ DerivedCategory.Q.obj R),
      ∃ β : addOpFunctor 1 ⋙ G K ≅ Y ⋙ DerivedCategory.Q,
        ∀ n : ℕ, a K n ≫ β.hom.app (op n) = g.hom ≫ DerivedCategory.Q.map (p n)) :
    let K := e.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj P)
    let X := (O.E.mapHomologicalComplex (.up ℤ)).obj P
    ∃ α : X.asFunctor ⋙ DerivedCategory.Q ⋙ e.functor.mapDerivedCategory ≅
        addOpFunctor 1 ⋙ G K,
      ∀ n : ℕ,
        e.functor.mapDerivedCategory.map
            (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P)) ≫
          α.hom.app (op n) = a K n := by
  let F := e.functor.mapHomologicalComplex (.up ℤ)
  let R := F.obj P
  let X := (O.E.mapHomologicalComplex (.up ℤ)).obj P
  let p (n : ℕ) : P ⟶ X.asFunctor.obj (op n) :=
    (NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P
  have hscalar (n : ℕ) : F.map (ℓ ^ (n + 1) • 𝟙 P) = ℓ ^ (n + 1) • 𝟙 R := by
    rw [F.map_nsmul, F.map_id]
  have hz (n : ℕ) : (ℓ ^ (n + 1) • 𝟙 R) ≫ F.map (p n) = 0 :=
    mapped_ordinary_quotient_zero e.functor ℓ O P n _ (hscalar n)
  have hT (n : ℕ) : (ShortComplex.mk _ _ (hz n)).ShortExact :=
    mapped_ordinary_quotient_shortExact e.functor ℓ O P hP n
      (ℓ ^ (n + 1) • 𝟙 R) (hscalar n) (hz n)
  let K := e.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj P)
  let g : K ≅ DerivedCategory.Q.obj R := e.functor.mapDerivedCategoryFactors.app P
  let Y := X.asFunctor ⋙ F
  have hp (n : ℕ) : F.map (p (n + 1)) ≫
      Y.map (homOfLE (Nat.le_succ n)).op = F.map (p n) :=
    mapped_ordinary_quotient_transition e.functor ℓ O P n
  obtain ⟨β, hβ⟩ := hc R Y (fun n ↦ F.map (p n)) hz hT hp K g
  exact transport_derived_quotient_tower e P X.asFunctor p (G K) (a K) β hβ

private theorem principal_quotient_tower_nat
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {Λ : Type (u + 1)} [CommRing Λ]
    (ℓ : ℕ) (hr : (ℓ : Λ) ∈ nonZeroDivisors Λ)
    (R : CochainComplex (Sheaf J (ModuleCat.{u + 1} Λ)) ℤ)
    (Y : ℕᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{u + 1} Λ)) ℤ)
    (p : ∀ n : ℕ, R ⟶ Y.obj (op n))
    (hz : ∀ n : ℕ, (ℓ ^ (n + 1) • 𝟙 R) ≫ p n = 0)
    (hT : ∀ n : ℕ, (ShortComplex.mk _ _ (hz n)).ShortExact)
    (hp : ∀ n : ℕ, p (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op = p n)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ)))
    (g : K ≅ DerivedCategory.Q.obj R) :
    ∃ β : addOpFunctor 1 ⋙ DerivedCategory.derivedCompletionDiagram J
          (Ideal.span {(ℓ : Λ)}) K ≅ Y ⋙ DerivedCategory.Q,
      ∀ n : ℕ, (DerivedCategory.derivedCompletionCone J (Ideal.span {(ℓ : Λ)}) K).π.app
          (op (n + 1)) ≫ β.hom.app (op n) = g.hom ≫ DerivedCategory.Q.map (p n) := by
  have hs (n : ℕ) : (ℓ : Λ) ^ (n + 1) • 𝟙 R = ℓ ^ (n + 1) • 𝟙 R := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hz' (n : ℕ) : ((ℓ : Λ) ^ (n + 1) • 𝟙 R) ≫ p n = 0 := by
    rw [hs]
    exact hz n
  have hT' (n : ℕ) : (ShortComplex.mk _ _ (hz' n)).ShortExact := by
    simpa only [hs n] using hT n
  exact regular_principal_quotient_tower J (ℓ : Λ) hr R Y p hz' hT' hp K g

/-- An ordinary quotient presentation is transported to the positive derived quotient tower. -/
theorem regular_quotient_presentation_tower
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{u + 1} A]
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (ℓ : ℕ) {Λ : Type (u + 1)} [CommRing Λ]
    (hr : (ℓ : Λ) ∈ nonZeroDivisors Λ) (J : GrothendieckTopology C)
    (O : DiagonalReductionPresentation ℓ (𝟭 A))
    (e : A ≌ Sheaf J (ModuleCat.{u + 1} Λ))
    [e.functor.Additive] [e.inverse.Additive]
    (P : CochainComplex A ℤ)
    (hP : ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) :
    let K := e.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj P)
    let X := (O.E.mapHomologicalComplex (.up ℤ)).obj P
    let G := DerivedCategory.derivedCompletionDiagram J
      (Ideal.span {(ℓ : Λ)}) K
    ∃ α : X.asFunctor ⋙ DerivedCategory.Q ⋙ e.functor.mapDerivedCategory ≅
        addOpFunctor 1 ⋙ G,
      ∀ n : ℕ,
        e.functor.mapDerivedCategory.map
            (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P)) ≫
          α.hom.app (op n) =
        (DerivedCategory.derivedCompletionCone J
          (Ideal.span {(ℓ : Λ)}) K).π.app (op (n + 1)) := by
  let G (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) :=
    DerivedCategory.derivedCompletionDiagram J (Ideal.span {(ℓ : Λ)}) K
  let a (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (n : ℕ) :=
    (DerivedCategory.derivedCompletionCone J (Ideal.span {(ℓ : Λ)}) K).π.app (op (n + 1))
  exact quotient_presentation_from_comparison ℓ O e P hP G a
    (principal_quotient_tower_nat J ℓ hr)

end AlgebraicGeometry.ProEtale

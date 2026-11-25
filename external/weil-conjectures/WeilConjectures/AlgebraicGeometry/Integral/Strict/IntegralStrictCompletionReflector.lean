/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import WeilConjectures.AlgebraicGeometry.Integral.Strict.IntegralStrictCompletionComparison
import all Mathlib.Logic.Small.Defs

/-! # Reflection by the integral strict quotient tower

## References

* Stacks Project Tags 099M, 091S and 091Z
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

universe a b va vb

private theorem orthogonal_equivalence_iff
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Preadditive A] [Preadditive B] (E : A ≌ B)
    [E.functor.Additive] [E.inverse.Additive] (n : ℕ) (N : A) :
    (∀ P : A, IsIso (n • 𝟙 P) → Subsingleton (P ⟶ N)) ↔
      (∀ P : B, IsIso (n • 𝟙 P) → Subsingleton (P ⟶ E.functor.obj N)) := by
  constructor
  · intro h P hp
    have : IsIso (n • 𝟙 (E.inverse.obj P)) := by
      have : IsIso (n • 𝟙 P) := hp
      have := Functor.map_isIso E.inverse (n • 𝟙 P)
      simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using this
    have hs := h (E.inverse.obj P) inferInstance
    refine ⟨fun f g ↦ ?_⟩
    apply (cancel_epi (E.counitIso.app P).hom).1
    exact E.fullyFaithfulFunctor.map_preimage
      ((E.counitIso.app P).hom ≫ f) |>.symm.trans
        ((congrArg E.functor.map (hs.elim
          (E.fullyFaithfulFunctor.preimage ((E.counitIso.app P).hom ≫ f))
          (E.fullyFaithfulFunctor.preimage ((E.counitIso.app P).hom ≫ g)))).trans
            (E.fullyFaithfulFunctor.map_preimage _))
  · intro h P hp
    have : IsIso (n • 𝟙 (E.functor.obj P)) := by
      have : IsIso (n • 𝟙 P) := hp
      have := Functor.map_isIso E.functor (n • 𝟙 P)
      simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using this
    exact ⟨fun f g ↦ E.functor.map_injective ((h _ inferInstance).elim _ _)⟩

private theorem reflector_transport
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Preadditive A] [Preadditive B] (E : A ≌ B)
    [E.functor.Additive] [E.inverse.Additive] (n : ℕ)
    (G : A ⥤ A) (H : B ⥤ B) (η : 𝟭 B ⟶ H)
    (hH : ∀ K P : B, IsIso (n • 𝟙 P) → Subsingleton (P ⟶ H.obj K))
    (hη : ∀ K N : B,
      (∀ P : B, IsIso (n • 𝟙 P) → Subsingleton (P ⟶ N)) →
        Function.Bijective (fun f : H.obj K ⟶ N ↦ η.app K ≫ f))
    (c : G ⋙ E.functor ≅ E.functor ⋙ H) :
    ∃ unit : 𝟭 A ⟶ G,
      (∀ K P : A, IsIso (n • 𝟙 P) → Subsingleton (P ⟶ G.obj K)) ∧
      ∀ K N : A,
        (∀ P : A, IsIso (n • 𝟙 P) → Subsingleton (P ⟶ N)) →
          Function.Bijective (fun f : G.obj K ⟶ N ↦ unit.app K ≫ f) := by
  let w : (𝟭 A) ⋙ E.functor ⟶ G ⋙ E.functor :=
    (Functor.leftUnitor E.functor).hom ≫ (Functor.rightUnitor E.functor).inv ≫
      Functor.whiskerLeft E.functor η ≫ c.inv
  let unit : 𝟭 A ⟶ G := (E.fullyFaithfulFunctor.whiskeringRight A).preimage w
  have hunit (K : A) : E.functor.map (unit.app K) = η.app (E.functor.obj K) ≫
      (c.app K).inv := by
    have hh := congrArg (fun z ↦ z.app K)
      ((E.fullyFaithfulFunctor.whiskeringRight A).map_preimage w)
    change E.functor.map (unit.app K) = w.app K at hh
    rw [hh]
    simp [w]
  refine ⟨unit, ?_, ?_⟩
  · intro K
    apply (orthogonal_equivalence_iff E n (G.obj K)).mpr
    intro P hp
    have hs := hH (E.functor.obj K) P hp
    refine ⟨fun f g ↦ ?_⟩
    apply (cancel_mono (c.app K).hom).1
    exact hs.elim _ _
  · intro K N hN
    let e : (G.obj K ⟶ N) ≃ (H.obj (E.functor.obj K) ⟶ E.functor.obj N) :=
      E.fullyFaithfulFunctor.homEquiv.trans (Iso.homCongr (c.app K) (Iso.refl _))
    have hb := (hη (E.functor.obj K) (E.functor.obj N)
      ((orthogonal_equivalence_iff E n N).mp hN)).comp e.bijective
    have heq : (fun f : G.obj K ⟶ N ↦ η.app (E.functor.obj K) ≫ e f) =
        (fun f ↦ E.functor.map (unit.app K ≫ f)) := by
      funext f
      simp only [e, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
      rw [Functor.map_comp, hunit, Category.assoc]
      rfl
    change Function.Bijective (fun f : G.obj K ⟶ N ↦ η.app (E.functor.obj K) ≫ e f) at hb
    rw [heq] at hb
    exact (Function.Bijective.of_comp_iff' E.fullyFaithfulFunctor.homEquiv.bijective _).mp hb

private theorem smulInvertible_natCast
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]
    (n : ℕ) (P : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    DerivedCategory.smulInvertible J (n : R) P ↔ IsIso (n • 𝟙 P) := by
  dsimp only [DerivedCategory.smulInvertible]
  rw [Nat.cast_smul_eq_nsmul]

private theorem integral_module_completion_reflector (ℓ : ℕ) [Fact ℓ.Prime]
    (W : Scheme.{u}) :
    ∃ unit : 𝟭 _ ⟶ integralModuleCompletion ℓ W,
      (∀ K P, IsIso (ℓ • 𝟙 P) →
        Subsingleton (P ⟶ (integralModuleCompletion ℓ W).obj K)) ∧
      ∀ K N,
        (∀ P, IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ N)) →
        Function.Bijective (fun f : (integralModuleCompletion ℓ W).obj K ⟶ N ↦
          unit.app K ≫ f) := by
  let J := Scheme.ProEt.topology W
  let r : ULift.{u + 1} ℤ := ℓ
  let I := Ideal.span {r}
  let h : ∃ t ∈ nonZeroDivisors (ULift.{u + 1} ℤ), I = Ideal.span {t} :=
    ⟨r, integralCompletionPrimeRegular ℓ, rfl⟩
  let adj := DerivedCategory.derivedCompletionAdjunction J I h
  refine ⟨adj.unit, ?_, ?_⟩
  · intro K P hp
    have hc := ((DerivedCategory.derivedCompletion J I h).obj K).property
    have ho := (DerivedCategory.derivedComplete_iff_rightOrthogonal
      (integralCompletionPrimeRegular ℓ) (show I = Ideal.span {r} from rfl) _).mp hc
    have hi : DerivedCategory.smulInvertible J r P := by
      exact (smulInvertible_natCast J ℓ P).mpr hp
    exact ⟨fun f g ↦ (ho f hi).trans (ho g hi).symm⟩
  · intro K N hN
    have ho : (DerivedCategory.smulInvertible J r).rightOrthogonal N := by
      intro P f hp
      have hi : IsIso (ℓ • 𝟙 P) := by
        exact (smulInvertible_natCast J ℓ P).mp hp
      exact (hN P hi).elim f 0
    have hc := (DerivedCategory.derivedComplete_iff_rightOrthogonal
      (integralCompletionPrimeRegular ℓ) (show I = Ideal.span {r} from rfl) _).mpr ho
    let e := InducedCategory.homEquiv.symm.trans (adj.homEquiv K ⟨N, hc⟩)
    have he (f : (integralModuleCompletion ℓ W).obj K ⟶ N) :
        e f = adj.unit.app K ≫ f := by
      dsimp only [e, Equiv.trans_apply]
      rw [Adjunction.homEquiv_unit]
      rfl
    have hb : Function.Bijective (fun f : (integralModuleCompletion ℓ W).obj K ⟶ N ↦ e f) :=
      e.bijective
    simpa only [he] using hb

/-- The total derived limit of the integral prime-power quotient tower is the
reflection onto complexes right orthogonal to all ell-invertible complexes. -/
theorem integral_strict_completion_reflector (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (I : DiagonalDerivedReduction ℓ (𝟭 (DiagonalAb W)))
    (RZ : DerivedCategory (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DerivedCategory (DiagonalAb W))
    (ηZ : (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ)
    (hRZ : RZ.IsRightDerivedFunctor ηZ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ DiagonalAb W) (.up ℤ))) :
    ∃ unit : 𝟭 (DerivedCategory (DiagonalAb W)) ⟶ I.T ⋙ RZ,
      (∀ (K P : DerivedCategory (DiagonalAb W)), IsIso (ℓ • 𝟙 P) →
        Subsingleton (P ⟶ (I.T ⋙ RZ).obj K)) ∧
      ∀ (K N : DerivedCategory (DiagonalAb W)),
        (∀ P : DerivedCategory (DiagonalAb W), IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ N)) →
        Function.Bijective (fun f : (I.T ⋙ RZ).obj K ⟶ N ↦ unit.app K ≫ f)  := by
  obtain ⟨unit, hc, hb⟩ := integral_module_completion_reflector ℓ W
  obtain ⟨c⟩ := integral_strict_completion_comparison ℓ W I RZ ηZ hRZ
  have : (integralCompletionCoefficientEquivalence W).mapDerivedCategory.functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (integralCompletionCoefficientEquivalence W).mapDerivedCategory.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  exact reflector_transport (integralCompletionCoefficientEquivalence W).mapDerivedCategory
    ℓ (I.T ⋙ RZ) (integralModuleCompletion ℓ W) unit hc hb c

end AlgebraicGeometry.ProEtale

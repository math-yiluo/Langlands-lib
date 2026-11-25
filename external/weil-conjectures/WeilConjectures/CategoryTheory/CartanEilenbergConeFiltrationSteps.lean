/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- The finite image sum in the pinned cone-filtration formula.
Source: Stacks Project, Tags 0133 and 012W, augmented-cone variant.
(blueprint: lem-sp-cartan-eilenberg-cone-filtration-data-steps). -/
noncomputable def coneFiltrationStep
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (aug : K ⟶
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
        (ComplexShape.up ℤ)) (b p n : ℤ) : Subobject ((CochainComplex.mappingCone aug).X n) :=
  (if p ≤ n + 1 then imageSubobject
    ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
  (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
    ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
      (ComplexShape.up ℤ) (n - s) s n ≫
        (CochainComplex.mappingCone.inr aug).f n))

/-- A containing subobject receives a morphism through its image. -/
private theorem cone_factors_image
    {A : Type uA} [Category.{vA} A] [Abelian A] {X Y : A}
    (f : X ⟶ Y) (Q : Subobject Y) (h : imageSubobject f ≤ Q) : Q.Factors f := by
  apply Subobject.factors_of_le f h
  simpa using imageSubobject_factors_comp_self f (𝟙 X)

/-- The totalization signs preserve factorization through a subobject. -/
private theorem cone_factors_units
    {A : Type uA} [Category.{vA} A] [Abelian A] {X Y : A}
    (Q : Subobject Y) (f : X ⟶ Y) (h : Q.Factors f) (z : ℤˣ) :
    Q.Factors (z • f) := by
  rw [Subobject.factors_iff]
  exact ⟨z • Q.factorThru f h, by simp [Linear.units_smul_comp]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The explicit cone steps are antitone and stable under the cone differential.
Source: Stacks Project, Tags 0133 and 012W, augmented-cone variant.
Proof: raising the cutoff shrinks the interval of generators and removes the K
summand when necessary. Pull the target step back along the cone differential.
The K generator maps to minus its differential and the augmentation: the former
lands in the next K generator, and the latter lands in complex index n+1 by haug.
If n+1<b, the augmentation component is zero because its source is zero.
A total generator of complex index s maps to signed terms of indices s and s+1.
Both indices lie in the next interval [max b p,n+1]. Thus every generating image
lies in the pullback, so their finite supremum does too. The pullback universal
property supplies the required factorization. Empty intervals require no cases.
The hypothesis on I below b is unnecessary for stability but is retained here
for compatibility with the parent's hypotheses.
(blueprint: lem-sp-cartan-eilenberg-cone-filtration-data-steps). -/
theorem coneFiltrationStep_props
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (b : ℤ) (_hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (haug : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 n n (zero_add n)) :
    (∀ n, Antitone (fun p ↦ coneFiltrationStep K I aug b p n)) ∧
    (∀ p n, (coneFiltrationStep K I aug b p (n + 1)).Factors
      ((coneFiltrationStep K I aug b p n).arrow ≫
        (CochainComplex.mappingCone aug).d n (n + 1))) := by
  constructor
  · intro n p q hpq
    unfold coneFiltrationStep
    apply sup_le_sup
    · split_ifs with hq hp hp
      · exact le_rfl
      · omega
      · exact bot_le
      · exact le_rfl
    · apply Finset.sup_mono
      intro s hs
      simp only [Finset.mem_Icc, max_le_iff] at hs ⊢
      exact ⟨⟨hs.1.1, hpq.trans hs.1.2⟩, hs.2⟩
  · intro p n
    let J := ((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip
    let d := (CochainComplex.mappingCone aug).d n (n + 1)
    let Q := coneFiltrationStep K I aug b p (n + 1)
    let P := (Subobject.pullback d).obj Q
    have hinl : ∀ m : ℤ, p ≤ m + 1 →
        (coneFiltrationStep K I aug b p m).Factors
          (HomologicalComplex.homotopyCofiber.inlX aug (m + 1) m rfl) := by
      intro m hm
      apply cone_factors_image
      simpa only [coneFiltrationStep, ite_eq_left hm, CochainComplex.mappingCone.inl,
        CochainComplex.HomComplex.Cochain.mk_v] using
        (le_sup_left : imageSubobject
          (HomologicalComplex.homotopyCofiber.inlX aug (m + 1) m rfl) ≤
          imageSubobject (HomologicalComplex.homotopyCofiber.inlX aug (m + 1) m rfl) ⊔ _)
    have hinr : ∀ s : ℤ, max b p ≤ s → s ≤ n + 1 →
        Q.Factors (J.ιTotalOrZero (ComplexShape.up ℤ) ((n + 1) - s) s (n + 1) ≫
          (CochainComplex.mappingCone.inr aug).f (n + 1)) := by
      intro s hs hn
      apply cone_factors_image
      exact (Finset.le_sup (f := fun s ↦ imageSubobject
        (J.ιTotalOrZero (ComplexShape.up ℤ) ((n + 1) - s) s (n + 1) ≫
          (CochainComplex.mappingCone.inr aug).f (n + 1)))
          (Finset.mem_Icc.mpr ⟨hs, hn⟩)).trans le_sup_right
    have hle : coneFiltrationStep K I aug b p n ≤ P := by
      unfold coneFiltrationStep
      apply sup_le
      · split_ifs with hp
        · let u := HomologicalComplex.homotopyCofiber.inlX aug (n + 1) n rfl
          have hu : Q.Factors (u ≫ d) := by
            change Q.Factors (HomologicalComplex.homotopyCofiber.inlX aug (n + 1) n rfl ≫
              HomologicalComplex.homotopyCofiber.d aug n (n + 1))
            rw [HomologicalComplex.homotopyCofiber.inlX_d aug n (n + 1)
              ((n + 1) + 1) rfl rfl]
            apply Subobject.factors_add
            · have hh := Subobject.factors_of_factors_right (K.d (n + 1) ((n + 1) + 1))
                (hinl (n + 1) (by omega))
              rw [← Subobject.factorThru_arrow _ _ hh, ← Preadditive.neg_comp]
              exact Subobject.factors_comp_arrow _
            · change Q.Factors (aug.f (n + 1) ≫
                (CochainComplex.mappingCone.inr aug).f (n + 1))
              by_cases hb : b ≤ n + 1
              · rw [haug]
                have hh := hinr (n + 1) (by omega) le_rfl
                rw [show (n + 1) - (n + 1) = 0 by omega,
                  J.ιTotalOrZero_eq _ _ _ _ (zero_add (n + 1))] at hh
                simpa only [Category.assoc] using Subobject.factors_of_factors_right
                  ((a.f (n + 1)).f 0 ≫ (HomologicalComplex.extendXIso
                    (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X (n + 1)))
                    ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv) hh
              · rw [(hKbelow (n + 1) (by omega)).eq_zero_of_src
                  (aug.f (n + 1) ≫ (CochainComplex.mappingCone.inr aug).f (n + 1))]
                exact Subobject.factors_zero
          have hf := pullback_factors d Q u hu
          simpa only [CochainComplex.mappingCone.inl,
            CochainComplex.HomComplex.Cochain.mk_v] using
            imageSubobject_le u (P.factorThru u hf) (P.factorThru_arrow u hf)
        · exact bot_le
      · apply Finset.sup_le
        intro s hs
        have hbs := (Finset.mem_Icc.mp hs).1
        have hsn := (Finset.mem_Icc.mp hs).2
        let v := J.ιTotalOrZero (ComplexShape.up ℤ) (n - s) s n ≫
          (CochainComplex.mappingCone.inr aug).f n
        have hv : Q.Factors (v ≫ d) := by
          dsimp only [v, d]
          rw [Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc,
            J.ιTotalOrZero_eq _ _ _ _ (by change n - s + s = n; omega),
            HomologicalComplex₂.total_d, Preadditive.comp_add, Preadditive.add_comp,
            HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
            J.d₁_eq' _ (show (ComplexShape.up ℤ).Rel (n - s) ((n - s) + 1) by rfl),
            J.d₂_eq' _ (n - s) (show (ComplexShape.up ℤ).Rel s (s + 1) by rfl)]
          simp only [Linear.units_smul_comp, Category.assoc]
          apply Subobject.factors_add
          · apply cone_factors_units
            have hh := hinr s hbs (by omega)
            rw [show (n + 1) - s = (n - s) + 1 by omega] at hh
            exact Subobject.factors_of_factors_right ((J.d (n - s) ((n - s) + 1)).f s) hh
          · apply cone_factors_units
            have hh := hinr (s + 1) (by omega) (by omega)
            rw [show (n + 1) - (s + 1) = n - s by omega] at hh
            exact Subobject.factors_of_factors_right ((J.X (n - s)).d s (s + 1)) hh
        have hf := pullback_factors d Q v hv
        exact imageSubobject_le v (P.factorThru v hf) (P.factorThru_arrow v hf)
    apply (pullback_factors_iff d Q _).1
    exact Subobject.factors_of_le _ hle (Subobject.factors_self _)


end CategoryTheory.Functor

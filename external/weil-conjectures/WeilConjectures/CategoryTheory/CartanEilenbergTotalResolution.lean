/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.CategoryTheory.KInjectiveBridge
import WeilConjectures.CategoryTheory.CartanEilenbergAugmentationQuasiIso
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # The augmented Cartan--Eilenberg total complex

Source: blueprint thm-sp-if-e1, proof paragraph 2; Stacks Tags 0133 and 015J.
(blueprint: lem-sp-cartan-eilenberg-total-resolution).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
/-- The total of bounded-below injective rows is a K-injective resolution, with the
augmentation specified on its degree-zero summands.
Source: blueprint thm-sp-if-e1, proof paragraph 2; Stacks Tags 0133 and 015J.
(blueprint: lem-sp-cartan-eilenberg-total-resolution).

Proof.
1. Extend each nonnegative resolution by zero and flip. The maps from K into
resolution degree zero commute with the total differential: their resolution differential
is zero, and their complex differential commutes with the augmentation a. They therefore
assemble into the displayed augmentation.
2. Fix a lower bound b for I. In degree n only resolution degrees 0 through n-b
contribute. Thus the total is zero below b and its terms are finite sums of injectives.
A finite sum of injectives is injective, and a bounded-below complex of injectives is
K-injective by lem-sp-kinjective-computes.
3. After adjusting the cone signs, the cone of the augmentation is the total of
the rows augmented by K^s in resolution degree -1. Each augmented row is acyclic
by hrows. Its filtration by complex degree is finite in every cochain degree;
the associated first page vanishes. Bounded convergence makes the cone
acyclic. Hence the augmentation is a quasi-isomorphism. -/
theorem cartanEilenberg_total_resolution
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex.Plus A)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K.obj ⟶ I)
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (hterms : ∀ (s : ℤ) (r : ℕ), Injective ((I.X s).X r))
    (hrows : ∀ s : ℤ, QuasiIso (a.f s)) :
    ∃ (aug : K.obj ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
        (ComplexShape.up ℤ)),
          (∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
            (HomologicalComplex.extendXIso
              (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
              ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
            (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
              (ComplexShape.up ℤ) 0 n n (zero_add n)) ∧
      QuasiIso aug ∧
      CochainComplex.IsKInjective
        ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
          (ComplexShape.up ℤ)) := by
  classical
  let J := ((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip
  let f (n : ℤ) : K.obj.X n ⟶ (J.total (ComplexShape.up ℤ)).X n :=
    (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      J.ιTotal (ComplexShape.up ℤ) 0 n n (zero_add n)
  -- Only the complex-degree differential survives on the resolution-degree-zero summand.
  have hf (n m : ℤ) (hnm : (ComplexShape.up ℤ).Rel n m) :
      f n ≫ (J.total (ComplexShape.up ℤ)).d n m = K.obj.d n m ≫ f m := by
    have hm : m = n + 1 := by simpa using hnm.symm
    subst m
    dsimp only [f, HomologicalComplex₂.total]
    simp only [Preadditive.comp_add, Category.assoc, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂]
    rw [J.d₁_eq (ComplexShape.up ℤ) (by simp : (ComplexShape.up ℤ).Rel 0 1) n (n + 1)
        (by dsimp [ComplexShape.π]; omega),
      J.d₂_eq (ComplexShape.up ℤ) 0 (by simp : (ComplexShape.up ℤ).Rel n (n + 1)) (n + 1) (by simp)]
    simp only [ComplexShape.ε₁, ComplexShape.ε₂]
    dsimp only [TotalComplexShape.ε₁, TotalComplexShape.ε₂]
    simp only [ComplexShape.ε_zero, one_smul]
    change (a.f n).f 0 ≫ _ ≫
        (((I.X n).extend ComplexShape.embeddingUpNat).d 0 1 ≫ _) +
      (a.f n).f 0 ≫ _ ≫
        ((HomologicalComplex.extendMap (I.d n (n + 1))
          ComplexShape.embeddingUpNat).f 0 ≫ _) = _
    rw [HomologicalComplex.extend_d_eq (I.X n) ComplexShape.embeddingUpNat
        (i := 0) (j := 1) (i' := 0) (j' := 1) rfl rfl,
      HomologicalComplex.extendMap_f (I.d n (n + 1)) ComplexShape.embeddingUpNat
        (i := 0) (i' := 0) rfl]
    simp only [Category.assoc]
    have hv := (a.f n).comm 0 1
    change (a.f n).f 0 ≫ (I.X n).d 0 1 = 0 ≫ (a.f n).f 1 at hv
    simp only [zero_comp] at hv
    simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
      eqToIso]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc ((a.f n).f 0), hv, zero_comp, zero_add]
    have hh := congrArg (fun g ↦ g.f 0) (a.comm n (n + 1))
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_obj_d,
      CochainComplex.single₀_map_f_zero] at hh
    rw [← Category.assoc ((a.f n).f 0), hh, Category.assoc]
  let aug : K.obj ⟶ J.total (ComplexShape.up ℤ) := { f := f, comm' := hf }
  refine ⟨aug, fun n ↦ rfl, ?_, ?_⟩
  · exact cartanEilenberg_augmentation_quasiIso K.obj I a hbelow hrows aug (fun n ↦ rfl)
  · obtain ⟨b, hb⟩ := hbelow
    have hz (r s : ℤ) (h : r < 0 ∨ s < b) : IsZero ((J.X r).X s) := by
      rcases h with h | h
      · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat r
          (fun m hm ↦ by change (m : ℤ) = r at hm; omega)
      · exact (HomologicalComplex.eval A (ComplexShape.up ℤ) r).map_isZero
          ((ComplexShape.embeddingUpNat.extendFunctor A).map_isZero (hb s h))
    have hge : CochainComplex.IsStrictlyGE (J.total (ComplexShape.up ℤ)) b := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro n hn
      rw [IsZero.iff_id_eq_zero]
      apply HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) (K := J)
      intro r s hrs
      have hsum : r + s = n := hrs
      exact (hz r s (by omega)).eq_of_src _ _
    -- The full diagonal coproduct equals the coproduct of these finitely many summands.
    let κ (n : ℤ) : J.CoreHasTotal (ComplexShape.up ℤ) n :=
      { J := { s : ℤ // s ∈ Finset.Icc b n }
        φ₁ := fun s ↦ n - s
        φ₂ := fun s ↦ s
        π_φ := fun s ↦ by dsimp [ComplexShape.π]; omega
        hφ := by
          intro s t h
          apply Subtype.ext
          exact congrArg (fun x : ℤ × ℤ ↦ x.2) h
        isZero := by
          intro r s h hrs
          have hbounds : 0 ≤ r ∧ b ≤ s := by
            constructor <;> by_contra hbad
            · exact hrs (hz r s (Or.inl (by omega)))
            · exact hrs (hz r s (Or.inr (by omega)))
          refine ⟨⟨s, Finset.mem_Icc.mpr ⟨hbounds.2, ?_⟩⟩, ?_, rfl⟩
          · dsimp [ComplexShape.π] at h; omega
          · dsimp [ComplexShape.π] at h; dsimp; omega }
    let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
    have hinj (n : ℤ) : Injective ((J.total (ComplexShape.up ℤ)).X n) := by
      let c := κ n
      let : Finite c.J := by dsimp [c, κ]; infer_instance
      let T : c.J → A := fun s ↦ (J.X (c.φ₁ s)).X (c.φ₂ s)
      have hi (s : c.J) : Injective (T s) := by
        have hr : 0 ≤ n - (s : ℤ) := by
          have := (Finset.mem_Icc.mp s.property).2
          omega
        let r := (n - (s : ℤ)).toNat
        have he : (r : ℤ) = n - (s : ℤ) := Int.toNat_of_nonneg hr
        exact Injective.of_iso
          (HomologicalComplex.extendXIso
            (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s))
            ComplexShape.embeddingUpNat (i := r) (i' := n - (s : ℤ)) he).symm
          (hterms s r)
      -- CoreHasTotal gives a genuine colimit, so no choice of an unproved witness is used.
      let e : (∐ T) ≅ (J.total (ComplexShape.up ℤ)).X n :=
        c.isColimit.coconePointUniqueUpToIso
          (J.toGradedObject.isColimitCofanMapObj
            (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)
      exact Injective.of_iso (biproduct.isoCoproduct T ≪≫ e) inferInstance
    exact CochainComplex.isKInjective_of_injective (J.total (ComplexShape.up ℤ)) b

end CategoryTheory.Functor

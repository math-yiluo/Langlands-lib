import Langlands.AbelianScheme.TorsionFiniteEtaleStatement
import Langlands.AlgebraicGeometry.InfinitesimalKernel
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Finite etale torsion of abelian schemes

Let `A` be an abelian scheme over `S` and let `n` be a natural number invertible on `S`. The
torsion subgroup scheme `A[n]` is etale over `S`: on affine charts, the formal etaleness criterion
reduces to unique lifting of points of `A[n]` along square-zero thickenings, which follows from
smoothness of `A` and unique divisibility of infinitesimal kernels by `n`. It is proper, being
closed in `A`, and locally quasi-finite, being etale, hence finite by Zariski's main theorem.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry

/-- A morphism is locally of finite presentation if its composition with a morphism locally of
finite type is. -/
lemma locallyOfFinitePresentation_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := g (f x)) (U := ⊤) trivial
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := f x) (U := g ⁻¹ᵁ U) hxU
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := f ⁻¹ᵁ V) hxV
  refine ⟨⟨V, hV⟩, ⟨W, hW⟩, hxW, hWV, ?_⟩
  have h₁ := HasRingHomProperty.appLE @LocallyOfFinitePresentation (f ≫ g) inferInstance
    ⟨U, hU⟩ ⟨W, hW⟩ (hWV.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hVU)).le)
  have h₂ := HasRingHomProperty.appLE @LocallyOfFiniteType g inferInstance ⟨U, hU⟩ ⟨V, hV⟩ hVU
  rw [← Scheme.Hom.appLE_comp_appLE f g U V W hVU hWV, CommRingCat.hom_comp] at h₁
  exact RingHom.FinitePresentation.of_comp_finiteType _ h₁ h₂

/-- Etale morphisms are locally quasi-finite. -/
lemma locallyQuasiFinite_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :
    LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h := HasRingHomProperty.appLE @Etale f inferInstance U V e
  let _ := (f.appLE U V e).hom.toAlgebra
  have : Algebra.Etale Γ(Y, U) Γ(X, V) := h
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

namespace TorsionChart

open SquareZero InfinitesimalKernel

variable {S : Scheme.{u}} {S₀ : S.Opens} (hS₀ : IsAffineOpen S₀) {M T : Over S} [GrpObj M]
  [IsCommMonObj M] (j : T ⟶ M) [Mono j] (n : ℕ)
  (htors : ∀ {Y : Over S} (x : Y ⟶ M), (∃ y : Y ⟶ T, y ≫ j = x) ↔ x ^ n = 1)
  (hn : IsUnit (n : Γ(S, S₀)))
  (cV : Chart S₀ T) (cA : Chart S₀ M) (cW : Chart S₀ M)
  (hVA : cV.U ≤ j.left ⁻¹ᵁ cA.U) (hVW : cV.U ≤ (1 : T ⟶ M).left ⁻¹ᵁ cW.U)

include hVW in
lemma range_one_subset {C : Type u} [CommRing C] [Algebra Γ(S, S₀) C]
    (ψ : cV.Ring →ₐ[Γ(S, S₀)] C) : Set.range (1 : testObj hS₀ C ⟶ M).left ⊆ cW.U := by
  rw [← MonObj.comp_one (cV.pt hS₀ ψ)]
  rintro _ ⟨z, rfl⟩
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  exact hVW (cV.range_pt hS₀ ψ ⟨z, rfl⟩)

include hn in
lemma isUnit_natCast {D : Type u} [CommRing D] [Algebra Γ(S, S₀) D] : IsUnit (n : D) := by
  simpa using hn.map (algebraMap Γ(S, S₀) D)

include hS₀ htors hn hVW in
/-- Points of `T` over a square-zero thickening are determined by their reduction. -/
lemma comp_injective {D : Type u} [CommRing D] [Algebra Γ(S, S₀) D] (I : Ideal D)
    (hI : I ^ 2 = ⊥) :
    Function.Injective ((Ideal.Quotient.mkₐ Γ(S, S₀) I).comp :
      (cV.Ring →ₐ[Γ(S, S₀)] D) → cV.Ring →ₐ[Γ(S, S₀)] D ⧸ I) := by
  intro φ₁ φ₂ h
  have hW := range_one_subset hS₀ cV cW hVW ((Ideal.Quotient.mkₐ Γ(S, S₀) I).comp φ₁)
  have hx₁ : (cV.pt hS₀ φ₁ ≫ j) ^ n = 1 := (htors _).mp ⟨_, rfl⟩
  have hx₂ : (cV.pt hS₀ φ₂ ≫ j) ^ n = 1 := (htors _).mp ⟨_, rfl⟩
  have hr : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫
      ((cV.pt hS₀ φ₁ ≫ j) * (cV.pt hS₀ φ₂ ≫ j)⁻¹) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
      cV.testHom_comp_pt, cV.testHom_comp_pt, h, mul_inv_cancel]
  have hrn : ((cV.pt hS₀ φ₁ ≫ j) * (cV.pt hS₀ φ₂ ≫ j)⁻¹) ^ n = 1 := by
    rw [mul_pow, inv_pow, hx₁, hx₂, inv_one, mul_one]
  have h1 := eq_one_of_pow_eq_one hS₀ hI cW hW n (isUnit_natCast n hn) _ hr hrn
  exact cV.pt_injective hS₀ ((cancel_mono j).mp (mul_inv_eq_one.mp h1))

include hS₀ htors hn hVA hVW in
/-- Points of `T` over the reduction of a square-zero thickening lift. -/
lemma comp_surjective [Algebra.FormallySmooth Γ(S, S₀) cA.Ring] {D : Type u} [CommRing D]
    [Algebra Γ(S, S₀) D] (I : Ideal D) (hI : I ^ 2 = ⊥) :
    Function.Surjective ((Ideal.Quotient.mkₐ Γ(S, S₀) I).comp :
      (cV.Ring →ₐ[Γ(S, S₀)] D) → cV.Ring →ₐ[Γ(S, S₀)] D ⧸ I) := by
  intro φ
  have hW := range_one_subset hS₀ cV cW hVW φ
  have hrange : Set.range (cV.pt hS₀ φ ≫ j).left ⊆ cA.U := by
    rintro _ ⟨z, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hVA (cV.range_pt hS₀ φ ⟨z, rfl⟩)
  obtain ⟨χ, hχ⟩ := cA.exists_pt hS₀ _ hrange
  have hInil : IsNilpotent I := ⟨2, hI.trans Ideal.zero_eq_bot.symm⟩
  have hx₀ : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫
      cA.pt hS₀ (Algebra.FormallySmooth.lift I hInil χ) =
      cV.pt hS₀ φ ≫ j := by
    rw [cA.testHom_comp_pt, Algebra.FormallySmooth.comp_lift, hχ]
  have hk : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫
      cA.pt hS₀ (Algebra.FormallySmooth.lift I hInil χ) ^ n =
      1 := by
    rw [MonObj.comp_pow, hx₀]
    exact (htors _).mp ⟨_, rfl⟩
  obtain ⟨r, hr, hrn⟩ := exists_pow_eq hS₀ hI cW hW n (isUnit_natCast n hn) _ hk
  have hxn : (cA.pt hS₀ (Algebra.FormallySmooth.lift I hInil χ) *
      r⁻¹) ^ n = 1 := by
    rw [mul_pow, inv_pow, hrn, mul_inv_cancel]
  have hxmk : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫
      (cA.pt hS₀ (Algebra.FormallySmooth.lift I hInil χ) * r⁻¹) =
      cV.pt hS₀ φ ≫ j := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hx₀, hr, inv_one, mul_one]
  obtain ⟨y, hy⟩ := (htors _).mpr hxn
  have hymk : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫ y = cV.pt hS₀ φ := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hy, hxmk]
  have hyrange : Set.range y.left ⊆ cV.U := by
    rw [← range_testHom_comp hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I)
      (Ideal.Quotient.mkₐ_surjective Γ(S, S₀) I) (isNilpotent_ker_mk hI) y, hymk]
    exact cV.range_pt hS₀ φ
  obtain ⟨ψ, rfl⟩ := cV.exists_pt hS₀ y hyrange
  exact ⟨ψ, cV.pt_injective hS₀ (by rw [← cV.testHom_comp_pt, hymk])⟩

include hS₀ htors hn hVA hVW in
/-- The chart ring of `T` is formally etale. -/
lemma formallyEtale [Algebra.FormallySmooth Γ(S, S₀) cA.Ring] :
    Algebra.FormallyEtale Γ(S, S₀) cV.Ring := by
  rw [Algebra.FormallyEtale.iff_comp_bijective]
  intro D _ _ I hI
  exact ⟨comp_injective hS₀ j n htors hn cV cW hVW I hI,
    comp_surjective hS₀ j n htors hn cV cA cW hVA hVW I hI⟩

end TorsionChart

end Langlands.AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.GroupScheme

variable {S : Scheme.{u}} (A : AbelianScheme S) (n : ℕ)

/-- The torsion scheme is locally of finite presentation over the base. -/
lemma torsion_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (torsion A.toGrp (n : ℤ)).X.hom := by
  have : LocallyOfFinitePresentation (η[A.toGrp.X].left ≫ A.toGrp.X.hom) := by
    rw [Over.w η[A.toGrp.X]]
    exact (inferInstance : LocallyOfFinitePresentation (𝟙 S))
  have : LocallyOfFinitePresentation η[A.toGrp.X].left :=
    locallyOfFinitePresentation_of_comp _ A.toGrp.X.hom
  have : LocallyOfFinitePresentation (torsionι A.toGrp (n : ℤ)).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (torsion_isPullback_scheme A.toGrp (n : ℤ)).flip this
  rw [← Over.w (torsionι A.toGrp (n : ℤ)).hom.hom]
  infer_instance

/-- The torsion scheme is proper over the base. -/
lemma torsion_isProper : IsProper (torsion A.toGrp (n : ℤ)).X.hom := by
  rw [← Over.w (torsionι A.toGrp (n : ℤ)).hom.hom]
  infer_instance

/-- A point of the abelian scheme factors through the `n`-torsion exactly when it is killed
by `n`. -/
lemma exists_torsion_lift_iff {Y : Over S} (x : Y ⟶ A.toGrp.X) :
    (∃ y : Y ⟶ (torsion A.toGrp (n : ℤ)).X, y ≫ (torsionι A.toGrp (n : ℤ)).hom.hom = x) ↔
      x ^ n = 1 := by
  rw [← zpow_natCast, ← existsUnique_torsion_lift_iff A.toGrp (n : ℤ) Y x]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy, fun y' hy' => (cancel_mono (torsionι A.toGrp (n : ℤ)).hom.hom).mp
      (hy'.trans hy.symm)⟩
  · exact fun h => h.exists

/-- The torsion scheme is etale over the base when `n` is invertible. -/
theorem torsion_etale (hn : IsUnit (n : Γ(S, ⊤))) :
    Etale (torsion A.toGrp (n : ℤ)).X.hom := by
  have hLFP := torsion_locallyOfFinitePresentation A n
  rw [HasRingHomProperty.iff_exists_appLE (P := @Etale)
    (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      (RingHom.Etale.propertyIsLocal.HoldsForLocalizationAway
        RingHom.Etale.containsIdentities)).left]
  intro x
  obtain ⟨S₀, hS₀, hxS₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := (torsion A.toGrp (n : ℤ)).X.hom x) (U := ⊤) trivial
  have h1x : (1 : (torsion A.toGrp (n : ℤ)).X ⟶ A.toGrp.X).left x ∈ A.toGrp.X.hom ⁻¹ᵁ S₀ := by
    change A.toGrp.X.hom ((1 : (torsion A.toGrp (n : ℤ)).X ⟶ A.toGrp.X).left x) ∈ S₀
    rw [← Scheme.Hom.comp_apply, Over.w]
    exact hxS₀
  have hιx : (torsionι A.toGrp (n : ℤ)).hom.hom.left x ∈ A.toGrp.X.hom ⁻¹ᵁ S₀ := by
    change A.toGrp.X.hom ((torsionι A.toGrp (n : ℤ)).hom.hom.left x) ∈ S₀
    rw [← Scheme.Hom.comp_apply, Over.w]
    exact hxS₀
  obtain ⟨W, hW, hxW, hWS⟩ := exists_isAffineOpen_mem_and_subset h1x
  obtain ⟨UA, hUA, hxUA, hUAS⟩ := exists_isAffineOpen_mem_and_subset hιx
  obtain ⟨V, hV, hxV, hVsub⟩ := exists_isAffineOpen_mem_and_subset
    (U := (torsionι A.toGrp (n : ℤ)).hom.hom.left ⁻¹ᵁ UA ⊓
      (1 : (torsion A.toGrp (n : ℤ)).X ⟶ A.toGrp.X).left ⁻¹ᵁ W)
    (TopologicalSpace.Opens.mem_inf.mpr ⟨hxUA, hxW⟩)
  have hVS : V ≤ (torsion A.toGrp (n : ℤ)).X.hom ⁻¹ᵁ S₀ := by
    intro v hv
    have h := hUAS (TopologicalSpace.Opens.mem_inf.mp (hVsub hv)).1
    change A.toGrp.X.hom ((torsionι A.toGrp (n : ℤ)).hom.hom.left v) ∈ S₀ at h
    change (torsion A.toGrp (n : ℤ)).X.hom v ∈ S₀
    rwa [← Scheme.Hom.comp_apply, Over.w] at h
  refine ⟨⟨S₀, hS₀⟩, ⟨V, hV⟩, hxV, hVS, ?_⟩
  let cV : Chart S₀ (torsion A.toGrp (n : ℤ)).X := ⟨V, hV, hVS⟩
  let cA : Chart S₀ A.toGrp.X := ⟨UA, hUA, hUAS⟩
  let cW : Chart S₀ A.toGrp.X := ⟨W, hW, hWS⟩
  have hnS₀ : IsUnit (n : Γ(S, S₀)) := by
    simpa using hn.map (S.presheaf.map (homOfLE le_top).op).hom
  have : Algebra.Smooth Γ(S, S₀) cA.Ring :=
    HasRingHomProperty.appLE @Smooth A.toGrp.X.hom inferInstance ⟨S₀, hS₀⟩ ⟨UA, hUA⟩ hUAS
  have : Algebra.FinitePresentation Γ(S, S₀) cV.Ring :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation _ hLFP ⟨S₀, hS₀⟩ ⟨V, hV⟩ hVS
  have : Algebra.FormallyEtale Γ(S, S₀) cV.Ring :=
    TorsionChart.formallyEtale hS₀ (torsionι A.toGrp (n : ℤ)).hom.hom n
      (fun x => exists_torsion_lift_iff A n x) hnS₀ cV cA cW
      (fun v hv => (TopologicalSpace.Opens.mem_inf.mp (hVsub hv)).1)
      (fun v hv => (TopologicalSpace.Opens.mem_inf.mp (hVsub hv)).2)
  exact (RingHom.etale_algebraMap (R := Γ(S, S₀)) (S := cV.Ring)).mpr
    ⟨inferInstance, inferInstance⟩

/-- Positive torsion of an abelian scheme is finite etale when its order is invertible. -/
theorem torsionFiniteEtale : TorsionFiniteEtaleStatement.{u} := by
  intro S A n _ hn
  have := torsion_etale A n hn
  have := torsion_isProper A n
  have := locallyQuasiFinite_of_etale (torsion A.toGrp (n : ℤ)).X.hom
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, inferInstance⟩

end Langlands.AbelianScheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.CohomologyPowersIdealApplication
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Cohomology reductions: ImageStabilization
Source: Stacks Project, Lemma 02OB. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem power_zero_isIso {X : Scheme.{u}} (J : X.IdealSheafData)
    (F : X.Modules) :
    IsIso (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι 0).2 F) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  dsimp only [Scheme.idealSheafPower, Scheme.idealModuleProductι]
  have : Epi (image.ι
      (MonoidalCategory.whiskerRight (C := X.Modules)
        (𝟙 (SheafOfModules.unit X.ringCatSheaf : X.Modules)) F ≫
        (MonoidalCategory.leftUnitor (C := X.Modules) F).hom)) := epi_image_of_epi _
  exact isIso_of_mono_of_epi _

/-- Proof: put J = I O_X and apply cohomology_powers_ideal_application in degree
p+1, obtaining c. The exact sequences of 0 -> J^k F -> F -> F/J^k F -> 0
and 0 -> J^n F -> F -> F/J^n F -> 0 form a natural ladder. Write delta_k for
the connecting map and alpha_(k,n) for H^(p+1)(J^k F) -> H^(p+1)(J^n F).
For x in H^p(F/J^k F), delta_k(x) lies in the kernel of the map to H^(p+1)(F).
The kernel equality of the cited lemma says it maps to zero at exponent k-c.
For k >= n+c, the transition to exponent n factors through exponent k-c, so
alpha_(k,n)(delta_k(x)) = 0. Naturality gives delta_n(tau_(k,n)(x)) = 0,
and exactness places tau_(k,n)(x) in the image of H^p(F). Conversely the quotient
maps satisfy tau_(k,n) rho_k = rho_n, giving the reverse inclusion of images.
This argument uses only positive quotient levels, including n = 1 and c = 0.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OB,
part (3) (blueprint: ml-cohomology-powers-ideal-image-stabilization). -/
theorem ml_cohomology_powers_ideal_image_stabilization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (I : Ideal A) (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (p : ℕ) :
    ∃ c : ℕ,
      (∀ (n k : ℕ), 1 ≤ n → ∀ h : n + c ≤ k,
        Set.range (((RingedSpace.moduleCohomology X.toRingedSpace p).map
          (formalModuleQuotientMap
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f)
            (𝟙 F) (Nat.le_trans (Nat.le_add_right n c) h))).hom) =
        Set.range (((RingedSpace.moduleCohomology X.toRingedSpace p).map
          (formalModuleQuotientπ
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f) n F)).hom)) := by
  classical
  let J := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f
  let P (n : ℕ) := Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F
  let j (n : ℕ) : P n ⟶ F :=
    Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F
  have hj (n : ℕ) : Mono (j n) := by
    dsimp [j, Scheme.idealModuleProductι]
    infer_instance
  let S (n : ℕ) : ShortComplex X.Modules :=
    ShortComplex.mk (j n) (formalModuleQuotientπ J n F) (cokernel.condition (j n))
  have hs (n : ℕ) : (S n).ShortExact := by
    refine { exact := ShortComplex.exact_cokernel (j n), mono_f := hj n, epi_g := ?_ }
    change Epi (cokernel.π (j n))
    infer_instance
  obtain ⟨i, hi, c, _, hc⟩ :=
    cohomology_powers_ideal_application A I f J rfl F hF (p + 1)
  -- The inclusions into F are monic, so transitions compose uniquely.
  have hcomp (k l n : ℕ) (h₁ : l ≤ k) (h₂ : n ≤ l) :
      i k l h₁ ≫ i l n h₂ = i k n (h₂.trans h₁) := by
    apply (cancel_mono (j n)).1
    dsimp only [j]
    simp only [Category.assoc, hi]
  obtain ⟨G, hG⟩ := (sheafCohomologyAndHigherDirectImages.{u, u + 1, u + 1} X).1
  rcases G with ⟨H, hadd, δ, hmono, hmiddle, hright, hleft, hnat⟩
  dsimp only at hG
  subst H
  let H := RingedSpace.moduleCohomology X.toRingedSpace
  have hπ (k n : ℕ) (h : n ≤ k) :
      formalModuleQuotientπ J k F ≫ formalModuleQuotientMap J (𝟙 F) h =
        formalModuleQuotientπ J n F := by
    simp [formalModuleQuotientπ, formalModuleQuotientMap]
  have hnat' (k n : ℕ) (h : n ≤ k) :
      δ (S k) (hs k) p ≫ (H (p + 1)).map (i k n h) =
        (H p).map (formalModuleQuotientMap J (𝟙 F) h) ≫ δ (S n) (hs n) p := by
    let φ : S k ⟶ S n :=
      { τ₁ := i k n h
        τ₂ := 𝟙 F
        τ₃ := formalModuleQuotientMap J (𝟙 F) h
        comm₁₂ := by simpa [S, j] using hi k n h
        comm₂₃ := by simpa [S] using (hπ k n h).symm }
    exact hnat (S k) (S n) (hs k) (hs n) φ p
  refine ⟨c, ?_⟩
  intro n k hn h
  let hnk : n ≤ k := (Nat.le_add_right n c).trans h
  change Set.range ((H p).map (formalModuleQuotientMap J (𝟙 F) hnk)).hom =
    Set.range ((H p).map (formalModuleQuotientπ J n F)).hom
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    let y := (δ (S k) (hs k) p).hom x
    obtain ⟨hz, _⟩ := hleft (S k) (hs k) p
    have hy : ((H (p + 1)).map (j k)).hom y = 0 := by
      exact congrArg (fun t ↦ t.hom x) hz
    have hzeroIso : IsIso (j 0) := power_zero_isIso J F
    have hzeroMono : Mono ((H (p + 1)).map (j 0)) := inferInstance
    have hy0 : ((H (p + 1)).map (i k 0 (Nat.zero_le k))).hom y = 0 := by
      apply (ModuleCat.mono_iff_injective _).1 hzeroMono
      change (((H (p + 1)).map (i k 0 (Nat.zero_le k)) ≫
        (H (p + 1)).map (j 0)).hom y) = _
      rw [← Functor.map_comp, hi]
      simpa using hy
    have hkc : c ≤ k := le_trans (Nat.le_add_left c n) h
    -- Restricting scalars does not change the underlying kernel condition.
    have hyc : ((H (p + 1)).map (i k (k - c) (Nat.sub_le k c))).hom y = 0 := by
      have he := congrArg (fun K ↦ y ∈ K) (hc k hkc)
      change (((H (p + 1)).map (i k 0 (Nat.zero_le k))).hom y = 0) =
        (((H (p + 1)).map (i k (k - c) (Nat.sub_le k c))).hom y = 0) at he
      exact he.mp hy0
    -- The transition to n factors through the level k - c.
    have hnc : n ≤ k - c := Nat.le_sub_of_add_le h
    have hyn : ((H (p + 1)).map (i k n hnk)).hom y = 0 := by
      rw [← hcomp k (k - c) n (Nat.sub_le k c) hnc, Functor.map_comp]
      change ((H (p + 1)).map (i (k - c) n hnc)).hom
        (((H (p + 1)).map (i k (k - c) (Nat.sub_le k c))).hom y) = 0
      rw [hyc, map_zero]
    have hδ : (δ (S n) (hs n) p).hom
        (((H p).map (formalModuleQuotientMap J (𝟙 F) hnk)).hom x) = 0 := by
      have he := congrArg (fun t ↦ t.hom x) (hnat' k n hnk)
      exact he.symm.trans hyn
    obtain ⟨_, hex⟩ := hright (S n) (hs n) p
    change _ ∈ LinearMap.range ((H p).map (formalModuleQuotientπ J n F)).hom
    rw [hex.moduleCat_range_eq_ker]
    exact hδ
  · rintro _ ⟨x, rfl⟩
    refine ⟨((H p).map (formalModuleQuotientπ J k F)).hom x, ?_⟩
    change (((H p).map (formalModuleQuotientπ J k F) ≫
      (H p).map (formalModuleQuotientMap J (𝟙 F) hnk)).hom x) = _
    rw [← Functor.map_comp, hπ]

end AlgebraicGeometry

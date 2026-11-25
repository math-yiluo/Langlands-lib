/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.AffineComplement

/-! # A finite affine section cover in one positive tensor power

Source: Stacks Project, Morphisms, Lemma 01VS, first proof paragraph;
Properties, Definition 01PS.
(blueprint: lem-weil-pbc-ample-finite-common-power-cover).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Ampleness gives finitely many affine section loci in one positive tensor power.

Source: Stacks Project, Morphisms, Lemma 01VS, first proof paragraph;
Properties, Definition 01PS.
(blueprint: lem-weil-pbc-ample-finite-common-power-cover).

Proof:
1. Choose an affine nonvanishing locus of a positive-degree section through each point,
   using absolute ampleness. Quasi-compactness gives a finite subcover.
2. Take the product m of their positive degrees. Raise each section to the quotient
   m / n of degrees, and transport it by the tensor-power exponent isomorphism.
   Locally in a rank-one trivialization, its coefficient is raised to a positive power;
   a coefficient is a unit exactly when that positive power is a unit. Thus the loci
   remain unchanged and affine, and they still cover.
3. A global section corresponds to a morphism from the structure module by evaluation
   at one. For an invertible module its nonvanishing germ locus equals the complement
   of the support of its zero locus: in a rank-one stalk both say the coefficient is a
   unit. Use this identification to express the cover in the source library's convention.
4. Add a degree-one zero section to the finite subcover, giving a nonempty family
   indexed by Option of the finite index type. Its empty affine locus leaves the cover
   unchanged. This also handles an empty scheme and an empty subcover: the product
   degree is one and the zero section covers the empty scheme. Enumerate the resulting
   common-degree family by ULift (Fin (r + 1)). -/
theorem IsAmple.exists_finite_common_power_cover (X : Scheme.{u}) (L : X.Modules)
    [L.IsInvertible] (hL : IsAmple X L) :
    ∃ (m : ℕ) (_ : 0 < m) (r : ℕ)
      (s : ULift.{u} (Fin (r + 1)) → (𝟙_ X.Modules ⟶ L.tensorPow m)),
      (∀ i, IsAffineOpen (Hom.zeroLocus (s i)).support.compl) ∧
      (⨆ i, (Hom.zeroLocus (s i)).support.compl) = ⊤ := by
  classical
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ X.Modules) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  let : CompactSpace X := hL.1
  choose n hn a U hx hU ha using hL.2
  let σ (x : X) : 𝟙_ X.Modules ⟶ L.tensorPow (n x) :=
    homOfGlobalSection _ (a x)
  have hσ (x : X) : (Hom.zeroLocus (σ x)).support.compl = U x := by
    ext y
    exact (ha x y).trans
      (Set.ext_iff.mp (nonvanishingLocus_eq_compl_support_zeroLocus X _ (a x)) y)
      |>.symm
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (U x : Set X))
    (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let β := Option t
  let d : β → ℕ := fun i ↦ i.elim 1 (fun x ↦ n x.1)
  let b : (i : β) → (𝟙_ X.Modules ⟶ L.tensorPow (d i)) :=
    fun i ↦ match i with
    | none => 0
    | some x => σ x.1
  have hd (i : β) : 0 < d i := by
    cases i with
    | none => exact Nat.zero_lt_one
    | some x => exact hn x.1
  have hb (i : β) : IsAffineOpen (Hom.zeroLocus (b i)).support.compl := by
    cases i with
    | none =>
      have := IsInvertible.sheafOfModules_isInvertible (L.tensorPow 1)
      have hz := (Hom.zeroLocus_eq_bot_iff
        (0 : 𝟙_ X.Modules ⟶ L.tensorPow 1)).mpr rfl
      have hempty : (Hom.zeroLocus (b none)).support.compl = ⊥ := by
        change (Hom.zeroLocus (0 : 𝟙_ X.Modules ⟶ L.tensorPow 1)).support.compl = ⊥
        rw [hz, IdealSheafData.support_bot]
        ext x
        simp
      rw [hempty]
      exact isAffineOpen_bot X
    | some x => simpa only [b, hσ] using hU x.1
  have hcov : (⨆ i, (Hom.zeroLocus (b i)).support.compl) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨some ⟨y, hy⟩, ?_⟩
    change x ∈ (Hom.zeroLocus (σ y)).support.compl
    rw [hσ]
    exact hxy
  let m := ∏ i : β, d i
  have hm : 0 < m := Finset.prod_pos (fun i _ ↦ hd i)
  have hdiv (i : β) : d i ∣ m := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have hq (i : β) : 0 < m / d i := Nat.div_pos (Nat.le_of_dvd hm (hdiv i)) (hd i)
  let e (i : β) : (L.tensorPow (d i)).tensorPow (m / d i) ≅ L.tensorPow m :=
    (L.tensorPowMulIso (d i) (m / d i)).symm ≪≫
      eqToIso (congrArg L.tensorPow (Nat.mul_div_cancel' (hdiv i)))
  let c (i : β) : 𝟙_ X.Modules ⟶ L.tensorPow m :=
    tensorPowSection (b i) (m / d i) ≫ (e i).hom
  have hc (i : β) : (Hom.zeroLocus (c i)).support.compl =
      (Hom.zeroLocus (b i)).support.compl := by
    have := IsInvertible.sheafOfModules_isInvertible (L.tensorPow m)
    have := IsInvertible.sheafOfModules_isInvertible
      ((L.tensorPow (d i)).tensorPow (m / d i))
    rw [show Hom.zeroLocus (c i) = Hom.zeroLocus
      (tensorPowSection (b i) (m / d i)) from
        (Hom.zeroLocus_eq_of_arrowIso
          (tensorPowSection (b i) (m / d i)) (c i)
          (Arrow.isoMk (Iso.refl _) (e i) (by simp [c]))).symm]
    exact compl_support_zeroLocus_tensorPowSection _ _ (hq i)
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := β))
  let f : ULift.{u} (Fin (r + 1)) ≃ β :=
    Equiv.ulift.trans (Fintype.equivFinOfCardEq hr).symm
  refine ⟨m, hm, r, fun i ↦ c (f i), fun i ↦ (hc (f i)).symm ▸ hb (f i), ?_⟩
  calc
    (⨆ i, (Hom.zeroLocus (c (f i))).support.compl) =
        ⨆ i, (Hom.zeroLocus (b (f i))).support.compl := iSup_congr (fun i ↦ hc (f i))
    _ = ⨆ i, (Hom.zeroLocus (b i)).support.compl := f.surjective.iSup_comp
      (fun i ↦ (Hom.zeroLocus (b i)).support.compl)
    _ = ⊤ := hcov

end AlgebraicGeometry.Scheme.Modules

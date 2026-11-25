/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.FixedChartMap
import WeilConjectures.Algebra.Module.ProjAwayDegreeZeroExactPair
import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties

/-!
# Exact maps on fixed associated graded-module sheaves

## References

* Stacks Project, Tag 01M7, final paragraph
* Stacks Project, Constructions, Tag 01M7, final paragraph
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem basis_chain_exact
    (X : Scheme.{u}) (B : Set X.Opens) (hB : Opens.IsBasis B)
    (F₂ F₁ F₀ F : X.Modules) (g₂ : F₂ ⟶ F₁) (g₁ : F₁ ⟶ F₀) (g₀ : F₀ ⟶ F)
    (hsections : ∀ U ∈ B,
      Function.Injective (g₂.val.app (op U)) ∧
      Function.Exact (g₂.val.app (op U)) (g₁.val.app (op U)) ∧
      Function.Exact (g₁.val.app (op U)) (g₀.val.app (op U)) ∧
      Function.Surjective (g₀.val.app (op U))) :
    Mono g₂ ∧ Epi g₀ ∧ (ComposableArrows.mk₃ g₂ g₁ g₀).Exact := by
  classical
  have hcover (W : X.Opens) :
      (⨆ U : {U : X.Opens // U ∈ B ∧ U ≤ W}, U.val) = W := by
    apply le_antisymm
    · exact iSup_le fun U ↦ U.property.2
    · intro x hx
      obtain ⟨U, hUB, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.mp hB hx
      exact Opens.mem_iSup.mpr ⟨⟨U, hUB, hUW⟩, hxU⟩
  have hnat {K L : X.Modules} (φ : K ⟶ L) (V W : X.Opens) (hVW : V ≤ W)
      (s : K.val.obj (op W)) :
      φ.val.app (op V) (K.val.map (homOfLE hVW).op s) =
        L.val.map (homOfLE hVW).op (φ.val.app (op W) s) := by
    exact ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hVW).op) s
  have hsep (K : X.Modules) (W : X.Opens) (s t : K.val.obj (op W))
      (heq : ∀ (U : X.Opens) (hUB : U ∈ B) (hUW : U ≤ W),
        K.val.map (homOfLE hUW).op s = K.val.map (homOfLE hUW).op t) : s = t := by
    exact TopCat.Sheaf.eq_of_locally_eq' ⟨K.presheaf, K.isSheaf⟩
      (fun U : {U : X.Opens // U ∈ B ∧ U ≤ W} ↦ U.val) W
      (fun U ↦ homOfLE U.property.2) (le_of_eq (hcover W).symm) s t
      (fun U ↦ heq U.val U.property.1 U.property.2)
  have hpair {K L N : X.Modules} (i : K ⟶ L) (q : L ⟶ N)
      (hex : ∀ U ∈ B, Function.Exact (i.val.app (op U)) (q.val.app (op U))) :
      ∃ h : i ≫ q = 0, (ShortComplex.mk i q h).Exact := by
    have h : i ≫ q = 0 := by
      ext W s
      change q.val.app (op W) (i.val.app (op W) s) = 0
      apply hsep N W
      intro U hUB hUW
      rw [← hnat, ← hnat]
      simpa using (hex U hUB).apply_apply_eq_zero (K.val.map (homOfLE hUW).op s)
    refine ⟨h, ?_⟩
    apply ((RingedSpace.module_exactness_local_lifting X.toRingedSpace).2.2 K L N i q h).mpr
    intro W s hs
    let I := {U : X.Opens // U ∈ B ∧ U ≤ W}
    have hlift : ∀ U : I, ∃ f : K.val.obj (op U.val),
        i.val.app (op U.val) f = L.val.map (homOfLE U.property.2).op s := by
      intro U
      apply ((hex U.val U.property.1) _).mp
      rw [hnat, hs]
      exact map_zero _
    choose f hf using hlift
    exact ⟨I, fun U ↦ U.val, fun U ↦ U.property.2, f, hcover W, hf⟩
  have hmono : Mono g₂ := by
    constructor
    intro K a b hab
    ext W s
    apply hsep F₂ W
    intro U hUB hUW
    apply (hsections U hUB).1
    rw [hnat, hnat]
    exact congrArg (fun φ : K ⟶ F₁ ↦ φ.val.app (op W) s) hab |> congrArg
      ((F₁.val.map (homOfLE hUW).op))
  have hepi : Epi g₀ := by
    apply ((RingedSpace.module_exactness_local_lifting X.toRingedSpace).2.1 F₀ F g₀).2.mp
    intro W t
    let I := {U : X.Opens // U ∈ B ∧ U ≤ W}
    have hlift : ∀ U : I, ∃ g : F₀.val.obj (op U.val),
        g₀.val.app (op U.val) g = F.val.map (homOfLE U.property.2).op t := by
      intro U
      exact (hsections U.val U.property.1).2.2.2 _
    choose g hg using hlift
    exact ⟨I, fun U ↦ U.val, fun U ↦ U.property.2, g, hcover W, hg⟩
  obtain ⟨hc₂, he₂⟩ := hpair g₂ g₁ (fun U hU ↦ (hsections U hU).2.1)
  obtain ⟨hc₁, he₁⟩ := hpair g₁ g₀ (fun U hU ↦ (hsections U hU).2.2.1)
  refine ⟨hmono, hepi, ?_⟩
  apply ComposableArrows.exact_of_δ₀
  · exact ComposableArrows.exact₂_mk _ hc₂ he₂
  · exact ComposableArrows.exact₂_mk _ hc₁ he₁

/-- Fixed associated sheaves of an exact graded chain admit an exact chain of maps. -/
theorem graded_chain_maps_exact (k : Type u) [Field k]
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (F : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f M)
    (halpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f))
    (hscalar : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • alpha f d hd hf s)
    (hres : ∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : M)
          (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha g b hb hg (F.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (A : Fin 3 → ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝒢 : ∀ i : Fin 3, ℤ → AddSubgroup (A i))
    (f₂ : A 2 →ₗ[MvPolynomial (Fin 2) k] A 1)
    (f₁ : A 1 →ₗ[MvPolynomial (Fin 2) k] A 0)
    (f₀ : A 0 →ₗ[MvPolynomial (Fin 2) k] M)
    (h𝒢 : ∀ i : Fin 3, DirectSum.IsInternal (𝒢 i))
    (hA_smul : ∀ (i : Fin 3) (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : A i),
        s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒢 i j →
          s • x ∈ 𝒢 i ((n : ℤ) + j))
    (hf₂ : ∀ (j : ℤ) (x : A 2), x ∈ 𝒢 2 j → f₂ x ∈ 𝒢 1 j)
    (hf₁ : ∀ (j : ℤ) (x : A 1), x ∈ 𝒢 1 j → f₁ x ∈ 𝒢 0 j)
    (hf₀ : ∀ (j : ℤ) (x : A 0), x ∈ 𝒢 0 j → f₀ x ∈ 𝓜 j)
    (hinj : Function.Injective f₂) (hex₁ : LinearMap.range f₂ = LinearMap.ker f₁)
    (hex₀ : LinearMap.range f₁ = LinearMap.ker f₀) (hsurj : Function.Surjective f₀)
    (E : Fin 3 → (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (hE : (∀ i : Fin 3,
        ∃ (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
          0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
          (E i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
            LocalizedModule.Away f (A i)),
          (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
            (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
            Function.Injective (alpha f d hd hf) ∧
            Set.range (alpha f d hd hf) = degreeZeroFractions
              (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
              (fun n : ℕ ↦ (𝒢 i n : Set (A i))) (Submonoid.powers f)) ∧
          (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
            (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
            (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (s : (E i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
            alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
              algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
                (Localization.Away f) r • alpha f d hd hf s) ∧
          (∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
            (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
            (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
            (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
              basicOpen (homogeneousSubmodule (Fin 2) k) f)
            (e c : ℕ) (a : MvPolynomial (Fin 2) k),
            0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
            ∀ (m : ℕ) (y : A i)
              (s : (E i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
              alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
              alpha g b hb hg ((E i).val.map (homOfLE inc).op s) =
                mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)))) :
    ∃ (g₂ : E 2 ⟶ E 1) (g₁ : E 1 ⟶ E 0) (g₀ : E 0 ⟶ F),
      Mono g₂ ∧ Epi g₀ ∧ (ComposableArrows.mk₃ g₂ g₁ g₀).Exact := by
  classical
  choose alphaE hcharts hscalars hrestrictions using hE
  obtain ⟨g₂, hg₂⟩ := fixed_chart_map k
    (A 2) (𝒢 2) (E 2) (alphaE 2) (hcharts 2)
    (hscalars 2) (hrestrictions 2)
    (A 1) (𝒢 1) (E 1) (alphaE 1) (hcharts 1)
    (hscalars 1) (hrestrictions 1) f₂ hf₂
  obtain ⟨g₁, hg₁⟩ := fixed_chart_map k
    (A 1) (𝒢 1) (E 1) (alphaE 1) (hcharts 1)
    (hscalars 1) (hrestrictions 1)
    (A 0) (𝒢 0) (E 0) (alphaE 0) (hcharts 0)
    (hscalars 0) (hrestrictions 0) f₁ hf₁
  obtain ⟨g₀, hg₀⟩ := fixed_chart_map k
    (A 0) (𝒢 0) (E 0) (alphaE 0) (hcharts 0)
    (hscalars 0) (hrestrictions 0)
    M 𝓜 F alpha halpha hscalar hres f₀ hf₀
  refine ⟨g₂, g₁, g₀, ?_⟩
  let B : Set (Proj (homogeneousSubmodule (Fin 2) k)).Opens :=
    {U | ∃ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d ∧ f ∈ homogeneousSubmodule (Fin 2) k d ∧
        U = basicOpen (homogeneousSubmodule (Fin 2) k) f}
  apply basis_chain_exact _ B
    (standardOpenProperties.{u, u, u} (homogeneousSubmodule (Fin 2) k)).1
  rintro U ⟨f, d, hd, hf, rfl⟩
  have hex₂ : Function.Exact f₂ f₁ := by
    intro y
    rw [← LinearMap.mem_ker, ← hex₁]
    rfl
  have hex₁' : Function.Exact f₁ f₀ := by
    intro y
    rw [← LinearMap.mem_ker, ← hex₀]
    rfl
  let N : Fin 3 → ModuleCat.{u} (MvPolynomial (Fin 2) k) := ![A 2, A 1, A 0]
  let H : ∀ j, ℤ → AddSubgroup (N j) :=
    Fin.cases (𝒢 2) (Fin.cases (𝒢 1) (Fin.cases (𝒢 0) (fun i ↦ Fin.elim0 i)))
  let T : Fin 3 → (Proj (homogeneousSubmodule (Fin 2) k)).Modules := ![E 2, E 1, E 0]
  let a : ∀ j, (T j).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
      LocalizedModule.Away f (N j) :=
    Fin.cases (alphaE 2 f d hd hf)
      (Fin.cases (alphaE 1 f d hd hf) (Fin.cases (alphaE 0 f d hd hf) (fun i ↦ Fin.elim0 i)))
  have hN : ∀ j, DirectSum.IsInternal (H j) := by
    exact Fin.cases (h𝒢 2) (Fin.cases (h𝒢 1) (Fin.cases (h𝒢 0) (fun i ↦ Fin.elim0 i)))
  have hNs : ∀ (j : Fin 3) (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : N j),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ H j z → a • y ∈ H j (n + z) := by
    exact Fin.cases (hA_smul 2)
      (Fin.cases (hA_smul 1) (Fin.cases (hA_smul 0) (fun i ↦ Fin.elim0 i)))
  have ha : ∀ j, Function.Injective (a j) ∧ Set.range (a j) = degreeZeroFractions
      (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
      (fun n : ℕ ↦ (H j n : Set (N j))) (Submonoid.powers f) := by
    exact Fin.cases (hcharts 2 f d hd hf)
      (Fin.cases (hcharts 1 f d hd hf) (Fin.cases (hcharts 0 f d hd hf) (fun i ↦ Fin.elim0 i)))
  obtain ⟨hexL, hinjL, _⟩ := proj_away_degreeZero_exact_pair k (fun j ↦ N j) H hN hNs f d hd hf
    (fun j ↦ (T j).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))) a ha
    f₂ f₁ hf₂ hf₁ hex₂
    (g₂.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))).hom.toAddMonoidHom
    (g₁.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))).hom.toAddMonoidHom
    (hg₂ f d hd hf) (hg₁ f d hd hf)
  let N' : Fin 3 → ModuleCat.{u} (MvPolynomial (Fin 2) k) := ![A 1, A 0, M]
  let H' : ∀ j, ℤ → AddSubgroup (N' j) :=
    Fin.cases (𝒢 1) (Fin.cases (𝒢 0) (Fin.cases 𝓜 (fun i ↦ Fin.elim0 i)))
  let T' : Fin 3 → (Proj (homogeneousSubmodule (Fin 2) k)).Modules := ![E 1, E 0, F]
  let a' : ∀ j, (T' j).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
      LocalizedModule.Away f (N' j) :=
    Fin.cases (alphaE 1 f d hd hf)
      (Fin.cases (alphaE 0 f d hd hf) (Fin.cases (alpha f d hd hf) (fun i ↦ Fin.elim0 i)))
  have hN' : ∀ j, DirectSum.IsInternal (H' j) := by
    exact Fin.cases (h𝒢 1) (Fin.cases (h𝒢 0) (Fin.cases h𝓜 (fun i ↦ Fin.elim0 i)))
  have hNs' : ∀ (j : Fin 3) (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : N' j),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ H' j z → a • y ∈ H' j (n + z) := by
    exact Fin.cases (hA_smul 1) (Fin.cases (hA_smul 0) (Fin.cases hsmul (fun i ↦ Fin.elim0 i)))
  have ha' : ∀ j, Function.Injective (a' j) ∧ Set.range (a' j) = degreeZeroFractions
      (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
      (fun n : ℕ ↦ (H' j n : Set (N' j))) (Submonoid.powers f) := by
    exact Fin.cases (hcharts 1 f d hd hf)
      (Fin.cases (hcharts 0 f d hd hf) (Fin.cases (halpha f d hd hf) (fun i ↦ Fin.elim0 i)))
  obtain ⟨hexR, _, hsurjR⟩ := proj_away_degreeZero_exact_pair k (fun j ↦ N' j) H' hN' hNs' f d hd hf
    (fun j ↦ (T' j).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))) a' ha'
    f₁ f₀ hf₁ hf₀ hex₁'
    (g₁.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))).hom.toAddMonoidHom
    (g₀.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))).hom.toAddMonoidHom
    (hg₁ f d hd hf) (hg₀ f d hd hf)
  exact ⟨hinjL hinj, hexL, hexR, hsurjR hsurj⟩

end AlgebraicGeometry.Proj

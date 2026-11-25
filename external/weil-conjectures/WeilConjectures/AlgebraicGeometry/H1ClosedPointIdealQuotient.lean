/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # The distinguished section of a closed-point ideal quotient

Source: Stacks Project, Tag 01XF, first paragraph of the proof.
(blueprint: lem-pqf-h1-closed-point-ideal-quotient)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The quotient of the two reduced vanishing ideals has a section with residue one.

Source: Stacks Project, Tag 01XF, first paragraph, up to the application of H¹ vanishing.
(blueprint: lem-pqf-h1-closed-point-ideal-quotient)

Proof: Set Z = X \ U and Z' = Z union {x}, and take their reduced vanishing ideals I
and J. Their sections are functions whose residues vanish on the respective closed sets.
The section 1 on U therefore lifts to a section sU of I. Take Q to be the cokernel of
J into I, with quotient section qU on U. On V = X \ {x} the two ideals agree: every
section of I vanishes also on Z', because no point of V is x. Their inclusion restricted
to V is an isomorphism, so Q restricted to V is zero. Glue qU and zero on the cover U,V,
using the zero sections of Q on the overlaps. This gives a global section q of Q.
If s is a global lift of q, then s restricted to U minus sU is killed by the quotient
map. Evaluation on any open preserves kernels, so this difference comes from a section
of J on U. Its residue at x is zero. The image of sU is 1, so the residue of s is 1;
restriction commutes with germs and residues. The argument works for any open U containing
x, without affineness or separation assumptions. For U = X the same gluing applies;
nonreduced schemes use the radical vanishing ideals, and x in U excludes empty cases. -/
theorem exists_closedPoint_ideal_quotient_section (X : Scheme.{u})
    (U : X.Opens) (x : X) (hxU : x ∈ U)
    (hx : IsClosed ({x} : Set X)) :
    let Z : TopologicalSpace.Closeds X := ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
    let Z' : TopologicalSpace.Closeds X := ⟨(U : Set X)ᶜ ∪ {x},
      U.isOpen.isClosed_compl.union hx⟩
    let I := Scheme.IdealSheafData.vanishingIdeal Z
    let J := Scheme.IdealSheafData.vanishingIdeal Z'
    let i : J.toModules ⟶ I.toModules := Scheme.IdealSheafData.toModulesOfLE
      (Scheme.IdealSheafData.vanishingIdeal_antimono
        (show Z ≤ Z' from Set.subset_union_left))
    ∃ (q : Γ(cokernel i, ⊤)), ∀ (s : Γ(I.toModules, ⊤)),
      (cokernel.π i).app ⊤ s = q →
        X.evaluation ⊤ x (by trivial) (I.toModulesι.app ⊤ s) = 1 := by
  classical
  intro Z Z' I J i
  have hI (W : X.Opens) (s : Γ(X, W)) :=
    (Scheme.IdealSheafData.reduced_induced_closed_subscheme X Z).1 W s
  have hJ (W : X.Opens) (s : Γ(X, W)) :=
    (Scheme.IdealSheafData.reduced_induced_closed_subscheme X Z').1 W s
  have hone : (1 : Γ(X, U)) ∈ I.idealOfOpens U := by
    apply (hI U 1).mpr
    intro y hy hz
    exact (hz hy).elim
  obtain ⟨sU, hsU⟩ : ∃ sU : Γ(I.toModules, U), I.toModulesι.app U sU = (1 : Γ(X, U)) := by
    have : (1 : Γ(X, U)) ∈ Set.range (I.toModulesι.app U) := by
      rw [I.range_toModulesι_app_eq_idealOfOpens]
      exact hone
    exact this
  let V : X.Opens := ⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩
  have hiV : IsIso ((Scheme.Modules.restrictFunctor V.ι).map i) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro W
    rw [ConcreteCategory.isIso_iff_bijective]
    let T := V.ι ''ᵁ W
    have hcomp := Scheme.IdealSheafData.toModulesOfLE_toModulesι
      (Scheme.IdealSheafData.vanishingIdeal_antimono
        (show Z ≤ Z' from Set.subset_union_left))
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply J.injective_toModulesι_app T
      have he := congr($(hcomp).app T a)
      have he' := congr($(hcomp).app T b)
      exact he.symm.trans ((congrArg (I.toModulesι.app T) hab).trans he')
    · intro a
      have ha : I.toModulesι.app T a ∈ I.idealOfOpens T := by
        change I.toModulesι.app T a ∈ (I.idealOfOpens T : Set Γ(X, T))
        rw [← I.range_toModulesι_app_eq_idealOfOpens]
        exact ⟨a, rfl⟩
      have hb : I.toModulesι.app T a ∈ J.idealOfOpens T := by
        apply (hJ T _).mpr
        intro y hy hyZ'
        rcases hyZ' with hyZ | hyx
        · exact (hI T _).mp ha y hy hyZ
        · have hyV : y ∈ V := (V.ι.image_le_opensRange W).trans (by simp) hy
          exact (hyV hyx).elim
      obtain ⟨b, hb⟩ : ∃ b : Γ(J.toModules, T),
          J.toModulesι.app T b = I.toModulesι.app T a := by
        have : I.toModulesι.app T a ∈ Set.range (J.toModulesι.app T) := by
          rw [J.range_toModulesι_app_eq_idealOfOpens]
          exact hb
        exact this
      refine ⟨b, ?_⟩
      apply I.injective_toModulesι_app T
      exact congr($(hcomp).app T b) |>.trans hb
  let Q := cokernel i
  have hQV : IsZero (Q.restrict V.ι) :=
    (isZero_cokernel_of_epi ((Scheme.Modules.restrictFunctor V.ι).map i)).of_iso
      (PreservesCokernel.iso (Scheme.Modules.restrictFunctor V.ι) i)
  have hzero (W : X.Opens) (hWV : W ≤ V) : Subsingleton Γ(Q, W) := by
    have hz := (SheafOfModules.evaluation _ (op (V.ι ⁻¹ᵁ W))).map_isZero hQV
    have : Subsingleton Γ(Q.restrict V.ι, V.ι ⁻¹ᵁ W) :=
      ModuleCat.subsingleton_of_isZero hz
    have he := (Q.restrictAppIso V.ι (V.ι ⁻¹ᵁ W)).addCommGroupIsoToAddEquiv
    have : Subsingleton Γ(Q, V.ι ''ᵁ (V.ι ⁻¹ᵁ W)) :=
      he.toEquiv.symm.subsingleton
    have heW : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hWV]
    rwa [heW] at this
  let C : Bool → X.Opens := fun b ↦ if b then U else V
  let a : (b : Bool) → Γ(Q, C b) := fun b ↦ by
    cases b
    · exact 0
    · exact (cokernel.π i).app U sU
  have hcover : (⨆ b, C b) = ⊤ := by
    apply le_antisymm le_top
    intro y _
    by_cases h : y ∈ U
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, h⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, by
        change y ∉ ({x} : Set X)
        simp only [Set.mem_singleton_iff]
        intro he
        exact h (he ▸ hxU)⟩
  have hcompat : TopCat.Presheaf.IsCompatible Q.presheaf C a := by
    intro b c
    cases b <;> cases c
    · rfl
    · have : Subsingleton Γ(Q, C false ⊓ C true) := hzero _ inf_le_left
      exact Subsingleton.elim _ _
    · have : Subsingleton Γ(Q, C true ⊓ C false) := hzero _ inf_le_right
      exact Subsingleton.elim _ _
    · rfl
  obtain ⟨q, hq, _⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨Q.presheaf, Q.isSheaf⟩ C ⊤
    (fun _ ↦ homOfLE le_top) (by rw [hcover]) a hcompat
  refine ⟨q, ?_⟩
  intro s hs
  have hqU : Q.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op q =
      (cokernel.π i).app U sU := hq true
  let s' := I.toModules.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s
  have hπ : (cokernel.π i).app U (s' - sU) = 0 := by
    rw [map_sub]
    have hn := (ConcreteCategory.congr_hom ((cokernel.π i).val.naturality
      (homOfLE (le_top : U ≤ ⊤)).op) s).symm
    change Q.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      ((cokernel.π i).app ⊤ s) = (cokernel.π i).app U s' at hn
    rw [← hn, hs, hqU, sub_self]
  have : Mono i := by
    have hi : i ≫ I.toModulesι = J.toModulesι :=
      Scheme.IdealSheafData.toModulesOfLE_toModulesι _
    have : Mono (i ≫ I.toModulesι) := hi ▸ inferInstance
    exact mono_of_mono i I.toModulesι
  have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let : E.Additive := inferInstanceAs
    ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)).Additive)
  have hex : ((ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).map E).Exact := by
    exact ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp
      inferInstance _ hS).1
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex (s' - sU) hπ
  have ht' : J.toModulesι.app U t = I.toModulesι.app U (s' - sU) := by
    rw [← Scheme.IdealSheafData.toModulesOfLE_toModulesι
      (Scheme.IdealSheafData.vanishingIdeal_antimono
        (show Z ≤ Z' from Set.subset_union_left))]
    change I.toModulesι.app U (i.app U t) = I.toModulesι.app U (s' - sU)
    exact congrArg (I.toModulesι.app U) ht
  have htmem : J.toModulesι.app U t ∈ J.idealOfOpens U := by
    change J.toModulesι.app U t ∈ (J.idealOfOpens U : Set Γ(X, U))
    rw [← J.range_toModulesι_app_eq_idealOfOpens]
    exact ⟨t, rfl⟩
  have htx : X.evaluation U x hxU (J.toModulesι.app U t) = 0 :=
    (hJ U _).mp htmem x hxU (Or.inr (Set.mem_singleton x))
  rw [ht', map_sub, hsU, map_sub, map_one] at htx
  have hres : X.evaluation U x hxU (I.toModulesι.app U s') = 1 := sub_eq_zero.mp htx
  have hn := (ConcreteCategory.congr_hom (I.toModulesι.val.naturality
    (homOfLE (le_top : U ≤ ⊤)).op) s).symm
  change X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (I.toModulesι.app ⊤ s) =
    I.toModulesι.app U s' at hn
  rw [← hn] at hres
  simpa only [Scheme.evaluation, ← ConcreteCategory.comp_apply, ← Category.assoc,
    TopCat.Presheaf.germ_res] using hres

end AlgebraicGeometry

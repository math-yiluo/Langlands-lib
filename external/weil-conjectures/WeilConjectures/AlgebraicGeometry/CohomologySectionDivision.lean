/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.Topology.OpenModuleCohomologyLocalIso

/-! # Dividing restricted twisted cohomology by a nonvanishing section

Source: Stacks Project, Tags 09MR and 01CY, construction of the canonical map.
(blueprint: lem-sc-cohomology-section-division)
-/

@[expose] public section

universe uMV

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

/-- Multiplication by each tensor power of the nonvanishing section is bijective
on cohomology over W intersect S. Its inverse after restriction is compatible with
transition multiplication. This is a statement on individual twists, before either
direct sums or quotient fractions are formed.

Source: Stacks Project, Tag 09MR, canonical map; Tag 01CY, local trivialization.
Proof: The section s trivializes L on S. Its n-th tensor power, tensored with F,
is therefore an isomorphism on S and on every W intersect S. Compute cohomology on
that open using a restricted injective resolution, or equivalently derive the
restriction functor; the functor sends this isomorphism to an isomorphism. This gives
the last bijectivity assertion. Define q by restricting a class to W intersect S
and then applying the inverse cohomology isomorphism. Multiplication followed by
its inverse gives the first formula. To check transition compatibility, multiply
both proposed values by s^(n+b). Naturality of cohomology restriction and the tensor
power identity s^(n+b)=s^n tensor s^b give the same result. Cancel this bijective
multiplication to obtain the second formula. When n=0 this is ordinary restriction;
when s is zero S is empty and all target groups are zero. No quasi-coherence or
compactness hypothesis is used.
(blueprint: lem-sc-cohomology-section-division). -/
theorem exists_cohomologySection_division (X : Scheme.{uMV})
    (L F : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (S : X.Opens) (_hS : (S : Set X) = nonvanishingLocus L s) :
    ∃ q : ∀ (W : X.Opens) (p n : ℕ),
      (openModuleCohomology X.toRingedSpace p W).obj (F ⊗ L.tensorPow n : X.Modules) →+
        (openModuleCohomology X.toRingedSpace p (W ⊓ S)).obj F,
      (∀ (W : X.Opens) (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p W).obj (F ⊗ L.tensorPow n : X.Modules)),
        (openModuleCohomology X.toRingedSpace p (W ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (q W p n ξ) =
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : W ⊓ S ≤ W))).app (F ⊗ L.tensorPow n : X.Modules) ξ) ∧
      (∀ (W : X.Opens) (p n b : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p W).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        q W p (n + b) ((openModuleCohomology X.toRingedSpace p W).map
          (mulTensorPowSection (homOfGlobalSection L s) F n b) ξ) = q W p n ξ) ∧
      (∀ (W : X.Opens) (p n : ℕ), Function.Bijective
        ((openModuleCohomology X.toRingedSpace p (W ⊓ S)).map
          (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
            F ⟶ (F ⊗ L.tensorPow n : X.Modules)))) := by
  classical
  obtain ⟨U, hU, _, hdiv⟩ := nonvanishing_section_trivializes X L s
  have hUS : U = S := SetLike.coe_injective (hU.trans _hS.symm)
  subst U
  have hgen : IsFreeGenerator
      ((homOfGlobalSection L s).app S (unitSectionsEquiv S 1)) := by
    rw [show (homOfGlobalSection L s).app S (unitSectionsEquiv S 1) =
      L.presheaf.map (homOfLE (le_top : S ≤ ⊤)).op s from
      homOfGlobalSection_app_one L s S]
    intro V hV
    rw [presheaf_map_map_apply]
    rw [show homOfLE hV ≫ homOfLE (le_top : S ≤ ⊤) =
      homOfLE (le_top : V ≤ ⊤) from Subsingleton.elim _ _]
    constructor
    · intro a b hab
      obtain ⟨c, _, hc⟩ := hdiv V hV
        (a • L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s)
      exact (hc a rfl).trans (hc b hab).symm
    · intro t
      obtain ⟨a, ha, _⟩ := hdiv V hV t
      exact ⟨a, ha.symm⟩
  let m (n : ℕ) : F ⟶ (F ⊗ L.tensorPow n : X.Modules) :=
    (ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n
  have hlocal (W : X.Opens) (n : ℕ) :
      IsIso ((SheafOfModules.overFunctor X.ringCatSheaf (W ⊓ S)).map (m n)) := by
    let G := SheafOfModules.forget (X.ringCatSheaf.over (W ⊓ S)) ⋙
      PresheafOfModules.toPresheaf (X.ringCatSheaf.over (W ⊓ S)).obj
    rw [← isIso_iff_of_reflects_iso _ G]
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective ((m n).app V.unop.left)
    have he := isFreeGenerator_tensorPowSectionOne (homOfGlobalSection L s) hgen n
    have hb := he.bijective_tmulSection_right (M := F)
      ((leOfHom V.unop.hom).trans inf_le_right)
    rw [presheaf_map_tensorPowSectionOne] at hb
    change Function.Bijective fun x => (m n).app V.unop.left x
    simpa only [m, rightUnitor_inv_comp_whiskerLeft_app] using hb
  have hbij (W : X.Opens) (p n : ℕ) :
      Function.Bijective ((openModuleCohomology X.toRingedSpace p (W ⊓ S)).map (m n)) := by
    have := hlocal W n
    have := openModuleCohomology_map_isIso_of_overFunctor X.toRingedSpace (W ⊓ S) (m n) p
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  let e (W : X.Opens) (p n : ℕ) :=
    AddEquiv.ofBijective
      ((openModuleCohomology X.toRingedSpace p (W ⊓ S)).map (m n)).hom (hbij W p n)
  let q (W : X.Opens) (p n : ℕ) := (e W p n).symm.toAddMonoidHom.comp
    ((openModuleCohomologyRestriction X.toRingedSpace p
      (homOfLE (inf_le_left : W ⊓ S ≤ W))).app (F ⊗ L.tensorPow n : X.Modules)).hom
  have hq (W : X.Opens) (p n : ℕ) (ξ) :
      (openModuleCohomology X.toRingedSpace p (W ⊓ S)).map (m n) (q W p n ξ) =
        (openModuleCohomologyRestriction X.toRingedSpace p
          (homOfLE (inf_le_left : W ⊓ S ≤ W))).app (F ⊗ L.tensorPow n : X.Modules) ξ := by
    exact (e W p n).apply_symm_apply _
  refine ⟨q, hq, ?_, hbij⟩
  intro W p n b ξ
  apply (hbij W p (n + b)).1
  rw [hq]
  have hm : m n ≫ mulTensorPowSection (homOfGlobalSection L s) F n b = m (n + b) := by
    ext V x
    change (mulTensorPowSection (homOfGlobalSection L s) F n b).app V
      ((m n).app V x) = (m (n + b)).app V x
    dsimp only [m]
    rw [rightUnitor_inv_comp_whiskerLeft_app, rightUnitor_inv_comp_whiskerLeft_app,
      mulTensorPowSection_app_tmulSection]
  have hn := (openModuleCohomologyRestriction X.toRingedSpace p
    (homOfLE (inf_le_left : W ⊓ S ≤ W))).naturality
      (mulTensorPowSection (homOfGlobalSection L s) F n b)
  have hn' := congrArg (fun f => f ξ) hn
  simp only [ConcreteCategory.comp_apply] at hn'
  rw [hn']
  rw [← hm, Functor.map_comp, ConcreteCategory.comp_apply, hq]

end AlgebraicGeometry

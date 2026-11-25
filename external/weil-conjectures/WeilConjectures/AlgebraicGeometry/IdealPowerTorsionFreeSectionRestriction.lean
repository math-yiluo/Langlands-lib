/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import all WeilConjectures.AlgebraicGeometry.CoherentSupportVanishingIdealNilpotence
import all WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Restriction of ideal-power-torsion-free sections

Source: Stacks Project, Properties, Tag 01PM, localization and injectivity argument.
(blueprint: lem-pc-ideal-power-torsion-free-section-restriction)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

noncomputable local instance {X : Scheme.{u}} (F : X.Modules) {V W : X.Opens} (h : V ≤ W) :
    HSMul ((SheafOfModules.unit X.ringCatSheaf).val.obj (op V))
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (homOfLE h).op).hom).obj
        (F.val.obj (op V))) (F.val.obj (op V)) where
  hSMul := @SMul.smul Γ(X, V) Γ(F, V) inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem basicOpen_le_surjective_stalk {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    (V : X.Opens) (f : Γ(X, V))
    (hf : f ∈ LinearMap.range (ι.val.app (op V)).hom)
    (U : X.Opens) (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom) :
    X.basicOpen f ≤ U := by
  intro x hx
  have hxV : x ∈ V := X.basicOpen_le f hx
  obtain ⟨s, hs⟩ := hf
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  obtain ⟨e, he, _⟩ := ideal_module_product_stalk ι
    (SheafOfModules.unit X.ringCatSheaf) x
  let t : S.obj I := TopCat.Presheaf.germ I.val.presheaf V x hxV s
  have ht : e.hom ((S.map ι).hom t) = X.presheaf.germ V x hxV f := by
    dsimp [t, S]
    change e.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf _).map ι.val)
        (TopCat.Presheaf.germ I.val.presheaf V x hxV s)) = _
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact (he V hxV _).trans (congrArg (fun a ↦ X.presheaf.germ V x hxV a) hs)
  have hu : IsUnit (X.presheaf.germ V x hxV f) := (X.mem_basicOpen f x hxV).mp hx
  apply (hU x).mpr
  intro y
  have hy : e.hom y = (e.hom y * ↑hu.unit⁻¹) * X.presheaf.germ V x hxV f := by
    calc
      _ = e.hom y * (↑hu.unit⁻¹ * ↑hu.unit) := by simp
      _ = _ := by simp only [hu.unit_spec, mul_assoc]
  refine ⟨(e.hom y * ↑hu.unit⁻¹) • t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  rw [map_smul, map_smul]
  change (e.hom y * ↑hu.unit⁻¹) * e.hom ((S.map ι).hom t) = e.hom y
  rw [ht]
  exact hy.symm

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the ideal complement is injective for an ideal-power-torsion-free module.

Source: Stacks Project, Properties, Tag 01PM, localization and injectivity argument.
(blueprint: lem-pc-ideal-power-torsion-free-section-restriction)

Proof: Subtract two sections with equal restriction to W intersect U. Cover W by
all its affine subopens A. Let z be the restricted difference on A and J the
finite ideal which is the section image of I. Every f in J has D(f) inside U:
its germ lies in the ideal stalk and is invertible, so that stalk inclusion is
surjective. Thus z vanishes on D(f); affine module localization gives a power
of f killing z. Let L be the kernel of the linear map a ↦ a • z. Then J is
contained in the radical of L. Finite generation of J gives d with J^d contained
in L. The proved affine-power section formula identifies the image of the
recursive power inclusion with J^d, so every power section on A kills z.
For a section b of the power on D(g), clear a denominator to write g^k b as
the restriction of a section on A. Naturality of the inclusion and scalar action
shows g^k kills the product of the image of b with z restricted to D(g).
Since g is invertible on D(g), that product is zero. Cover every subopen V of A
by such D(g) and use sheaf separation to get the local annihilation condition
required by htf. It gives z=0 on A. Separation on the affine cover of W gives
the original difference zero. If J=0 its first power is contained in L; if J is
the unit ideal restriction is the identity. Empty opens and the zero scheme are
handled by the same sheaf separation arguments on empty covers. No compactness
is needed: each affine open has its own exponent d. -/
theorem ideal_power_torsionFree_section_restriction
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens)
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (htf : ∀ (n : ℕ) (W : X.Opens) (x : F.val.obj (op W)),
      (∀ (V : X.Opens) (h : V ≤ W)
        (b : (idealSheafPower ι n).1.val.obj (op V)),
        ((idealSheafPower ι n).2.val.app (op V) b : Γ(X, V)) •
          F.val.map (homOfLE h).op x = 0) → x = 0)
    (W : X.Opens) :
    Function.Injective (F.presheaf.map
      (homOfLE (inf_le_left : W ⊓ U ≤ W)).op)  := by
  intro x y hxy
  have hz : F.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  suffices x - y = 0 from sub_eq_zero.mp this
  let z := x - y
  have hlocal (A : X.affineOpens) (hAW : A.1 ≤ W) :
      F.presheaf.map (homOfLE hAW).op z = 0 := by
    let zA := F.presheaf.map (homOfLE hAW).op z
    let J : Ideal Γ(X, A.1) := LinearMap.range (ι.val.app (op A.1)).hom
    let L : Ideal Γ(X, A.1) :=
      LinearMap.ker (LinearMap.toSpanSingleton Γ(X, A.1) Γ(F, A.1) zA)
    have : Module.Finite Γ(X, A.1) Γ(I, A.1) :=
      Modules.finite_sections_of_finiteType I A.2
    let i : Γ(I, A.1) →ₗ[Γ(X, A.1)] Γ(X, A.1) := (ι.val.app (op A.1)).hom
    have hfg : J.FG := Submodule.fg_range i
    have hrad : J ≤ L.radical := by
      intro f hf
      have hBU : X.basicOpen f ≤ U := basicOpen_le_surjective_stalk ι A.1 f hf U hU
      have hBA := X.basicOpen_le f
      have hBW : X.basicOpen f ≤ W := hBA.trans hAW
      have hb : F.presheaf.map (homOfLE hBA).op zA = 0 := by
        have hi : (homOfLE hAW).op ≫ (homOfLE hBA).op =
            (homOfLE (inf_le_left : W ⊓ U ≤ W)).op ≫
              (homOfLE (le_inf hBW hBU)).op := Subsingleton.elim _ _
        dsimp [zA]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hi, Functor.map_comp]
        change F.presheaf.map (homOfLE (le_inf hBW hBU)).op
          (F.presheaf.map (homOfLE inf_le_left).op (x - y)) = 0
        rw [hz, map_zero]
      obtain ⟨k, hk⟩ := Modules.exists_pow_smul_eq_zero_of_isAffineOpen F A.2 f zA hb
      exact ⟨k, hk⟩
    obtain ⟨d, hd⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg
    have hp := Modules.powers_affine_sections ι d
    have : (idealSheafPower ι d).1.IsQuasicoherent := hp.1
    have hkill (b : Γ((idealSheafPower ι d).1, A.1)) :
        (show Γ(X, A.1) from (idealSheafPower ι d).2.app A.1 b) • zA = 0 := by
      let q : Γ((idealSheafPower ι d).1, A.1) →ₗ[Γ(X, A.1)] Γ(X, A.1) :=
        ((idealSheafPower ι d).2.val.app (op A.1)).hom
      have hq : q.range = J ^ d := hp.2 A
      exact hd (hq ▸ LinearMap.mem_range_self q b)
    have hbasic (g : Γ(X, A.1)) (b : Γ((idealSheafPower ι d).1, X.basicOpen g)) :
        (show Γ(X, X.basicOpen g) from (idealSheafPower ι d).2.app (X.basicOpen g) b) •
          F.presheaf.map (homOfLE (X.basicOpen_le g)).op zA = 0 := by
      obtain ⟨k, t, ht⟩ := Modules.exists_map_eq_pow_smul_of_isAffineOpen
        (idealSheafPower ι d).1 A.2 g b
      let j : X.basicOpen g ⟶ A.1 := homOfLE (X.basicOpen_le g)
      let g' : Γ(X, X.basicOpen g) := X.presheaf.map j.op g
      have he := congrArg (fun c ↦
        ((show Γ(X, X.basicOpen g) from (idealSheafPower ι d).2.app (X.basicOpen g) c) •
          F.presheaf.map j.op zA)) ht
      have he' : g' ^ k •
          ((show Γ(X, X.basicOpen g) from (idealSheafPower ι d).2.app (X.basicOpen g) b) •
            F.presheaf.map j.op zA) = 0 := by
        have hnat := PresheafOfModules.naturality_apply
          (idealSheafPower ι d).2.val j.op t
        erw [hnat, Modules.Hom.app_smul] at he
        change X.presheaf.map j.op ((idealSheafPower ι d).2.app A.1 t) •
            F.presheaf.map j.op zA =
          (g' ^ k * (show Γ(X, X.basicOpen g) from
            (idealSheafPower ι d).2.app (X.basicOpen g) b)) • F.presheaf.map j.op zA at he
        rw [← F.map_smul, hkill, map_zero, mul_smul] at he
        exact he.symm
      have hu : IsUnit g' := X.toRingedSpace.isUnit_res_basicOpen g
      exact (hu.pow k).smul_left_cancel.mp (he'.trans (smul_zero _).symm)
    apply htf d A.1 zA
    intro V hVA b
    let T := {g : Γ(X, A.1) // X.basicOpen g ≤ V}
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, F.isSheaf⟩
      (fun i : T ↦ X.basicOpen i.1) V (fun i ↦ homOfLE i.2)
    · intro q hq
      obtain ⟨g, hg, hqg⟩ := A.2.exists_basicOpen_le ⟨q, hq⟩ (hVA hq)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hqg⟩
    · intro i
      rw [map_zero, F.map_smul]
      have hnat := PresheafOfModules.naturality_apply
        (idealSheafPower ι d).2.val (homOfLE i.2).op b
      erw [← hnat]
      have hi : (homOfLE hVA).op ≫ (homOfLE i.2).op =
          (homOfLE (X.basicOpen_le i.1)).op := Subsingleton.elim _ _
      erw [← F.val.map_comp_apply, hi]
      exact hbasic i.1 _
  let A := {A : X.affineOpens // A.1 ≤ W}
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, F.isSheaf⟩
    (fun A : A ↦ A.1.1) W (fun A ↦ homOfLE A.2)
  · intro q hq
    obtain ⟨V, hV, hqV, hVW⟩ := exists_isAffineOpen_mem_and_subset hq
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hqV⟩
  · intro A
    rw [map_zero]
    exact hlocal A.1 A.2

end AlgebraicGeometry.Scheme

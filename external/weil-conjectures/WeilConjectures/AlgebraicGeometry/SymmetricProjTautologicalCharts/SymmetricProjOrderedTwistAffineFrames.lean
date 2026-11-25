/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.FreeProjectiveBundleBaseChangeSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Ordered quotient frames over one affine base open

Source: Stacks Project, Constructions, Tags 01OE, 01OB, 01MS and 01NR.
(blueprint: lem-trf-symmetric-proj-ordered-twist-affine-frames).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

open Scheme.Modules HomogeneousLocalization

private theorem tensor_unit_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    ((tensorPullbackSectionAdjunction f).unit.app M).app U s =
      tensorPullbackSection f M U s :=
  (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction f)).1 M U s

private theorem tensor_section_map {X Y : Scheme.{u}} (j : X ⟶ Y)
    (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    Scheme.Modules.tensorPullbackSection j M V (M.presheaf.map (homOfLE h).op s) =
      ((Scheme.Modules.tensorPullback j).obj M).presheaf.map
        (homOfLE (j.preimage_mono h)).op
        (Scheme.Modules.tensorPullbackSection j M U s) := by
  let adj := Scheme.Modules.tensorPullbackSectionAdjunction j
  have hn (W : Y.Opens) (t : Γ(M, W)) :
      (adj.unit.app M).app W t = Scheme.Modules.tensorPullbackSection j M W t :=
    (Classical.choose_spec (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction j)).1
      M W t
  rw [← hn, ← hn]
  exact Scheme.Modules.Hom.app_presheaf_map (adj.unit.app M) (homOfLE h) s

private theorem quotient_basis_restrict (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (V : S.affineOpens) (i : ULift.{u} (Fin (r + 1))) :
    let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
    let σ := (Scheme.Modules.tensorPullbackSectionAdjunction p).homEquiv E D.line D.quotient
    σ.app V.1 (b.hom.app V.1 ((SheafOfModules.ιFree
        (R := S.ringCatSheaf) i).val.app (op V.1) (1 : Γ(S, V.1)))) =
      D.line.presheaf.map (homOfLE (p.preimage_mono (le_top : V.1 ≤ ⊤))).op
        (σ.app ⊤ (b.hom.app ⊤ ((SheafOfModules.ιFree
          (R := S.ringCatSheaf) i).val.app (op ⊤) (1 : Γ(S, ⊤))))) := by
  let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
  let σ := (Scheme.Modules.tensorPullbackSectionAdjunction p).homEquiv E D.line D.quotient
  let t := SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom ≫ σ
  have h := PresheafOfModules.naturality_apply t.val
    (homOfLE (le_top : V.1 ≤ ⊤)).op (1 : Γ(S, ⊤))
  have h1 : (SheafOfModules.unit S.ringCatSheaf).val.map
      (homOfLE (le_top : V.1 ≤ ⊤)).op (1 : Γ(S, ⊤)) = (1 : Γ(S, V.1)) :=
    (S.ringCatSheaf.obj.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom.map_one
  rw [h1] at h
  exact h

private theorem tensor_section_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (r : Γ(Y, U)) (s : Γ(M, U)) :
    tensorPullbackSection f M U (r • s) =
      f.app U r • tensorPullbackSection f M U s := by
  rw [← tensor_unit_section, ← tensor_unit_section]
  exact Hom.app_smul ((tensorPullbackSectionAdjunction f).unit.app M) r s

private noncomputable def sectionComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorPullback f ≅ pullback f :=
  (tensorPullbackSectionAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)

private theorem sectionComparison_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    ((sectionComparison f).hom.app M).app (f ⁻¹ᵁ U)
      (tensorPullbackSection f M U s) = pullbackSection f s := by
  have H := congrArg (fun t ↦ t.app U s)
    ((tensorPullbackSectionAdjunction f).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction f) M)
  change ((sectionComparison f).hom.app M).app (f ⁻¹ᵁ U)
    (((tensorPullbackSectionAdjunction f).unit.app M).app U s) = _ at H
  rw [tensor_unit_section] at H
  exact H

private theorem tensor_section_injective {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (U : Y.Opens) (hU : U ≤ j.opensRange) :
    Function.Injective (tensorPullbackSection j M U) := by
  intro s t h
  apply (bijective_pullbackUnit_app_of_isOpenImmersion j M hU).injective
  have H := congrArg (((sectionComparison j).hom.app M).app (j ⁻¹ᵁ U)) h
  rw [sectionComparison_section, sectionComparison_section] at H
  exact H

private theorem tensor_section_free_descent {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (U : Y.Opens) (hU : U ≤ j.opensRange)
    (s : Γ(M, U)) (hs : IsFreeGenerator (tensorPullbackSection j M U s)) :
    IsFreeGenerator s := by
  intro V hV
  have hVr := hV.trans hU
  have := j.isIso_app V hVr
  have hr := ConcreteCategory.bijective_of_isIso (j.app V)
  have hm : Function.Bijective (tensorPullbackSection j M V) := by
    have hb : Function.Bijective (fun x : Γ(M, V) ↦ pullbackSection j x) :=
      bijective_pullbackUnit_app_of_isOpenImmersion j M hVr
    have hc := ConcreteCategory.bijective_of_isIso
      (((sectionComparison j).hom.app M).app (j ⁻¹ᵁ V))
    have heq : (fun x ↦ pullbackSection j (M := M) (U := V) x) =
        (((sectionComparison j).hom.app M).app (j ⁻¹ᵁ V)) ∘
          tensorPullbackSection j M V := funext (fun x ↦ (sectionComparison_section j M V x).symm)
    rw [heq] at hb
    exact (Function.Bijective.of_comp_iff' hc _).mp hb
  have H (r : Γ(Y, V)) :
      tensorPullbackSection j M V (r • M.presheaf.map (homOfLE hV).op s) =
        j.app V r • ((tensorPullback j).obj M).presheaf.map
          (homOfLE (j.preimage_mono hV)).op (tensorPullbackSection j M U s) := by
    rw [tensor_section_smul]
    congr 1
    exact tensor_section_map j M hV s
  constructor
  · intro r t h
    apply hr.injective
    apply (hs (j ⁻¹ᵁ V) (j.preimage_mono hV)).injective
    exact (H r).symm.trans ((congrArg (tensorPullbackSection j M V) h).trans (H t))
  · intro x
    obtain ⟨r, he⟩ := (hs (j ⁻¹ᵁ V) (j.preimage_mono hV)).surjective
      (tensorPullbackSection j M V x)
    obtain ⟨t, rfl⟩ := hr.surjective r
    exact ⟨t, hm.injective ((H t).trans he)⟩

private theorem free_of_chart_section {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (N : X.Modules)
    (e : (tensorPullback j).obj M ≅ N) (W : Y.Opens) (hW : W ≤ j.opensRange)
    (s : Γ(M, W)) (t : Γ(N, j ⁻¹ᵁ W))
    (hn : e.hom.app (j ⁻¹ᵁ W) (tensorPullbackSection j M W s) = t)
    (ht : IsFreeGenerator t) : IsFreeGenerator s := by
  apply tensor_section_free_descent j M W hW
  have H := ht.app_hom e.symm
  rw [← hn] at H
  simpa only [Iso.symm_hom, ← ConcreteCategory.comp_apply, ← Hom.comp_app,
    Iso.hom_inv_id, Hom.id_app, ConcreteCategory.id_apply] using H

private theorem relation_of_chart_sections {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (N : X.Modules)
    (e : (tensorPullback j).obj M ≅ N) (W : Y.Opens) (hW : W ≤ j.opensRange)
    (s t : Γ(M, W)) (a b : Γ(N, j ⁻¹ᵁ W))
    (hs : e.hom.app (j ⁻¹ᵁ W) (tensorPullbackSection j M W s) = a)
    (ht : e.hom.app (j ⁻¹ᵁ W) (tensorPullbackSection j M W t) = b)
    (c : Γ(Y, W)) (h : a = j.app W c • b) : s = c • t := by
  apply tensor_section_injective j M W hW
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app (j ⁻¹ᵁ W))).injective
  rw [tensor_section_smul, Hom.app_smul, hs, ht]
  exact h

attribute [local instance] MvPolynomial.gradedAlgebra
private noncomputable def coefficientMap {I R T : Type u} [CommRing R] [CommRing T]
    (a : R →+* T) : MvPolynomial.homogeneousSubmodule I R →+*ᵍ
      MvPolynomial.homogeneousSubmodule I T :=
  { MvPolynomial.map a with map_mem := fun h ↦ h.map a }
private theorem coefficientMap_irrelevant {I R T : Type u} [CommRing R] [CommRing T]
    (a : R →+* T) :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule I T) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule I R)).map
        (coefficientMap a) := by
  apply toIdeal_le_toIdeal_iff.mp
  rw [MvPolynomial.toIdeal_irrelevant_homogeneousSubmodule, HomogeneousIdeal.toIdeal_map]
  rw [MvPolynomial.toIdeal_irrelevant_homogeneousSubmodule, Ideal.map_span]
  apply Ideal.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨MvPolynomial.X i, ⟨i, rfl⟩, ?_⟩
  exact MvPolynomial.map_X a i

private theorem gamma_integral (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens)
    (γ : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
      (RelativeProjectiveSpace.algebra S r).sectionGrade V)
    (hγ : ∀ x, γ x = RelativeProjectiveSpace.affinePolynomialEquiv S r V
      (MvPolynomial.rename (fun i : ULift.{u} (Fin (r + 1)) ↦ i.down) x)) :
    (γ.comp (coefficientMap ((Int.castRingHom Γ(S, V.1)).comp
      (ULift.ringEquiv (R := ℤ)).toRingHom))).toRingHom =
        RelativeProjectiveSpace.integralPolynomialMap S r V := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change γ (MvPolynomial.map _ (MvPolynomial.C a)) = _
    simp only [MvPolynomial.map_C, hγ, MvPolynomial.rename_C,
      RelativeProjectiveSpace.integralPolynomialMap, RingHom.comp_apply,
      MvPolynomial.eval₂Hom_C, RingEquiv.toRingHom_eq_coe]
    rfl
  · intro i
    change γ (MvPolynomial.map _ (MvPolynomial.X i)) = _
    simp only [MvPolynomial.map_X, hγ, MvPolynomial.rename_X,
      RelativeProjectiveSpace.integralPolynomialMap, RingHom.comp_apply,
      MvPolynomial.eval₂Hom_X']
    rfl

private theorem affine_integral_map (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r)
    (θ : RelativeProjectiveSpace.scheme S r ≅ ℙ(ULift.{u} (Fin (r + 1)); S))
    (V : S.affineOpens)
    (hAffine : ProjectiveBundleQuotientGeometry.AffineFreeComparison r b eRel V)
    (hθAffine : RelativeProjectiveSpace.IsIntegralProjComparison S r V
      (RelativeProjectiveSpace.affineToIntegral S r θ V)) :
    ∃ ψ : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ)
        →+*ᵍ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V,
      (∀ i, ψ (MvPolynomial.X i) = SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))
        (b.hom.app V.1 ((SheafOfModules.ιFree
          (R := S.ringCatSheaf) i).val.app (op V.1) (1 : Γ(S, V.1))))) ∧
      ∃ hψ : HomogeneousIdeal.irrelevant
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) ≤
        (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule
          (ULift.{u} (Fin (r + 1))) (ULift.{u} ℤ))).map ψ,
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V ≫ (eRel ≪≫ θ).hom ≫
          ProjectiveSpace.toProjInt (ULift.{u} (Fin (r + 1))) S = Proj.map ψ hψ := by
  obtain ⟨β, hb, hC, hX, hβ, eC, heC, htwist, γ, hγ, eR, hγformula, heR, hchart⟩ := hAffine
  obtain ⟨ψR, hψRing, hψR, hmap⟩ := hθAffine
  let α := coefficientMap (I := ULift.{u} (Fin (r + 1))) ((Int.castRingHom Γ(S, V.1)).comp
    (ULift.ringEquiv (R := ℤ)).toRingHom)
  have hα := coefficientMap_irrelevant (I := ULift.{u} (Fin (r + 1)))
    ((Int.castRingHom Γ(S, V.1)).comp (ULift.ringEquiv (R := ℤ)).toRingHom)
  have heq : ψR = γ.comp α := by
    apply GradedRingHom.ext
    intro x
    exact congrArg (fun a ↦ a x) (hψRing.trans (gamma_integral S r V γ hγformula).symm)
  refine ⟨β.comp α, ?_, HomogeneousIdeal.irrelevant_le_map_comp hα hβ, ?_⟩
  · intro i
    change β (MvPolynomial.map _ (MvPolynomial.X i)) = _
    rw [MvPolynomial.map_X, hX]
  · calc
      _ = eC.hom ≫ eR.inv ≫ RelativeProjectiveSpace.affineToIntegral S r θ V := by
        simp only [Iso.trans_hom, ← Category.assoc]
        rw [hchart]
        simp only [RelativeProjectiveSpace.affineToIntegral, Category.assoc]
      _ = eC.hom ≫ eR.inv ≫ Proj.map ψR hψR := by rw [hmap]
      _ = Proj.map (β.comp α) (HomogeneousIdeal.irrelevant_le_map_comp hα hβ) := by
        subst ψR
        rw [Proj.map_comp α γ hα hγ, ← heR, eR.inv_hom_id_assoc,
          heC, ← Proj.map_comp]

private theorem appLE_hom_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V e' := by
  subst g
  rfl
private theorem proj_polynomial_ratio (n : Type u) (S : Scheme.{u})
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜]
    (ψ : MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ) →+*ᵍ 𝒜)
    (hψ : HomogeneousIdeal.irrelevant 𝒜 ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))).map ψ)
    (k : Proj 𝒜 ⟶ ℙ(n; S))
    (hk : k ≫ ProjectiveSpace.toProjInt n S = Proj.map ψ hψ) (i j : n)
    (hB : Proj.basicOpen 𝒜 (ψ (MvPolynomial.X i)) ≤
      k ⁻¹ᵁ ProjectiveSpace.standardOpen n S i) :
    k.appLE (ProjectiveSpace.standardOpen n S i)
        (Proj.basicOpen 𝒜 (ψ (MvPolynomial.X i))) hB
        (ProjectiveSpace.coordRatio n S i j) =
      Proj.awayToSection 𝒜 (ψ (MvPolynomial.X i))
        (Away.map ψ (MvPolynomial.X i) (MvPolynomial.awayXRatio (ULift.{u} ℤ) i j)) := by
  let U := Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
    (MvPolynomial.X i)
  let V := Proj.basicOpen 𝒜 (ψ (MvPolynomial.X i))
  let a := Proj.awayToSection (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
    (MvPolynomial.X i) (MvPolynomial.awayXRatio (ULift.{u} ℤ) i j)
  have hc : (k ≫ ProjectiveSpace.toProjInt n S).appLE U V hB =
      (Proj.map ψ hψ).appLE U V (by rfl) := appLE_hom_congr hk U V hB (by rfl)
  have h := congrArg (fun φ ↦ (ConcreteCategory.hom φ)
      (MvPolynomial.awayXRatio (ULift.{u} ℤ) i j))
    (Proj.awayToSection_comp_appLE ψ hψ
      (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i))
  change (Proj.map ψ hψ).appLE U V (by rfl) a = _ at h
  calc
    _ = (k ≫ ProjectiveSpace.toProjInt n S).appLE U V hB a := by
      rw [Scheme.Hom.comp_appLE]
      rfl
    _ = (Proj.map ψ hψ).appLE U V (by rfl) a := congrArg (fun φ ↦ φ a) hc
    _ = _ := h

/-- The canonical inclusion, bundled with its degree-one membership proof. -/
private noncomputable def symmetricGenerator {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (V : S.affineOpens) (m : Γ(E, V.1)) :
    (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V 1 :=
  ⟨SymmetricAlgebra.ι Γ(S, V.1) Γ(E, V.1) m, by
    change SymmetricAlgebra.ι Γ(S, V.1) Γ(E, V.1) m ∈
      (SymmetricAlgebra.ι Γ(S, V.1) Γ(E, V.1)).range ^ (1 : ℕ)
    rw [pow_one]
    exact ⟨m, rfl⟩⟩

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι Proj.twist

attribute [local irreducible] SymmetricAlgebraSheaf.gradedAlgebraData

private theorem unit_section_res {X : Scheme.{u}} {M : X.Modules}
    (φ : unit X ⟶ M) {U V : X.Opens} (h : V ≤ U) :
    M.presheaf.map (homOfLE h).op (φ.app U (unitSectionsEquiv U 1)) =
      φ.app V (unitSectionsEquiv V 1) := by
  rw [← Hom.app_presheaf_map]
  apply congrArg (φ.app V)
  exact (presheaf_map_unitSectionsEquiv (homOfLE h) 1).trans
    (congrArg (unitSectionsEquiv V) (_root_.map_one (X.presheaf.map (homOfLE h).op).hom))

private theorem unit_section_relation {X : Scheme.{u}} {M : X.Modules}
    (φ ψ : unit X ⟶ M) {U V W : X.Opens} (h : V ≤ U) (hW : W ≤ V)
    (r : Γ(X, V))
    (H : M.presheaf.map (homOfLE h).op (φ.app U (unitSectionsEquiv U 1)) =
      r • M.presheaf.map (homOfLE h).op (ψ.app U (unitSectionsEquiv U 1))) :
    φ.app W (unitSectionsEquiv W 1) =
      X.presheaf.map (homOfLE hW).op r • ψ.app W (unitSectionsEquiv W 1) := by
  have H' := presheaf_map_homOfLE_eq_smul h hW H
  rw [unit_section_res, unit_section_res] at H'
  exact H'

private theorem quotient_chart_section (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (V : S.affineOpens) (m : Γ(E, V.1))
    (W : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Opens)
    (hW : W ≤ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ V.1) :
    (D.chart V).hom.app ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V ⁻¹ᵁ W)
      (tensorPullbackSection ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V)
        D.line W (D.line.presheaf.map (homOfLE hW).op
          (((tensorPullbackSectionAdjunction
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).homEquiv E D.line
              D.quotient).app V.1 m))) =
      (Proj.unitToTwist (symmetricGenerator E V m).property).app
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V ⁻¹ᵁ W)
        (1 : Γ(Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V),
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V ⁻¹ᵁ W)) := by
  rw [tensor_section_map, Hom.app_presheaf_map]
  erw [D.generator V m (symmetricGenerator E V m).property]
  exact unit_section_res (Proj.unitToTwist (symmetricGenerator E V m).property) _

/-- On one affine base open the ordered quotient sections have the standard free
frames and homogeneous coordinate ratios. This is a local calculation and does
not assert a global comparison of line modules.

Source: Stacks Project, Constructions, Tags 01OE, 01OB, 01MS and 01NR.
(blueprint: lem-trf-symmetric-proj-ordered-twist-affine-frames).

Proof: unpack the affine comparison into beta, eC, gamma and eR. Compose the chart equation for
eRel with theta and its integral projection. The normalization of gamma and the integral
comparison imply that this composite is eC followed by extension of coefficients from the
integral polynomial ring: both graded maps fix every ordered variable and map integers by the
structure map, hence are equal by polynomial extensionality. The inverse image of D_+(X_i) is
consequently D_+(beta(X_i)). On it beta(X_i) is a free frame of the degree-one symmetric twist.
The generator equation for D, applied to b(e_i), identifies the pullback of the displayed global
section with that frame. Naturality of the adjoint quotient identifies restriction of the global
section with the quotient of the local basis section. Transport freeness across D.chart and the
affine open immersion. The degree-one fraction identity on D_+(beta(X_i)) is
beta(X_j)=(beta(X_j)/beta(X_i))*beta(X_i). The Proj map sends X_j/X_i to this same ratio.
Transport this identity through D.chart and the open-immersion restriction comparison to obtain
the second assertion. No intersections of distinct affine base opens and no global gluing are
involved. For r=0 the sole ratio is 1. Empty opens and the zero coefficient ring satisfy the
same identities of zero localizations.
-/
theorem ordered_quotient_affine_frames (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r)
    (θ : RelativeProjectiveSpace.scheme S r ≅ ℙ(ULift.{u} (Fin (r + 1)); S))
    (V : S.affineOpens)
    (hAffine : ProjectiveBundleQuotientGeometry.AffineFreeComparison r b eRel V)
    (hθAffine : RelativeProjectiveSpace.IsIntegralProjComparison S r V
      (RelativeProjectiveSpace.affineToIntegral S r θ V)) :
    let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
    let f := (eRel ≪≫ θ).hom
    let σ := (Scheme.Modules.tensorPullbackSectionAdjunction p).homEquiv E D.line D.quotient
    let s (i : ULift.{u} (Fin (r + 1))) : Γ(D.line, ⊤) :=
      σ.app ⊤ (b.hom.app ⊤ ((SheafOfModules.ιFree
        (R := S.ringCatSheaf) i).val.app (op ⊤) (1 : Γ(S, ⊤))))
    ∀ i : ULift.{u} (Fin (r + 1)),
      let W := p ⁻¹ᵁ V.1 ⊓ f ⁻¹ᵁ ProjectiveSpace.standardOpen _ S i
      Scheme.Modules.IsFreeGenerator
        (D.line.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i)) ∧
      ∀ j : ULift.{u} (Fin (r + 1)),
        D.line.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s j) =
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.presheaf.map
            (homOfLE (inf_le_right : W ≤ f ⁻¹ᵁ ProjectiveSpace.standardOpen _ S i)).op
              (f.app (ProjectiveSpace.standardOpen _ S i)
                (ProjectiveSpace.coordRatio _ S i j))) •
            D.line.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i) := by
  classical
  dsimp only
  let A := SymmetricAlgebraSheaf.gradedAlgebraData E
  let p := A.relProjHom
  let f := (eRel ≪≫ θ).hom
  let j := A.relProjι V
  let σ := (tensorPullbackSectionAdjunction p).homEquiv E D.line D.quotient
  let q (i : ULift.{u} (Fin (r + 1))) : Γ(D.line, ⊤) :=
    σ.app ⊤ (b.hom.app ⊤ ((SheafOfModules.ιFree
      (R := S.ringCatSheaf) i).val.app (op ⊤) (1 : Γ(S, ⊤))))
  let m (i : ULift.{u} (Fin (r + 1))) : Γ(E, V.1) :=
    b.hom.app V.1 ((SheafOfModules.ιFree
      (R := S.ringCatSheaf) i).val.app (op V.1) (1 : Γ(S, V.1)))
  obtain ⟨ψ, hψX, hψ, hmap⟩ := affine_integral_map S E r b eRel θ V hAffine hθAffine
  let x (i : ULift.{u} (Fin (r + 1))) : A.grading V 1 :=
    ⟨ψ (MvPolynomial.X i), ψ.map_mem
      (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i)⟩
  have hgen (i) : x i = symmetricGenerator E V (m i) := Subtype.ext (hψX i)
  have hp : j ⁻¹ᵁ (p ⁻¹ᵁ V.1) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, A.relProjι_relProjHom,
      Scheme.Hom.comp_preimage, V.1.ι_preimage_self, Scheme.Hom.preimage_top]
  have hki (i) : (j ≫ f) ⁻¹ᵁ ProjectiveSpace.standardOpen _ S i =
      Proj.basicOpen (A.grading V) (x i).val := by
    change (j ≫ f ≫ ProjectiveSpace.toProjInt _ S) ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule _ (ULift.{u} ℤ))
        (MvPolynomial.X i) = _
    rw [hmap, Proj.map_preimage_basicOpen]
  have hpre (i) : j ⁻¹ᵁ
      (p ⁻¹ᵁ V.1 ⊓ f ⁻¹ᵁ ProjectiveSpace.standardOpen _ S i) =
      Proj.basicOpen (A.grading V) (x i).val := by
    change j ⁻¹ᵁ (p ⁻¹ᵁ V.1) ⊓ (j ≫ f) ⁻¹ᵁ ProjectiveSpace.standardOpen _ S i = _
    rw [hp, top_inf_eq, hki]
  intro i
  let W := p ⁻¹ᵁ V.1 ⊓ f ⁻¹ᵁ ProjectiveSpace.standardOpen _ S i
  have hW : W ≤ j.opensRange := by
    rw [← A.relProjHom_preimage V]
    exact inf_le_left
  have hnW (k) : (D.chart V).hom.app (j ⁻¹ᵁ W)
      (tensorPullbackSection j D.line W
        (D.line.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (q k))) =
      (Proj.unitToTwist (x k).property).app (j ⁻¹ᵁ W)
        (1 : Γ(Proj (A.grading V), j ⁻¹ᵁ W)) := by
    have hlocal : D.line.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (q k) =
        D.line.presheaf.map (homOfLE (inf_le_left : W ≤ p ⁻¹ᵁ V.1)).op
          (σ.app V.1 (m k)) := by
      rw [quotient_basis_restrict S E D r b V k,
        presheaf_map_homOfLE_map_homOfLE]
      rfl
    rw [hlocal, hgen]
    exact quotient_chart_section S E D V (m k) W inf_le_left
  constructor
  · refine free_of_chart_section j D.line _ (D.chart V) W hW _ _ (hnW i) ?_
    rw [hpre i]
    exact Proj.isFreeGenerator_unitToTwist (x i).property
  · intro k
    let c := A.relProj.presheaf.map (homOfLE
      (inf_le_right : W ≤ f ⁻¹ᵁ ProjectiveSpace.standardOpen _ S i)).op
        (f.app (ProjectiveSpace.standardOpen _ S i) (ProjectiveSpace.coordRatio _ S i k))
    refine relation_of_chart_sections j D.line _ (D.chart V) W hW _ _ _ _
      (hnW k) (hnW i) c ?_
    have hB : j ⁻¹ᵁ W ≤ Proj.basicOpen (A.grading V) (x i).val := (hpre i).le
    have hBi : Proj.basicOpen (A.grading V) (ψ (MvPolynomial.X i)) ≤
        (j ≫ f) ⁻¹ᵁ ProjectiveSpace.standardOpen _ S i := by
      exact (hki i).ge
    have hR := proj_polynomial_ratio _ S (A.grading V) ψ hψ (j ≫ f) hmap i k hBi
    simp only [MvPolynomial.awayXRatio, HomogeneousLocalization.Away.map_mk] at hR
    have hR' := congrArg ((Proj (A.grading V)).presheaf.map (homOfLE hB).op) hR
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at hR'
    have hz := congrArg (fun z ↦ z (ProjectiveSpace.coordRatio _ S i k))
      (Scheme.Hom.appLE_comp_appLE j f (ProjectiveSpace.standardOpen _ S i) W
        (j ⁻¹ᵁ W) inf_le_right le_rfl)
    change j.app W c = _ at hz
    have hc := hz.trans hR'
    rw [hc]
    exact unit_section_relation (Proj.unitToTwist (x k).property)
      (Proj.unitToTwist (x i).property) le_top hB _
      (Proj.map_unitToTwist_eq_smul (x k).property (x i).property
        (by simpa only [one_smul] using (x k).property))

end AlgebraicGeometry.SymmetricProjTautologicalCharts

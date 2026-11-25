/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientChartInverseData
import all WeilConjectures.AlgebraicGeometry.Line.LineQuotientHomogeneousFractionMap
import all WeilConjectures.AlgebraicGeometry.Graded.GradedLineHomogeneousFractionAtlas
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.CategoryTheory.Functor.EpiMono

/-! # LineQuotientPullbackCharts

## References

* Stacks Project, Constructions, Tags 01OA and 01O4
* Stacks Project, Constructions, Tags 01OA and 01O4, functoriality
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.ProjectiveBundleQuotientGeometry
open Scheme.Modules

attribute [local instance] instModuleRestrictedSections

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackSection

private theorem sectionAdjunction_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (m : Γ(M, U)) :
    ((tensorPullbackSectionAdjunction f).unit.app M).app U m =
      tensorPullbackSection f M U m :=
  (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction f)).1 M U m

private theorem tensorPullback_epi {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (q : M ⟶ N) [Epi q] : Epi ((tensorPullback f).map q) := by
  let : (tensorPullback f).IsLeftAdjoint := (tensorPullbackSectionAdjunction f).isLeftAdjoint
  infer_instance

private theorem lineQuotientPullback_epi {S T T' : Scheme.{u}} (h : T ⟶ S)
    (u : T' ⟶ T) (E : S.Modules) (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L) [Epi q] :
    Epi (lineQuotientPullback h u E L q) := by
  let := tensorPullback_epi u q
  unfold lineQuotientPullback
  infer_instance

private theorem tensorPullbackSection_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (v : M ⟶ N) (U : Y.Opens) (m : Γ(M, U)) :
    ((tensorPullback f).map v).app (f ⁻¹ᵁ U) (tensorPullbackSection f M U m) =
      tensorPullbackSection f N U (v.app U m) := by
  rw [← sectionAdjunction_unit, ← sectionAdjunction_unit]
  exact (congrArg (fun k ↦ k.app U m)
    ((tensorPullbackSectionAdjunction f).unit.naturality v)).symm

private theorem tensorPullbackSection_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens) (m : Γ(M, U)) :
    ((tensorPullbackSectionComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
        (tensorPullbackSection (f ≫ g) M U m) =
      tensorPullbackSection f ((tensorPullback g).obj M) (g ⁻¹ᵁ U)
        (tensorPullbackSection g M U m) := by
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (tensorPullbackSectionAdjunction (f ≫ g))
    (((tensorPullbackSectionAdjunction g).comp (tensorPullbackSectionAdjunction f)).ofNatIsoRight
      (pushforwardComp f g)) M
  have hv := congrArg (fun k ↦ k.app U m) hu
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Adjunction.comp_unit_app,
    Functor.whiskerLeft_app, pushforwardComp_hom_app_app] at hv
  change ((tensorPullbackSectionComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
    (((tensorPullbackSectionAdjunction (f ≫ g)).unit.app M).app U m) =
    ((tensorPullbackSectionAdjunction f).unit.app ((tensorPullback g).obj M)).app
      (g ⁻¹ᵁ U) (((tensorPullbackSectionAdjunction g).unit.app M).app U m) at hv
  calc
    _ = ((tensorPullbackSectionComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
        (((tensorPullbackSectionAdjunction (f ≫ g)).unit.app M).app U m) :=
      congrArg _ (sectionAdjunction_unit (f ≫ g) M U m).symm
    _ = _ := hv
    _ = _ := (sectionAdjunction_unit f _ _ _).trans
      (congrArg (tensorPullbackSection f _ _) (sectionAdjunction_unit g M U m))

private theorem lineQuotientPullback_section {S T T' : Scheme.{u}}
    (h : T ⟶ S) (u : T' ⟶ T) (E : S.Modules) (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L) (U : S.Opens) (m : Γ(E, U)) :
    (lineQuotientPullback h u E L q).app ((u ≫ h) ⁻¹ᵁ U)
      (tensorPullbackSection (u ≫ h) E U m) =
      tensorPullbackSection u L (h ⁻¹ᵁ U)
        (q.app (h ⁻¹ᵁ U) (tensorPullbackSection h E U m)) := by
  unfold lineQuotientPullback
  change ((tensorPullback u).map q).app ((u ≫ h) ⁻¹ᵁ U)
    (((tensorPullbackSectionComp u h).hom.app E).app _
      (tensorPullbackSection (u ≫ h) E U m)) = _
  rw [tensorPullbackSection_comp]
  exact tensorPullbackSection_naturality u q (h ⁻¹ᵁ U)
    (tensorPullbackSection h E U m)

private theorem pullbackSection_free {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) (hs : IsFreeGenerator s) :
    IsFreeGenerator (tensorPullbackSection f M U s) := by
  let adj := tensorPullbackSectionAdjunction f
  let cmp := adj.leftAdjointUniq (pullbackPushforwardAdjunction f)
  have h : (cmp.app M).hom.app (f ⁻¹ᵁ U) (tensorPullbackSection f M U s) =
      ((pullbackPushforwardAdjunction f).unit.app M).app U s := by
    rw [← sectionAdjunction_unit]
    exact congrArg (fun k ↦ k.app U s)
      (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction f) M)
  have ht := (hs.pullback_unit_app f).app_hom (cmp.app M).symm
  rw [← h] at ht
  simpa only [Iso.symm_hom, inv_app_hom_app_apply_of_iso] using ht

private theorem pullbackSection_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) {U V : Y.Opens} (j : V ≤ U) (s : Γ(M, U)) :
    tensorPullbackSection f M V (M.presheaf.map (homOfLE j).op s) =
      ((tensorPullback f).obj M).presheaf.map (homOfLE (f.preimage_mono j)).op
        (tensorPullbackSection f M U s) := by
  rw [← sectionAdjunction_unit, ← sectionAdjunction_unit]
  exact Hom.app_presheaf_map _ _ _

private theorem pullbackSection_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (r : Γ(Y, U)) (s : Γ(M, U)) :
    tensorPullbackSection f M U (r • s) =
      f.app U r • tensorPullbackSection f M U s := by
  rw [← sectionAdjunction_unit, ← sectionAdjunction_unit]
  exact Hom.app_smul _ r s

private theorem generator_pullback {S T T' : Scheme.{u}} (h : T ⟶ S)
    (u : T' ⟶ T) (E : S.Modules) (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l)
    (W' : T'.affineOpens) (hWW' : W'.1 ≤ u ⁻¹ᵁ W.1)
    (hW'U : W'.1 ≤ (u ≫ h) ⁻¹ᵁ U.1) (m : Γ(E, U.1)) :
    quotientGeneratorCoefficient (u ≫ h) E ((tensorPullback u).obj L)
      (lineQuotientPullback h u E L q) U W' hW'U
      (((tensorPullback u).obj L).val.map (homOfLE hWW').op
        (tensorPullbackSection u L W.1 l)) m =
      u.appLE W.1 W'.1 hWW' (quotientGeneratorCoefficient h E L q U W hWU l m) := by
  have hl' : IsFreeGenerator
      (((tensorPullback u).obj L).val.map (homOfLE hWW').op
        (tensorPullbackSection u L W.1 l)) := (pullbackSection_free u L W.1 l hl).map hWW'
  apply hl'.smul_left_injective
  dsimp only
  erw [quotientGeneratorCoefficient_smul (u ≫ h) E _
    (lineQuotientPullback h u E L q) U W' hW'U _ hl' m]
  have he := congrArg (fun z ↦ ((tensorPullback u).obj L).presheaf.map
    (homOfLE hWW').op (tensorPullbackSection u L W.1 z))
    (quotientGeneratorCoefficient_smul h E L q U W hWU l hl m)
  rw [pullbackSection_smul, map_smul] at he
  change u.appLE W.1 W'.1 hWW'
      (quotientGeneratorCoefficient h E L q U W hWU l m) •
      (((tensorPullback u).obj L).val.map (homOfLE hWW').op
        (tensorPullbackSection u L W.1 l)) = _ at he
  rw [he]
  erw [Hom.app_presheaf_map, lineQuotientPullback_section,
    Hom.app_presheaf_map, pullbackSection_map, presheaf_map_map_apply]
  rfl

private noncomputable def coefficientRing {S T : Scheme.{u}} {h : T ⟶ S}
    {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L) (U : S.affineOpens) (W : T.affineOpens)
    (hWU : W.1 ≤ h ⁻¹ᵁ U.1) (l : Γ(L, W.1)) (hl : IsFreeGenerator l) :
    A.obj U →+* Γ(T, W.1) :=
  atlasCoefficientRingHom ψ (fun l n ↦ quotientFramePower l n)
    (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl) U W hWU l hl
    (ψ.quotientCoefficient U W hWU l)
    (quotientCoefficient_smul_frame ψ U W hWU l hl)

private theorem coefficientRing_apply {S T : Scheme.{u}} {h : T ⟶ S}
    {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L) (U : S.affineOpens) (W : T.affineOpens)
    (hWU : W.1 ≤ h ⁻¹ᵁ U.1) (l : Γ(L, W.1)) (hl : IsFreeGenerator l)
    (d : ℕ) (z : A.grading U d) :
    coefficientRing ψ U W hWU l hl z.val = ψ.quotientCoefficient U W hWU l d z :=
  atlasCoefficientRingHom_apply ψ (fun l n ↦ quotientFramePower l n)
    (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl) U W hWU l hl
    (ψ.quotientCoefficient U W hWU l)
    (quotientCoefficient_smul_frame ψ U W hWU l hl) d z

private theorem coefficientRing_scalar {S T : Scheme.{u}} {h : T ⟶ S}
    {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L) (U : S.affineOpens) (W : T.affineOpens)
    (hWU : W.1 ≤ h ⁻¹ᵁ U.1) (l : Γ(L, W.1)) (hl : IsFreeGenerator l)
    (r : Γ(S, U.1)) :
    coefficientRing ψ U W hWU l hl (algebraMap Γ(S, U.1) (A.obj U) r) =
      h.appLE U.1 W.1 hWU r := by
  let z : A.grading U 0 :=
    ⟨algebraMap Γ(S, U.1) (A.obj U) r, SetLike.algebraMap_mem_graded _ r⟩
  change coefficientRing ψ U W hWU l hl z.val = _
  rw [coefficientRing_apply]
  apply (isFreeGenerator_one W.1).smul_left_injective
  change _ • quotientFramePower l 0 = _ • quotientFramePower l 0
  rw [quotientCoefficient_smul_frame ψ U W hWU l hl]
  have hz : z = r • ⟨1, SetLike.one_mem_graded (A.grading U)⟩ := by
    ext
    exact (Algebra.smul_def r 1).trans (mul_one _ ) |>.symm
  rw [hz, ψ.smul, ψ.one]
  change (𝟙_ T.Modules).presheaf.map (homOfLE hWU).op
    (h.app U.1 r • unitSectionsEquiv (h ⁻¹ᵁ U.1) 1) = _
  rw [map_smul]
  rw [presheaf_map_unitSectionsEquiv, map_one]
  rfl

private theorem homogeneous_pullback {S T T' : Scheme.{u}} (h : T ⟶ S)
    (u : T' ⟶ T) (E : S.Modules) [E.IsQuasicoherent]
    (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (ψ' : RelativeGradedLineMap (u ≫ h) (SymmetricAlgebraSheaf.gradedAlgebraData E)
      ((tensorPullback u).obj L))
    (hψ' : ψ'.ExtendsLineQuotient (u ≫ h) E _ (lineQuotientPullback h u E L q))
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l)
    (W' : T'.affineOpens) (hWW' : W'.1 ≤ u ⁻¹ᵁ W.1)
    (hW'U : W'.1 ≤ (u ≫ h) ⁻¹ᵁ U.1) (d : ℕ)
    (z : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d) :
    ψ'.quotientCoefficient U W' hW'U
      (((tensorPullback u).obj L).val.map (homOfLE hWW').op
        (tensorPullbackSection u L W.1 l)) d z =
      u.appLE W.1 W'.1 hWW' (ψ.quotientCoefficient U W hWU l d z) := by
  let l' : Γ((tensorPullback u).obj L, W'.1) := ((tensorPullback u).obj L).val.map (homOfLE hWW').op
    (tensorPullbackSection u L W.1 l)
  have hl' : IsFreeGenerator l' := (pullbackSection_free u L W.1 l hl).map hWW'
  let α := coefficientRing ψ U W hWU l hl
  let α' := coefficientRing ψ' U W' hW'U l' hl'
  have he : α' = (u.appLE W.1 W'.1 hWW').hom.comp α := by
    ext a
    change α' a = u.appLE W.1 W'.1 hWW' (α a)
    induction a using SymmetricAlgebra.induction with
    | algebraMap r =>
      dsimp only [α, α']
      erw [coefficientRing_scalar ψ' U W' hW'U l' hl' r,
        coefficientRing_scalar ψ U W hWU l hl r]
      exact (congrArg (fun f : CommRingCat.of Γ(S, U.1) ⟶
          CommRingCat.of Γ(T', W'.1) ↦ f r)
        (Scheme.Hom.appLE_comp_appLE u h U.1 W.1 W'.1 hWU hWW')).symm
    | ι m =>
      change α' (quotientSymmetricGenerator E U m).val =
        u.appLE W.1 W'.1 hWW' (α (quotientSymmetricGenerator E U m).val)
      dsimp only [α, α']
      rw [coefficientRing_apply, coefficientRing_apply,
        quotientCoefficient_generator ψ hψ U W hWU l hl,
        quotientCoefficient_generator ψ' hψ' U W' hW'U l' hl']
      exact generator_pullback h u E L q U W hWU l hl W' hWW' hW'U m
    | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  have hz := congrArg (fun f ↦ f z.val) he
  simpa only [RingHom.comp_apply, coefficientRing_apply, α, α'] using hz

private theorem fractionSource_pullback {T T' : Scheme.{u}} (u : T' ⟶ T)
    (W : T.affineOpens) (W' : T'.affineOpens) (j : W'.1 ≤ u ⁻¹ᵁ W.1)
    (b : Γ(T, W.1)) :
    quotientFractionSource W' (u.appLE W.1 W'.1 j b) ≫ u =
      Spec.map (CommRingCat.ofHom (Localization.awayMap (u.appLE W.1 W'.1 j).hom b)) ≫
        quotientFractionSource W b := by
  change Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ W'.2.fromSpec ≫ u =
    Spec.map (CommRingCat.ofHom _) ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ W.2.fromSpec
  rw [← W.2.SpecMap_appLE_fromSpec u W'.2 j, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc]
  congr 2
  ext r
  change algebraMap Γ(T', W'.1) _ (u.appLE W.1 W'.1 j r) =
    Localization.awayMap (u.appLE W.1 W'.1 j).hom b
      (algebraMap Γ(T, W.1) _ r)
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]

private theorem pullback_map_eq {S T T' : Scheme.{u}} (h : T ⟶ S)
    (u : T' ⟶ T) (E : S.Modules) [E.IsQuasicoherent]
    (L : T.Modules) [L.IsInvertible] (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hcharts : ψ.HasQuotientFractionCharts h E L q F)
    (ψ' : RelativeGradedLineMap (u ≫ h) (SymmetricAlgebraSheaf.gradedAlgebraData E)
      ((tensorPullback u).obj L))
    (hψ' : ψ'.ExtendsLineQuotient (u ≫ h) E _ (lineQuotientPullback h u E L q))
    (F' : T' ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hcharts' : ψ'.HasQuotientFractionCharts (u ≫ h) E _
      (lineQuotientPullback h u E L q) F') : F' = u ≫ F := by
  let := (SymmetricAlgebraSheaf.gradedAlgebraData E).gradedAlgebra
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := h (u x)) (U := ⊤) trivial
  let U : S.affineOpens := ⟨V, hV⟩
  have hxU : u x ∈ h ⁻¹ᵁ U.1 := hxV
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  obtain ⟨W, hxW, hWU, l, hl⟩ := exists_isFreeGenerator L hxU
  obtain ⟨V', hV', hxV', hV'W⟩ := exists_isAffineOpen_mem_and_subset
    (x := x) (U := u ⁻¹ᵁ W.1) hxW
  let W' : T'.affineOpens := ⟨V', hV'⟩
  have hWW' : W'.1 ≤ u ⁻¹ᵁ W.1 := hV'W
  have hW'U : W'.1 ≤ (u ≫ h) ⁻¹ᵁ U.1 := hWW'.trans (u.preimage_mono hWU)
  let l' : Γ((tensorPullback u).obj L, W'.1) := ((tensorPullback u).obj L).val.map (homOfLE hWW').op
    (tensorPullbackSection u L W.1 l)
  have hl' : IsFreeGenerator l' := (pullbackSection_free u L W.1 l hl).map hWW'
  have hW := hcharts.2 U W hWU l hl
  have hW' := hcharts'.2 U W' hW'U l' hl'
  have hx : x ∈ (⨆ m : Γ(E, U.1), T'.basicOpen
      (quotientGeneratorCoefficient (u ≫ h) E _
        (lineQuotientPullback h u E L q) U W' hW'U l' m)) := by
    rw [hW'.2.2.1]
    exact hxV'
  obtain ⟨m, hxm⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨ρ, hρ⟩ := hW.2.2.2.1 m
  have hgen := generator_pullback h u E L q U W hWU l hl W' hWW' hW'U m
  have hcoef := homogeneous_pullback h u E L q ψ hψ ψ' hψ' U W hWU l hl
    W' hWW' hW'U
  obtain ⟨ρ₀, hρ₀⟩ := hW'.2.2.2.1 m
  have hc' : ∃ ρ : HomogeneousLocalization.Away
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).val →+*
        Localization.Away (quotientGeneratorCoefficient (u ≫ h) E _
          (lineQuotientPullback h u E L q) U W' hW'U l' m),
      (∀ (d : ℕ) (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
        ρ (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
          (quotientSymmetricGenerator E U m) d a) =
        Localization.mk (ψ'.quotientCoefficient U W' hW'U l' d a)
          (⟨quotientGeneratorCoefficient (u ≫ h) E _
            (lineQuotientPullback h u E L q) U W' hW'U l' m ^ d, ⟨d, rfl⟩⟩ :
            Submonoid.powers _)) ∧
      quotientFractionSource W' (quotientGeneratorCoefficient (u ≫ h) E _
        (lineQuotientPullback h u E L q) U W' hW'U l' m) ≫ F' =
        Spec.map (CommRingCat.ofHom ρ) ≫
          Proj.awayι ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
            (quotientSymmetricGenerator E U m).val
            (quotientSymmetricGenerator E U m).property (by decide : 0 < (1 : ℕ)) ≫
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U :=
    ⟨ρ₀, hρ₀.1, hρ₀.2.2.1⟩
  dsimp only [l'] at hc'
  rw [hgen] at hc'
  obtain ⟨ρ', hρ'⟩ := hc'
  let b := quotientGeneratorCoefficient h E L q U W hWU l m
  let β := Localization.awayMap (u.appLE W.1 W'.1 hWW').hom b
  have hβ (d : ℕ) (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d) :
      β (Localization.mk (ψ.quotientCoefficient U W hWU l d a)
        (⟨b ^ d, ⟨d, rfl⟩⟩ : Submonoid.powers b)) =
      Localization.mk (ψ'.quotientCoefficient U W' hW'U l' d a)
        (⟨u.appLE W.1 W'.1 hWW' b ^ d, ⟨d, rfl⟩⟩ :
          Submonoid.powers (u.appLE W.1 W'.1 hWW' b)) := by
    rw [hcoef]
    simp only [β, Localization.mk_eq_mk',
      IsLocalization.Away.map, IsLocalization.map_mk', map_pow]
  have he : ρ' = β.comp ρ := by
    let := (SymmetricAlgebraSheaf.gradedAlgebraData E).gradedAlgebra U
    ext z
    obtain ⟨d, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).property z
    have ha' : a ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d := by
      simpa only [smul_eq_mul, mul_one] using ha
    exact (hρ'.1 d ⟨a, ha'⟩).trans
      ((hβ d ⟨a, ha'⟩).symm.trans (congrArg β (hρ.1 d ⟨a, ha'⟩).symm))
  have hs := fractionSource_pullback u W W' hWW' b
  have hmaps : quotientFractionSource W' (u.appLE W.1 W'.1 hWW' b) ≫ F' =
      quotientFractionSource W' (u.appLE W.1 W'.1 hWW' b) ≫ (u ≫ F) := by
    rw [← Category.assoc, hs, Category.assoc, hρ.2.2.1, hρ'.2, he]
    simp only [← Category.assoc, ← Spec.map_comp]
    rfl
  let f := quotientFractionSource W' (u.appLE W.1 W'.1 hWW' b)
  refine ⟨f.opensRange, ?_, ?_⟩
  · rw [quotientFractionSource_opensRange]
    exact hgen ▸ hxm
  · rw [← cancel_epi (Scheme.Hom.isoOpensRange f).hom]
    simpa only [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι] using hmaps

/-- The coefficientwise pullback of a fraction-chart morphism satisfies the fraction
charts of the pulled quotient and preserves all homogeneous and generator coefficients. -/
theorem lineQuotient_pullback_charts {S T T' : Scheme.{u}} (h : T ⟶ S)
    (u : T' ⟶ T) (E : S.Modules) [E.IsQuasicoherent]
    (L : T.Modules) [L.IsInvertible] (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hcharts : ψ.HasQuotientFractionCharts h E L q F)
    (ψ' : RelativeGradedLineMap (u ≫ h) (SymmetricAlgebraSheaf.gradedAlgebraData E)
      ((tensorPullback u).obj L))
    (hψ' : ψ'.ExtendsLineQuotient (u ≫ h) E _ (lineQuotientPullback h u E L q)) :
    ψ'.HasQuotientFractionCharts (u ≫ h) E _ (lineQuotientPullback h u E L q) (u ≫ F) ∧
      (∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
          (l : Γ(L, W.1)), IsFreeGenerator l →
          ∀ (W' : T'.affineOpens) (hWW' : W'.1 ≤ u ⁻¹ᵁ W.1)
            (hW'U : W'.1 ≤ (u ≫ h) ⁻¹ᵁ U.1),
            (∀ (d : ℕ) (z : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
              ψ'.quotientCoefficient U W' hW'U
                (((tensorPullback u).obj L).val.map (homOfLE hWW').op
                  (tensorPullbackSection u L W.1 l)) d z =
                u.appLE W.1 W'.1 hWW' (ψ.quotientCoefficient U W hWU l d z)) ∧
            ∀ m : Γ(E, U.1),
              quotientGeneratorCoefficient (u ≫ h) E ((tensorPullback u).obj L)
                (lineQuotientPullback h u E L q) U W' hW'U
                (((tensorPullback u).obj L).val.map (homOfLE hWW').op
                  (tensorPullbackSection u L W.1 l)) m =
                u.appLE W.1 W'.1 hWW'
                  (quotientGeneratorCoefficient h E L q U W hWU l m)) := by
  have := ((invertible_pullback_tensor u).1 L).2
  have := lineQuotientPullback_epi h u E L q
  obtain ⟨ψ₀, _, hψ₀, _, F', hc', _, _, _⟩ :=
    line_quotient_homogeneous_fraction_map (u ≫ h) E _ (lineQuotientPullback h u E L q)
  have he := hψ₀ ψ' hψ'
  subst ψ₀
  have hF := pullback_map_eq h u E L q ψ hψ F hcharts ψ' hψ' F' hc'
  constructor
  · rw [← hF]
    exact hc'
  · intro U W hWU l hl W' hWW' hW'U
    exact ⟨homogeneous_pullback h u E L q ψ hψ ψ' hψ' U W hWU l hl W' hWW' hW'U,
      generator_pullback h u E L q U W hWU l hl W' hWW' hW'U⟩

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry

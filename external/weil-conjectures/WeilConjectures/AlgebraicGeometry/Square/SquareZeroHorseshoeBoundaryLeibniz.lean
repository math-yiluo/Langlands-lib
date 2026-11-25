/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.AlgebraicGeometry.Boundary.BoundaryCechCompatibility
import WeilConjectures.AlgebraicGeometry.CechH1MapNatural
import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
import WeilConjectures.Topology.Sheaves.CechComparison

import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-! # The Leibniz identity for a fixed quotient action and horseshoe boundary

Source: Stacks Project, Cohomology, Lemma 0B8S, local-lift computation.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

private local instance squareZeroModuleProducts (R : Type u) [Ring R] (J : Type v)
    [Small.{u} J] : HasLimitsOfShape (Discrete J) (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfShape

set_option backward.isDefEq.respectTransparency false in
private theorem common_lifts (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (hep : Epi ((commAlgebraSheafModuleFunctor X.sheaf).map p))
    (f g : C.right.obj.obj (op ⊤)) :
    ∃ (ι : Type u) (U : ι → X.Opens), iSup U = ⊤ ∧
      ∃ (b c : ∀ a, B.right.obj.obj (op (U a))),
        (∀ a, p.right.hom.app (op (U a)) (b a) =
          C.right.obj.map (homOfLE le_top).op f) ∧
        (∀ a, p.right.hom.app (op (U a)) (c a) =
          C.right.obj.map (homOfLE le_top).op g) := by
  classical
  have h := ((RingedSpace.module_exactness_local_lifting X.toRingedSpace).2.1
    (commAlgebraSheafModule X.sheaf B) (commAlgebraSheafModule X.sheaf C)
    ((commAlgebraSheafModuleFunctor X.sheaf).map p)).2.mpr hep
  obtain ⟨J, V, hV, b, hcoverV, hb⟩ := h ⊤ f
  obtain ⟨K, W, hW, c, hcoverW, hc⟩ := h ⊤ g
  let U : J × K → X.Opens := fun a ↦ V a.1 ⊓ W a.2
  refine ⟨J × K, U, ?_,
    (fun a ↦ B.right.obj.map (homOfLE inf_le_left).op (b a.1)),
    (fun a ↦ B.right.obj.map (homOfLE inf_le_right).op (c a.2)), ?_, ?_⟩
  · dsimp [U]
    simp only [iSup_prod, ← inf_iSup_eq, ← iSup_inf_eq]
    rw [hcoverV, hcoverW, inf_top_eq]
  · intro a
    have hn := congrArg (fun m ↦ m (b a.1))
      (p.right.hom.naturality (homOfLE (inf_le_left : U a ≤ V a.1)).op)
    simp only [ConcreteCategory.comp_apply] at hn
    rw [hn]
    have hb' := hb a.1
    change p.right.hom.app _ (b a.1) = C.right.obj.map _ f at hb'
    rw [hb']
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  · intro a
    have hn := congrArg (fun m ↦ m (c a.2))
      (p.right.hom.naturality (homOfLE (inf_le_right : U a ≤ W a.2)).op)
    simp only [ConcreteCategory.comp_apply] at hn
    rw [hn]
    have hc' := hc a.2
    change p.right.hom.app _ (c a.2) = C.right.obj.map _ g at hc'
    rw [hc']
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

/-- Cancel a common comparison map before transporting along the target isomorphism. -/
private theorem boundary_eq_of_comparison {D : Type*} [Category* D]
    {A B C E F : D} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ E) [Epi c]
    (d : E ⟶ C) (e : F ≅ C) (f : E ⟶ F)
    (h : a ≫ b = c ≫ d) (h' : a ≫ b ≫ e.inv = c ≫ f) :
    d = f ≫ e.hom := by
  rw [← Category.assoc, h, Category.assoc] at h'
  have hd := (cancel_epi c).1 h'
  rw [← hd, Category.assoc, e.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem snake_boundary_eq_triangle (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{u + 1}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (S : ShortComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace))) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hz : α ≫ β = 0)
    (ha : IA.ι ≫ α = (CochainComplex.single₀ _).map S.f ≫ IB.ι)
    (hb : IB.ι ≫ β = (CochainComplex.single₀ _).map S.g ≫ IC.ι)
    (hr : ∀ k : ℕ, ((ShortComplex.mk α β hz).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) k)).ShortExact)
    (hΓ : ((ShortComplex.mk α β hz).map
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ))).ShortExact) :
    (IC.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0).hom ≫
      hΓ.δ 0 1 rfl ≫
      (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).inv =
        RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0 := by
  let v := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : PreservesFiniteLimits v := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
  obtain ⟨G, hF, hsnake, htriangle⟩ := rightDerived_triangle_connecting v
  obtain ⟨hΓ', heq⟩ := hsnake S hS IA IB IC α β hz ha hb hr
  have h := boundary_eq_of_comparison _ _ _ _
    (v.homologyRightDerivedFunctorPlusObjSingleFunctorIso S.X₁ 1) _
    (heq 0) (htriangle S hS 0)
  simp only [Category.assoc] at h
  dsimp only [v] at h
  dsimp only [RingedSpace.moduleCohomologyBoundary,
    Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso]
  simp only [NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app]
  exact h

/-- The Leibniz identity on local-lift cocycles, independent of derived-category comparisons. -/
private theorem cech_cycles_leibniz (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (i : I ⟶ commAlgebraSheafModule X.sheaf B)
    (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw).ShortExact)
    (μ : C.right.obj.obj (op ⊤) →+* End I)
    (hlift : ∀ (f : C.right.obj.obj (op ⊤)) (U : X.Opens)
      (b : B.right.obj.obj (op U)) (x : I.val.obj (op U)),
      p.right.hom.app (op U) b = C.right.obj.map (homOfLE le_top).op f →
      @id (B.right.obj.obj (op U)) (i.val.app (op U) ((μ f).asHom.val.app (op U) x)) =
        b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x))
    {ι : Type u} (U : ι → X.Opens) (f g : C.right.obj.obj (op ⊤))
    (b c : ∀ a, B.right.obj.obj (op (U a)))
    (hb : ∀ a, p.right.hom.app (op (U a)) (b a) =
      C.right.obj.map (homOfLE le_top).op f)
    (hc : ∀ a, p.right.hom.app (op (U a)) (c a) =
      C.right.obj.map (homOfLE le_top).op g) :
    let K := (CategoryTheory.cechComplexFunctor U).obj (show X.Modules from I).presheafModuleCat
    let act (s : C.right.obj.obj (op ⊤)) := (CategoryTheory.cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map (μ s).asHom.val)
    ∀ zf zg zfg : K.cycles 1,
      (∀ y : Fin 2 → ι,
        i.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
          (TopCat.Presheaf.cechComplexFunctorπ U
            (show X.Modules from I).presheafModuleCat 1 y (K.iCycles 1 zf)) =
          B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (b (y 1)) -
            B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (b (y 0))) →
      (∀ y : Fin 2 → ι,
        i.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
          (TopCat.Presheaf.cechComplexFunctorπ U
            (show X.Modules from I).presheafModuleCat 1 y (K.iCycles 1 zg)) =
          B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (c (y 1)) -
            B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (c (y 0))) →
      (∀ y : Fin 2 → ι,
        i.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
          (TopCat.Presheaf.cechComplexFunctorπ U
            (show X.Modules from I).presheafModuleCat 1 y (K.iCycles 1 zfg)) =
          B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (b (y 1) * c (y 1)) -
            B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (b (y 0) * c (y 0))) →
      zfg = HomologicalComplex.cyclesMap (act f) 1 zg +
        HomologicalComplex.cyclesMap (act g) 1 zf := by
  classical
  intro K act zf zg zfg hzf hzg hzfg
  have hinj : Function.Injective (K.iCycles 1) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hinj
  apply TopCat.Presheaf.cechComplexFunctor_ext U
    (show X.Modules from I).presheafModuleCat
  intro y
  let W := ∏ᶜ fun k : Fin 2 ↦ U (y k)
  let π := TopCat.Presheaf.cechComplexFunctorπ U
    (show X.Modules from I).presheafModuleCat 1 y
  let bf := fun k : Fin 2 ↦ B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (y k)) k).op
    (b (y k))
  let cg := fun k : Fin 2 ↦ B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (y k)) k).op
    (c (y k))
  have hlb (k : Fin 2) : p.right.hom.app (op W) (bf k) =
      C.right.obj.map (homOfLE le_top).op f := by
    dsimp [bf]
    rw [← ConcreteCategory.comp_apply, p.right.hom.naturality]
    simp only [ConcreteCategory.comp_apply, hb]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hlc (k : Fin 2) : p.right.hom.app (op W) (cg k) =
      C.right.obj.map (homOfLE le_top).op g := by
    dsimp [cg]
    rw [← ConcreteCategory.comp_apply, p.right.hom.naturality]
    simp only [ConcreteCategory.comp_apply, hc]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hφ (s : C.right.obj.obj (op ⊤)) (z : K.cycles 1) :
      π (K.iCycles 1 (HomologicalComplex.cyclesMap (act s) 1 z)) =
        (μ s).asHom.val.app (op W) (π (K.iCycles 1 z)) := by
    have hi := congrArg (fun m ↦ m z) (HomologicalComplex.cyclesMap_i (act s) 1)
    have hp := TopCat.Presheaf.cechComplexFunctor_map_f_π U
      (show X.Modules from I).presheafModuleCat
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        (μ s).asHom.val) 1 y
    dsimp only [act] at hi
    simp only [ConcreteCategory.comp_apply] at hi
    erw [hi]
    exact congrArg (fun m ↦ m (K.iCycles 1 z)) hp
  have hm : Mono i := hS.mono_f
  let E := SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op W)
  have hii : Function.Injective (i.val.app (op W)) :=
    (ModuleCat.mono_iff_injective (E.map i)).mp inferInstance
  apply hii
  change i.val.app (op W) (π (K.iCycles 1 zfg)) =
    i.val.app (op W) (π (K.iCycles 1
      (HomologicalComplex.cyclesMap (act f) 1 zg +
        HomologicalComplex.cyclesMap (act g) 1 zf)))
  rw [map_add, map_add, map_add, hφ, hφ]
  simp only [id_eq] at hlift
  erw [hlift f W (bf 0) _ (hlb 0), hlift g W (cg 1) _ (hlc 1)]
  have hf' := hzf y
  have hg' := hzg y
  have hfg' := hzfg y
  change i.val.app (op W) (π (K.iCycles 1 zf)) = bf 1 - bf 0 at hf'
  change i.val.app (op W) (π (K.iCycles 1 zg)) = cg 1 - cg 0 at hg'
  change i.val.app (op W) (π (K.iCycles 1 zfg)) =
    B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (b (y 1) * c (y 1)) -
      B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op
        (b (y 0) * c (y 0)) at hfg'
  rw [hf', hg', hfg']
  simp only [map_mul]
  change bf 1 * cg 1 - bf 0 * cg 0 = bf 0 * (cg 1 - cg 0) + cg 1 * (bf 1 - bf 0)
  ring

/-- Transfer the cocycle identity to the canonical boundary using the natural Čech comparison. -/
private theorem canonical_boundary_leibniz (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{u + 1}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (i : I ⟶ commAlgebraSheafModule X.sheaf B)
    (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw).ShortExact)
    (μ : C.right.obj.obj (op ⊤) →+* End I)
    (hlift : ∀ (f : C.right.obj.obj (op ⊤)) (U : X.Opens)
      (b : B.right.obj.obj (op U)) (x : I.val.obj (op U)),
      p.right.hom.app (op U) b = C.right.obj.map (homOfLE le_top).op f →
      @id (B.right.obj.obj (op U)) (i.val.app (op U) ((μ f).asHom.val.app (op U) x)) =
        b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x)) :
    let S := ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw
    ∀ f g : C.right.obj.obj (op ⊤),
      RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃
            (f * g)) =
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).map (μ f).asHom).hom
          (RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ g)) +
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).map (μ g).asHom).hom
          (RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
              S.X₃ f)) := by
  classical
  intro S f g
  obtain ⟨ι, U, hU, b, c, hb, hc⟩ := common_lifts X B C p hS.epi_g f g
  obtain ⟨cmp, hcmp, hnatural⟩ := Scheme.Modules.cechH1Map_natural X U hU
  have ht : ∀ a, p.right.hom.app (op (U a)) (b a * c a) =
      C.right.obj.map (homOfLE le_top).op (f * g) := by
    intro a
    simp only [map_mul, hb, hc]
  obtain ⟨zf, hzf, hcf⟩ := Scheme.Modules.boundary_cech_compatibility X S hS U hU
    (cmp I) (hcmp I) f b hb
  obtain ⟨zg, hzg, hcg⟩ := Scheme.Modules.boundary_cech_compatibility X S hS U hU
    (cmp I) (hcmp I) g c hc
  obtain ⟨zfg, hzfg, hcfg⟩ := Scheme.Modules.boundary_cech_compatibility X S hS U hU
    (cmp I) (hcmp I) (f * g) (fun a ↦ b a * c a) ht
  let K := (CategoryTheory.cechComplexFunctor U).obj (show X.Modules from I).presheafModuleCat
  let act (f : C.right.obj.obj (op ⊤)) :=
    (CategoryTheory.cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map (μ f).asHom.val)
  have hz := cech_cycles_leibniz X B C p I i hw hS μ hlift U f g b c hb hc
    zf zg zfg hzf hzg hzfg
  have hclass : K.homologyπ 1 zfg =
      HomologicalComplex.homologyMap (act f) 1 (K.homologyπ 1 zg) +
        HomologicalComplex.homologyMap (act g) 1 (K.homologyπ 1 zf) := by
    rw [hz, map_add]
    congr 1
    · exact (congrArg (fun m ↦ m zg)
        (HomologicalComplex.homologyπ_naturality (act f) 1)).symm
    · exact (congrArg (fun m ↦ m zf)
        (HomologicalComplex.homologyπ_naturality (act g) 1)).symm
  have hn (s : C.right.obj.obj (op ⊤)) (z : K.cycles 1) :
      cmp I (HomologicalComplex.homologyMap (act s) 1 (K.homologyπ 1 z)) =
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).map (μ s).asHom).hom
          (cmp I (K.homologyπ 1 z)) := by
    exact congrArg (fun m ↦ m (K.homologyπ 1 z)) (hnatural I I (μ s).asHom)
  have he := congrArg (fun z ↦ cmp I z) hclass
  rw [map_add, hn, hn, hcf, hcg, hcfg] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
/-- The connecting map obeys Leibniz for any sheaf action agreeing with multiplication
by local lifts. The action is input; no action, cohomology action, or boundary is chosen.
Source: Stacks Project, Cohomology, Lemma 0B8S, local-lift computation.
(blueprint: lem-sc-square-zero-horseshoe-boundary-leibniz)

Proof:
1. For global f and g, the sheaf epimorphism p gives a common open cover with lifts
b_a and c_a (intersect covers for f and g). Their products lift fg. Kernel exactness
identifies overlap differences with unique sections z_f, z_g, z_fg of I; the triple
differences telescope, so these are Cech cocycles.
2. On each overlap, b_a*c_a - b_b*c_b = (b_a-b_b)*c_a + b_b*(c_a-c_b).
The lift-action hypothesis identifies the two terms with the images under i of
(mu g)(z_f) and (mu f)(z_g). Injectivity of i on sections therefore identifies z_fg
with their sum. Square-zero guarantees that replacing any lift gives the same action.
3. Apply boundary_cech_local_lifts and cechH1Map_natural. The comparison is additive
and commutes with mu f and mu g, so the preceding cocycle identity yields the same
identity on H1 for the canonical connecting classes. Either uniform convention for
Cech differences gives this identity, since changing all three signs preserves it.
4. The displayed snake map is that connecting map: compare the compatible resolutions
with a horseshoe using exists_horseshoe_rightDerived_deltaFunctor and resolution
comparison. Naturality for the identity ladder makes the transported boundaries equal;
the degree-zero augmentation identifies the section f with its H0 class through
 toRightDerivedZero. Thus the same identity holds for the specified boundary d.
For I = 0 it is the zero identity; for a split extension the boundary vanishes. -/
theorem square_zero_horseshoe_boundary_leibniz (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (i : I ⟶ commAlgebraSheafModule X.sheaf B)
    (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw).ShortExact)
    (hsq : ∀ (U : X.Opens) (x y : B.right.obj.obj (op U)),
      p.right.hom.app (op U) x = 0 → p.right.hom.app (op U) y = 0 → x * y = 0)
    (IA : InjectiveResolution I)
    (IB : InjectiveResolution (commAlgebraSheafModule X.sheaf B))
    (IC : InjectiveResolution (commAlgebraSheafModule X.sheaf C))
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ _).map i ≫ IB.ι)
    (hιB : IB.ι ≫ β =
      (CochainComplex.single₀ _).map ((commAlgebraSheafModuleFunctor X.sheaf).map p) ≫ IC.ι)
    (hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) k)).ShortExact)
    (hΓ : ((ShortComplex.mk α β hαβ).map
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ))).ShortExact)
    (μ : C.right.obj.obj (op ⊤) →+* End I)
    (hlift : ∀ (f : C.right.obj.obj (op ⊤)) (U : X.Opens)
      (b : B.right.obj.obj (op U)) (x : I.val.obj (op U)),
      p.right.hom.app (op U) b = C.right.obj.map (homOfLE le_top).op f →
      @id (B.right.obj.obj (op U)) (i.val.app (op U) ((μ f).asHom.val.app (op U) x)) =
        b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x)) :
    let d :=
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
          (commAlgebraSheafModule X.sheaf C) ≫
        (IC.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0).hom ≫
        hΓ.δ 0 1 rfl ≫
        (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).inv
    ∀ f g : C.right.obj.obj (op ⊤), d.hom (f * g) =
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).map (μ f).asHom).hom (d.hom g) +
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).map ((μ g)).asHom).hom (d.hom f) := by
  classical
  have _ := hsq
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
  let S := ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw
  have hd := snake_boundary_eq_triangle X S hS IA IB IC α β hαβ hιA hιB hH hΓ
  dsimp only
  intro f g
  have he := canonical_boundary_leibniz X B C p I i hw hS μ hlift f g
  rw [← hd] at he
  simp only [ModuleCat.comp_apply]
  exact he

end AlgebraicGeometry

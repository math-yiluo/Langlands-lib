/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.Basic.Finite.Sum
import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-!
# Finite type modules: images and extensions

Source: Stacks Project, Modules, Lemma 01B7 (blueprint:
lem-weil-pbc-module-finite-type-image-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSpace

set_option backward.isDefEq.respectTransparency false in
private theorem finiteType_of_epi (X : RingedSpace.{u})
    {F G : SheafOfModules.{u} (moduleRings X)} (p : F ⟶ G)
    [Epi p] [F.IsFiniteType] : G.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let q' : G.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (p.over (q.X i)) }
  refine { exists_localGeneratorsData := ⟨q', ?_⟩ }
  constructor
  intro i
  have := hq.isFiniteType i
  exact inferInstanceAs ((q.generators i).ofEpi (p.over (q.X i))).IsFiniteType

set_option backward.isDefEq.respectTransparency false in
private theorem finite_sections_lift (X : RingedSpace.{u})
    {F G : SheafOfModules.{u} (moduleRings X)} (p : F ⟶ G) [Epi p]
    (U : TopologicalSpace.Opens X) {I : Type u} [Finite I]
    (s : I → G.val.obj (Opposite.op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : TopologicalSpace.Opens X) (hV : V ≤ U), x ∈ V ∧
      ∃ t : I → F.val.obj (Opposite.op V), ∀ i,
        p.val.app (Opposite.op V) (t i) = G.val.map (homOfLE hV).op (s i) := by
  classical
  have hl := (module_exactness_local_lifting X).2.1 F G p |>.2.mpr inferInstance
  have hi (i : I) : ∃ (V : TopologicalSpace.Opens X) (hV : V ≤ U),
      x ∈ V ∧ ∃ t : F.val.obj (Opposite.op V),
        p.val.app (Opposite.op V) t = G.val.map (homOfLE hV).op (s i) := by
    obtain ⟨J, V, hV, t, hcover, ht⟩ := hl U (s i)
    have hx' : x ∈ ⨆ j, V j := by rw [hcover]; exact hx
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    exact ⟨V j, hV j, hj, t j, ht j⟩
  choose V hV hxV t ht using hi
  let W := U ⊓ ⨅ i, V i
  have hWU : W ≤ U := inf_le_left
  have hWV (i : I) : W ≤ V i := inf_le_right.trans (iInf_le V i)
  refine ⟨W, hWU, ?_, fun i ↦ F.val.map (homOfLE (hWV i)).op (t i), ?_⟩
  · change x ∈ (U : Set X) ∩ ((⨅ i, V i : TopologicalSpace.Opens X) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨hx, hxV⟩
  · intro i
    have hn := congrArg (fun f ↦ f (t i)) (p.val.naturality (homOfLE (hWV i)).op)
    change p.val.app (Opposite.op W) (F.val.map (homOfLE (hWV i)).op (t i)) =
      G.val.map (homOfLE (hWV i)).op (p.val.app (Opposite.op (V i)) (t i)) at hn
    rw [hn, ht i]
    exact (G.val.map_comp_apply
      (homOfLE (hV i)).op (homOfLE (hWV i)).op (s i)).symm.trans
        (G.val.congr_map_apply (Subsingleton.elim _ _) _)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def section_on_open (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X)) (U : TopologicalSpace.Opens X)
    (s : F.val.obj (Opposite.op U)) : (F.over U).sections :=
  (F.over U).val.sectionsMk
    (fun W ↦ F.val.map W.unop.hom.op s)
    (fun {W Z} f ↦ by
      change F.val.map f.unop.left.op (F.val.map W.unop.hom.op s) =
        F.val.map Z.unop.hom.op s
      exact (F.val.map_comp_apply W.unop.hom.op f.unop.left.op s).symm.trans
        (F.val.congr_map_apply (Subsingleton.elim _ _) s))

set_option backward.isDefEq.respectTransparency false in
private theorem sections_ext_top (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X)) (U : TopologicalSpace.Opens X)
    (s t : (F.over U).sections)
    (h : s.val (Opposite.op (Over.mk (𝟙 U))) =
      t.val (Opposite.op (Over.mk (𝟙 U)))) : s = t := by
  apply PresheafOfModules.sections_ext
  intro W
  let f : W.unop ⟶ Over.mk (𝟙 U) := Over.homMk W.unop.hom
  exact ((F.over U).val.sections_property s f.op).symm.trans
    ((congrArg (fun z ↦ (F.over U).val.map f.op z) h).trans
      ((F.over U).val.sections_property t f.op))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def generators_over (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X)) {U V : TopologicalSpace.Opens X}
    (σ : (F.over U).GeneratingSections) (h : V ≤ U) :
    (F.over V).GeneratingSections :=
  (σ.map (SheafOfModules.overMap (moduleRings X) (homOfLE h))
    (SheafOfModules.overMapUnitIso (R := moduleRings X) (homOfLE h)).symm).ofEpi
    ((SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).app F).hom

set_option backward.isDefEq.respectTransparency false in
private theorem generators_over_finite (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X)) {U V : TopologicalSpace.Opens X}
    (σ : (F.over U).GeneratingSections) [σ.IsFiniteType] (h : V ≤ U) :
    (generators_over X F σ h).IsFiniteType := by
  exact ⟨inferInstanceAs (Finite σ.I)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem generators_over_eval (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X)) {U V : TopologicalSpace.Opens X}
    (σ : (F.over U).GeneratingSections) (h : V ≤ U) (i : σ.I) :
    ((generators_over X F σ h).s i).val (Opposite.op (Over.mk (𝟙 V))) =
      F.val.map (homOfLE h).op ((σ.s i).val (Opposite.op (Over.mk (𝟙 U)))) := by
  let D := SheafOfModules.overMap (moduleRings X) (homOfLE h)
  let η := (SheafOfModules.overMapUnitIso (R := moduleRings X) (homOfLE h)).symm
  let e := (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).app F
  have he : SheafOfModules.ιFree i ≫
      (SheafOfModules.mapFreeIso D σ.I η).hom ≫ D.map σ.π ≫ e.hom =
      η.hom ≫ D.map (SheafOfModules.ιFree i ≫ σ.π) ≫ e.hom := by
    simp only [SheafOfModules.ιFree_mapFreeIso_hom_assoc, D.map_comp, Category.assoc]
  have hs := congrArg
    (fun f ↦ ((F.over V).unitHomEquiv f).val
      (Opposite.op (Over.mk (𝟙 V)))) he
  change ((generators_over X F σ h).s i).val
      (Opposite.op (Over.mk (𝟙 V))) =
    ((F.over U).unitHomEquiv (SheafOfModules.ιFree i ≫ σ.π)).val
      (Opposite.op (Over.mk (homOfLE h))) at hs
  have hσ : (F.over U).unitHomEquiv (SheafOfModules.ιFree i ≫ σ.π) = σ.s i :=
    congrFun ((F.over U).freeHomEquiv.apply_symm_apply σ.s) i
  rw [hσ] at hs
  exact hs.trans (((F.over U).val.sections_property (σ.s i)
    (Over.homMk (homOfLE h) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U)).op).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem generators_extension
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (σ₁ : S.X₁.GeneratingSections) (σ₃ : S.X₃.GeneratingSections)
    [σ₁.IsFiniteType] [σ₃.IsFiniteType]
    (l : SheafOfModules.free σ₃.I ⟶ S.X₂) (hl : l ≫ S.g = σ₃.π) :
    ∃ σ : S.X₂.GeneratingSections, σ.IsFiniteType := by
  have := hS.epi_g
  let p := coprod.desc (σ₁.π ≫ S.f) l
  have hp : Epi p := by
    rw [Preadditive.epi_iff_cancel_zero]
    intro Z t ht
    have h₁ : σ₁.π ≫ S.f ≫ t = 0 := by
      simpa [p] using congrArg (fun k ↦ coprod.inl ≫ k) ht
    have hf : S.f ≫ t = 0 := by
      apply (cancel_epi σ₁.π).mp
      simpa using h₁
    let d := hS.exact.desc t hf
    have h₃ : σ₃.π ≫ d = 0 := by
      change σ₃.π ≫ hS.exact.desc t hf = 0
      rw [← hl, Category.assoc, ShortComplex.Exact.g_desc]
      simpa [p] using congrArg (fun k ↦ coprod.inr ≫ k) ht
    have hd : d = 0 := by
      apply (cancel_epi σ₃.π).mp
      simpa using h₃
    rw [← hS.exact.g_desc t hf]
    change S.g ≫ d = 0
    rw [hd, comp_zero]
  have := hp
  let σ : S.X₂.GeneratingSections :=
    { I := σ₁.I ⊕ σ₃.I
      s := S.X₂.freeHomEquiv
        ((SheafOfModules.freeSumIso (R := R) σ₁.I σ₃.I).inv ≫ p)
      epi := by rw [Equiv.symm_apply_apply]; infer_instance }
  exact ⟨σ, ⟨inferInstanceAs (Finite (σ₁.I ⊕ σ₃.I))⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem extension_generators_near (X : RingedSpace.{u})
    (S : ShortComplex (SheafOfModules.{u} (moduleRings X))) (hS : S.ShortExact)
    (U₁ U₃ : TopologicalSpace.Opens X)
    (σ₁ : (S.X₁.over U₁).GeneratingSections) (σ₃ : (S.X₃.over U₃).GeneratingSections)
    [σ₁.IsFiniteType] [σ₃.IsFiniteType] (x : X) (hx₁ : x ∈ U₁) (hx₃ : x ∈ U₃) :
    ∃ V : TopologicalSpace.Opens X, x ∈ V ∧
      ∃ σ : (S.X₂.over V).GeneratingSections, σ.IsFiniteType := by
  have := hS.epi_g
  classical
  let U := U₁ ⊓ U₃
  let τ := generators_over X S.X₃ σ₃ (show U ≤ U₃ from inf_le_right)
  have : τ.IsFiniteType := generators_over_finite X S.X₃ σ₃ inf_le_right
  obtain ⟨V, hV, hxV, t, ht⟩ := finite_sections_lift X S.g U
    (fun i ↦ (τ.s i).val (Opposite.op (Over.mk (𝟙 U)))) x ⟨hx₁, hx₃⟩
  let a := generators_over X S.X₁ σ₁ (hV.trans inf_le_left)
  let b := generators_over X S.X₃ τ hV
  have : a.IsFiniteType := generators_over_finite X S.X₁ σ₁ _
  have : b.IsFiniteType := generators_over_finite X S.X₃ τ _
  let l : SheafOfModules.free b.I ⟶ S.X₂.over V :=
    (S.X₂.over V).freeHomEquiv.symm (fun i ↦ section_on_open X S.X₂ V (t i))
  have hl : l ≫ S.g.over V = b.π := by
    apply (S.X₃.over V).freeHomEquiv.injective
    funext i
    rw [SheafOfModules.freeHomEquiv_comp_apply]
    dsimp only [l]
    rw [Equiv.apply_symm_apply]
    rw [show (S.X₃.over V).freeHomEquiv b.π = b.s from
      (S.X₃.over V).freeHomEquiv.apply_symm_apply b.s]
    apply sections_ext_top X S.X₃ V
    rw [generators_over_eval]
    change S.g.val.app (Opposite.op V) (S.X₂.val.map (𝟙 _) (t i)) = _
    rw [S.X₂.val.map_id]
    exact ht i
  refine ⟨V, hxV, ?_⟩
  exact generators_extension (S.map (SheafOfModules.overFunctor (moduleRings X) V))
    (hS.map_of_exact _) a b l hl

set_option backward.isDefEq.respectTransparency false in
/-- Images of finite type module sheaves and extensions of finite type module sheaves are
finite type (blueprint: lem-weil-pbc-module-finite-type-image-extension).

Source: Stacks Project, Modules, Lemma 01B7 (blueprint:
lem-weil-pbc-module-finite-type-image-extension).
Proof: for an epimorphism, push local finite generators along the map.  The image of a
morphism is the codomain of the induced epimorphism from its source to its image.  For a
short exact sequence, locally lift finitely many generators of the quotient and adjoin
finitely many generators of the subobject; the resulting sections generate the middle
object.  The local lifting and exactness arguments are those of the dependency nodes
`def-weil-pbc-module-finite-type-presentation`, `def-weil-pbc-exact-sequence`, and the
source's local lifting lemma.
-/
theorem finiteType_image_extension (X : RingedSpace.{u}) :
    (∀ {F G : SheafOfModules.{u} (moduleRings X)} (p : F ⟶ G),
      [Epi p] → [F.IsFiniteType] → G.IsFiniteType) ∧
    (∀ {F H : SheafOfModules.{u} (moduleRings X)} (φ : F ⟶ H),
      [F.IsFiniteType] → (Abelian.image φ).IsFiniteType) ∧
    (∀ (S : ShortComplex (SheafOfModules.{u} (moduleRings X))),
      S.ShortExact → [S.X₁.IsFiniteType] → [S.X₃.IsFiniteType] → S.X₂.IsFiniteType) := by
  refine ⟨fun p _ _ ↦ finiteType_of_epi X p, ?_, ?_⟩
  · intro F H φ hF
    exact finiteType_of_epi X (Abelian.factorThruImage φ)
  · intro S hS h₁ h₃
    classical
    obtain ⟨q₁, hq₁⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData S.X₁
    obtain ⟨q₃, hq₃⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData S.X₃
    have hloc (x : X) : ∃ V : TopologicalSpace.Opens X, x ∈ V ∧
        ∃ σ : (S.X₂.over V).GeneratingSections, σ.IsFiniteType := by
      obtain ⟨W₁, _, ⟨i, ⟨f⟩⟩, hx₁⟩ := q₁.coversTop ⊤ x (by trivial)
      obtain ⟨W₃, _, ⟨j, ⟨g⟩⟩, hx₃⟩ := q₃.coversTop ⊤ x (by trivial)
      have := hq₁.isFiniteType i
      have := hq₃.isFiniteType j
      exact extension_generators_near X S hS (q₁.X i) (q₃.X j)
        (q₁.generators i) (q₃.generators j) x (f.le hx₁) (g.le hx₃)
    choose V hxV σ hσ using hloc
    let q : S.X₂.LocalGeneratorsData :=
      { I := X
        X := V
        coversTop := fun W x hx ↦
          ⟨W ⊓ V x, homOfLE inf_le_left, ⟨x, ⟨homOfLE inf_le_right⟩⟩,
            ⟨hx, hxV x⟩⟩
        generators := σ }
    refine { exists_localGeneratorsData := ⟨q, ?_⟩ }
    exact { isFiniteType := hσ }

end AlgebraicGeometry.RingedSpace

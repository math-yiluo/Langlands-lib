/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.SiteCechComplex
import all WeilConjectures.CategoryTheory.SiteSesCechH1Surjective
import WeilConjectures.Topology.SheafCokernelLocalImage
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Surjectivity of module sections from vanishing Čech H¹

Source: Stacks Project, Cohomology of Sheaves, Lemma 01EU (lemma-ses-cech-h1).
(blueprint: lem-weil-pbc-module-ses-cech-h1-surjective).
-/

@[expose] public section

universe u v w r

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme

private theorem module_local_lifts (X : Scheme.{u}) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (U : Opens X) (s : S.X₃.val.obj (op U)) :
    ∀ x : X, x ∈ U → ∃ (V : Opens X) (hV : V ≤ U), x ∈ V ∧
      ∃ t : S.X₂.val.obj (op V),
        S.g.val.app (op V) t = S.X₃.val.map (homOfLE hV).op s := by
  let q : S.X₃ ⟶
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (cokernel S.g.val) :=
    ⟨cokernel.π S.g.val ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (cokernel S.g.val)⟩
  have hgq : S.g ≫ q = 0 := by
    apply SheafOfModules.Hom.ext
    change S.g.val ≫ (cokernel.π S.g.val ≫ _) = 0
    rw [← Category.assoc, cokernel.condition, zero_comp]
  have := hS.epi_g
  have hq : q = 0 := by
    apply (cancel_epi S.g).mp
    simpa using hgq
  apply (RingedSpace.sheafified_cokernel_local_image X.toRingedSpace S.g q rfl).1 U s |>.mp
  rw [hq]
  rfl

/-- Vanishing Čech H¹ on a cofinal system of open coverings makes sections of a
short exact sequence of `O_X`-modules surjective.
Source: Stacks Project, Cohomology, Tag 01EU.
(blueprint: lem-weil-pbc-module-ses-cech-h1-surjective).
Proof: local lifts are refined to a chosen covering; their differences form a
Čech cocycle in the kernel, which is a coboundary by the vanishing hypothesis.
Subtracting the coboundary makes the lifts compatible, and the sheaf axiom glues
them to a global lift. The empty open is included by the sheaf zero-section axiom.
-/
theorem module_sections_surjective_of_cech_h1_vanishing
    (X : Scheme.{u}) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (U : Opens X)
    (Cov : ∀ (I : Type (max u v)) (V : I → Opens X), (∀ i, V i ≤ U) → Prop)
    (hcover : ∀ (I : Type (max u v)) (V : I → Opens X) (hV : ∀ i, V i ≤ U),
      Cov I V hV → ∀ x, x ∈ U → ∃ i, x ∈ V i)
    (hcofinal : ∀ (I : Type (max u v)) (V : I → Opens X) (_hV : ∀ i, V i ≤ U),
      (∀ x, x ∈ U → ∃ i, x ∈ V i) →
      ∃ (K : Type (max u v)) (W : K → Opens X) (hW : ∀ k, W k ≤ U),
        Cov K W hW ∧ ∀ k, ∃ (i : I), W k ≤ V i)
    (hcech : ∀ (I : Type (max u v)) (V : I → Opens X) (hV : ∀ i, V i ≤ U),
      (hCov : Cov I V hV) →
      ∀ (f : ∀ i, V i ⟶ U),
      ∀ (Scech : SiteCechComplex V f),
        IsZero ((Scech.cohomologyFunctor 1).obj
          ((S.X₁.val.presheaf)))) :
    Function.Surjective (S.g.val.app (op U)) := by
  classical
  intro s
  choose V hV hxV t ht using fun x : U ↦ module_local_lifts X S hS U s x.1 x.2
  let I := ULift.{v} U
  let V' : I → Opens X := fun i ↦ V i.down
  have hV' (i : I) : V' i ≤ U := hV i.down
  obtain ⟨K, W, hW, hCov, href⟩ := hcofinal I V' hV' (fun x hx ↦
    ⟨⟨⟨x, hx⟩⟩, hxV ⟨x, hx⟩⟩)
  let g : ∀ k, W k ⟶ U := fun k ↦ homOfLE (hW k)
  have hlift : ∀ k, ∃ t : S.X₂.val.obj (op (W k)),
      S.g.val.app _ t = S.X₃.val.map (g k).op s := by
    intro k
    obtain ⟨i, hi⟩ := href k
    refine ⟨S.X₂.val.map (homOfLE hi).op (t i.down), ?_⟩
    have hn := ConcreteCategory.congr_hom
      (S.g.val.naturality (homOfLE hi).op) (t i.down)
    change S.g.val.app (op (W k))
      (S.X₂.val.map (homOfLE hi).op (t i.down)) =
        S.X₃.val.map (homOfLE hi).op (S.g.val.app (op (V' i)) (t i.down)) at hn
    rw [hn, ht]
    change S.X₃.val.presheaf.map (homOfLE hi).op
      (S.X₃.val.presheaf.map (homOfLE (hV i.down)).op s) =
        S.X₃.val.presheaf.map (g k).op s
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  choose t ht using hlift
  let T : SiteCechComplex W g :=
    { W := fun p z ↦ ⨅ k : Fin (p + 1), W (z k)
      pr := fun _ z k ↦ homOfLE (iInf_le (fun k ↦ W (z k)) k)
      comm := fun _ _ _ ↦ Subsingleton.elim _ _
      universal := by
        intro p z Z a _
        refine ⟨homOfLE (le_iInf fun k ↦ leOfHom (a k)), ?_, ?_⟩
        · intro k; exact Subsingleton.elim _ _
        · intro b _; exact Subsingleton.elim _ _
      W_zero := by intro z; simp
      pr_zero := fun _ ↦ Subsingleton.elim _ _
      indexMap := fun z α ↦ homOfLE
        (le_iInf fun k ↦ iInf_le (fun k ↦ W (z k)) (α k))
      indexMap_pr := fun _ _ _ ↦ Subsingleton.elim _ _ }
  let : Preadditive (TopCat.Presheaf AddCommGrpCat.{u} X) :=
    inferInstanceAs (Preadditive (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}))
  let : Abelian (TopCat.Presheaf AddCommGrpCat.{u} X) :=
    inferInstanceAs (Abelian (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}))
  let P : X.Modules ⥤ (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) := Modules.toPresheaf X
  let : P.Additive := inferInstanceAs ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj).Additive)
  let : PreservesLimits P := inferInstanceAs (PreservesLimits (Modules.toPresheaf X))
  let A := S.map P
  let a : T.cochains A.X₂ 0 := fun z ↦
    A.X₂.map (T.pr 0 z 0).op (t (z 0))
  have ha (z) : T.cochainsMap A.g 0 a z =
      A.X₃.map (T.pr 0 z 0 ≫ g (z 0)).op s := by
    change A.g.app _ (A.X₂.map _ _) = _
    rw [NatTrans.naturality_apply]
    have htt : A.g.app (op (W (z 0))) (t (z 0)) = A.X₃.map (g (z 0)).op s :=
      ht (z 0)
    rw [htt, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  have hex (Y : X.Opensᵒᵖ) (x : A.X₂.obj Y) (hx : A.g.app Y x = 0) :
      ∃ y, A.f.app Y y = x := by
    have := hS.mono_f
    exact (ShortComplex.ab_exact_iff _).1 (hS.exact.map_of_mono_of_preservesKernel
      (P ⋙ (evaluation _ _).obj Y) inferInstance inferInstance) x hx
  have hinj (Y : X.Opensᵒᵖ) : Function.Injective (A.f.app Y) := by
    have := hS.mono_f
    exact (AddCommGrpCat.mono_iff_injective _).1
      ((P ⋙ (evaluation _ _).obj Y).map_mono S.f)
  have hzero : T.cochainsMap A.g 1 ((T.complex A.X₂).d 0 1 a) = 0 := by
    rw [site_map_d]
    exact site_d_zero_restrict T _ s _ ha
  choose e he using fun z ↦ hex (op (T.W 1 z))
    (((T.complex A.X₂).d 0 1 a) z) (congrFun hzero z)
  have he' : T.cochainsMap A.f 1 e = (T.complex A.X₂).d 0 1 a := funext he
  have hec : (T.complex A.X₁).d 1 2 e = 0 := by
    have h : T.cochainsMap A.f 2 ((T.complex A.X₁).d 1 2 e) = 0 := by
      rw [site_map_d, he']
      exact ConcreteCategory.congr_hom ((T.complex A.X₂).d_comp_d 0 1 2) a
    funext z
    apply hinj _
    change A.f.app _ (((T.complex A.X₁).d 1 2 e) z) = A.f.app _ 0
    rw [map_zero]
    exact congrFun h z
  have hA : (T.complex A.X₁).ExactAt 1 :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ 1).2 (hcech K W hW hCov g T)
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
    ShortComplex.ab_exact_iff] at hA
  obtain ⟨b, hb⟩ := hA e hec
  change (T.complex A.X₁).d 0 1 b = e at hb
  let c : T.cochains A.X₂ 0 := a - T.cochainsMap A.f 0 b
  have hc : (T.complex A.X₂).d 0 1 c = 0 := by
    change (T.complex A.X₂).d 0 1 (a - T.cochainsMap A.f 0 b) = 0
    rw [map_sub, ← site_map_d, hb, he', sub_self]
  have hgcf (Y : X.Opensᵒᵖ) (x : A.X₁.obj Y) : A.g.app Y (A.f.app Y x) = 0 :=
    ConcreteCategory.congr_hom (NatTrans.congr_app A.zero Y) x
  let F₂ : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨A.X₂, S.X₂.isSheaf⟩
  let Q (z : Fin 1 → K) := T.W 0 z
  let q (z : Fin 1 → K) : Q z ⟶ U := T.pr 0 z 0 ≫ g (z 0)
  have hQ : U ≤ ⨆ z, Q z := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover K W hW hCov x hx
    apply Opens.mem_iSup.mpr
    refine ⟨fun _ ↦ i, ?_⟩
    simpa only [Q, T.W_zero] using hi
  have hcompat : TopCat.Presheaf.IsCompatible A.X₂ Q c := by
    intro z z'
    exact site_compatible T _ c hc z z'
      (homOfLE inf_le_left) (homOfLE inf_le_right) (Subsingleton.elim _ _)
  obtain ⟨σ, hσ, -⟩ := F₂.existsUnique_gluing' Q U q hQ c hcompat
  refine ⟨σ, ?_⟩
  apply TopCat.Presheaf.IsSheaf.section_ext S.X₃.isSheaf
  intro x hx
  obtain ⟨i, hi⟩ := hcover K W hW hCov x hx
  let z : Fin 1 → K := fun _ ↦ i
  have hxQ : x ∈ Q z := by simpa only [Q, T.W_zero] using hi
  refine ⟨Q z, leOfHom (q z), hxQ, ?_⟩
  change A.X₃.map (q z).op (A.g.app _ σ) = A.X₃.map (q z).op s
  rw [← NatTrans.naturality_apply]
  erw [hσ z]
  change A.g.app _ (a z - A.f.app _ (b z)) = _
  rw [map_sub, hgcf, sub_zero]
  exact ha z

end AlgebraicGeometry.Scheme

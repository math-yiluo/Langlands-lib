import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomPresheaf
import Langlands.AlgebraicGeometry.Modules.FaithfullyFlatHomDescent
import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing
import Langlands.AlgebraicGeometry.Modules.PullbackQuasicoherent
import Langlands.AlgebraicGeometry.Picard.LineBundleFpqcStackProof

/-! # Descent of all morphisms of actual module sheaves -/

noncomputable section

universe u

open CategoryTheory Opposite Limits Bicategory AlgebraicGeometry
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open Langlands.Scheme.Modules Langlands.Scheme.Modules.LineBundleFlatDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.CoherentSheaves

namespace IntrinsicModuleHomDescent

lemma mapComp'_hom {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (fg : X ⟶ Z) (h : g ≫ f = fg)
    (hp : f.op.toLoc ≫ g.op.toLoc = fg.op.toLoc) (M : Z.Modules) :
    ((intrinsicModulePseudofunctor.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc hp).hom.toNatTrans.app M) =
      (compIso g f fg h M).inv := by
  subst h
  rw [compIso_rfl]
  simp [Pseudofunctor.mapComp', intrinsicModulePseudofunctor,
    Pseudofunctor.comp, Scheme.Modules.pseudofunctor, Adj.forget₁]
  change 𝟙 _ ≫ (Scheme.Modules.pullbackComp g f).inv.app M =
    (Scheme.Modules.pullbackComp g f).inv.app M
  exact Category.id_comp _

set_option maxHeartbeats 800000 in
lemma mapComp'_inv {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (fg : X ⟶ Z) (h : g ≫ f = fg)
    (hp : f.op.toLoc ≫ g.op.toLoc = fg.op.toLoc) (M : Z.Modules) :
    ((intrinsicModulePseudofunctor.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc hp).inv.toNatTrans.app M) =
      (compIso g f fg h M).hom := by
  rw [← cancel_mono (compIso g f fg h M).inv]
  conv_lhs => rw [← mapComp'_hom g f fg h hp M]
  rw [Cat.Hom.inv_hom_id_toNatTrans_app]
  exact (Iso.hom_inv_id _).symm

lemma toDescentData_obj_hom {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (M : S.Modules) {Y : Scheme.{u}} (q : Y ⟶ S)
    {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ((intrinsicModulePseudofunctor.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ =
      (compIso f₁ (f i₁) q hf₁ M).hom ≫ (compIso f₂ (f i₂) q hf₂ M).inv := by
  dsimp only [Pseudofunctor.toDescentData]
  rw [Pseudofunctor.DescentData.ofObj_hom, mapComp'_inv, mapComp'_hom]

lemma modCompat {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) {M N : S.Modules}
    (φ : (intrinsicModulePseudofunctor.toDescentData f).obj M ⟶
      (intrinsicModulePseudofunctor.toDescentData f).obj N) :
    Picard.ModCompat f M N φ.hom := by
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  have h := φ.comm q f₁ f₂ hf₁ hf₂
  rw [toDescentData_obj_hom, toDescentData_obj_hom] at h
  exact h

/-- Unique gluing of compatible actual maps gives bijectivity on descent morphisms. -/
lemma bijective_toDescentData_map_of_unique {S : Scheme.{u}} {ι : Type*}
    {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) (M N : S.Modules)
    (H : ∀ (φ : (intrinsicModulePseudofunctor.toDescentData f).obj M ⟶
        (intrinsicModulePseudofunctor.toDescentData f).obj N),
      ∃! b : M ⟶ N, ∀ i, (Scheme.Modules.pullback (f i)).map b = φ.hom i) :
    Function.Bijective
      ((intrinsicModulePseudofunctor.toDescentData f).map : (M ⟶ N) → _) := by
  rw [Function.bijective_iff_existsUnique]
  intro φ
  obtain ⟨b, hb, hu⟩ := H φ
  refine ⟨b, ?_, fun c hc ↦ hu c fun i ↦ ?_⟩
  · ext i
    exact hb i
  · exact congrArg (fun ψ ↦ ψ.hom i) hc

/-- All module morphisms descend over open covers. -/
lemma bijective_toDescentData_map_openCover {S : Scheme.{u}} (𝒰 : S.OpenCover.{u})
    (M N : S.Modules) :
    Function.Bijective
      ((intrinsicModulePseudofunctor.toDescentData 𝒰.f).map : (M ⟶ N) → _) := by
  apply bijective_toDescentData_map_of_unique 𝒰.f M N
  intro φ
  apply OpenCoverHomGluing.openCoverHomGluing S 𝒰 M N φ.hom
  intro i j
  rw [Picard.squarePullbackIso_hom_eq _ _ _ _ _ (pullback.fst _ _ ≫ 𝒰.f i)
      rfl pullback.condition.symm,
    Picard.squarePullbackIso_hom_eq _ _ _ _ _ (pullback.fst _ _ ≫ 𝒰.f i)
      rfl pullback.condition.symm]
  exact modCompat 𝒰.f φ (pullback.fst _ _ ≫ 𝒰.f i)
    (pullback.fst _ _) (pullback.snd _ _) rfl pullback.condition.symm

lemma isPrestackFor_openCover {S : Scheme.{u}} (𝒰 : S.OpenCover.{u}) :
    intrinsicModulePseudofunctor.IsPrestackFor (Presieve.ofArrows 𝒰.X 𝒰.f) := by
  rw [Pseudofunctor.isPrestackFor_ofArrows_iff,
    Functor.FullyFaithful.nonempty_iff_map_bijective]
  exact bijective_toDescentData_map_openCover 𝒰

/-- The pseudofunctor of all modules is a Zariski prestack. -/
instance isPrestack_zariski :
    intrinsicModulePseudofunctor.{u}.IsPrestack Scheme.zariskiTopology :=
  Langlands.StackComposite.isPrestack_of_small.{u} _ fun _ 𝒰 ↦ isPrestackFor_openCover 𝒰

/-- With quasi-coherent target, actual Hom descends along affine faithfully flat maps. -/
lemma bijective_toDescentData_map_singleton {X S : Scheme.{u}} (p : X ⟶ S)
    [IsAffineHom p] [Flat p] [Surjective p] (M N : S.Modules) [N.IsQuasicoherent] :
    Function.Bijective
      ((intrinsicModulePseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ p)).map :
        (M ⟶ N) → _) := by
  apply bijective_toDescentData_map_of_unique (fun _ : PUnit.{1} ↦ p) M N
  intro φ
  obtain ⟨b, hb, hu⟩ := Modules.FaithfullyFlatHomDescent.existsUnique_hom p
    (φ.hom PUnit.unit) (fun U s t h ↦ by
      rw [equalCompositeIso_hom_eq_compIso p s t h (s ≫ p) rfl h.symm,
        equalCompositeIso_hom_eq_compIso p s t h (s ≫ p) rfl h.symm]
      exact modCompat (fun _ : PUnit.{1} ↦ p) φ (s ≫ p)
        (i₁ := PUnit.unit) (i₂ := PUnit.unit) s t rfl h.symm)
  exact ⟨b, fun i ↦ by cases i; exact hb, fun c hc ↦ hu c (hc PUnit.unit)⟩

/-- Affine faithfully flat Hom descent holds over every object of the full slice. -/
lemma isSheafFor_singleton_over {X S Y : Scheme.{u}} (p : X ⟶ S)
    [IsAffineHom p] [Flat p] [Surjective p] (M N : Y.Modules) [N.IsQuasicoherent]
    (s : S ⟶ Y) :
    Presieve.IsSheafFor (intrinsicModulePseudofunctor.presheafHom M N)
      (.singleton (Over.homMk p : Over.mk (p ≫ s) ⟶ Over.mk s)) := by
  have h := (Pseudofunctor.bijective_toDescentData_map_iff
      (F := intrinsicModulePseudofunctor) (fun _ : PUnit.{1} ↦ p)
      ((Scheme.Modules.pullback s).obj M) ((Scheme.Modules.pullback s).obj N)).1
    (bijective_toDescentData_map_singleton p
      ((Scheme.Modules.pullback s).obj M) ((Scheme.Modules.pullback s).obj N))
  have h' := (Presieve.isSheafFor_iff_of_iso
    (intrinsicModulePseudofunctor.overMapCompPresheafHomIso M N s)).2 h
  rw [Presieve.isSheafFor_over_map_op_comp_ofArrows_iff,
    Presieve.ofArrows_of_unique] at h'
  convert! h' using 1

/-- For an arbitrary source and quasi-coherent target, all actual module Hom is an fpqc
sheaf on the full scheme slice. -/
theorem isSheaf_presheafHom_fpqc {Y : Scheme.{u}} (M N : Y.Modules)
    [N.IsQuasicoherent] :
    Presieve.IsSheaf (Scheme.fpqcTopology.over Y)
      (intrinsicModulePseudofunctor.presheafHom M N) := by
  apply Picard.isSheaf_fpqcTopology_over
  · exact (isSheaf_iff_isSheaf_of_type _ _).1
      (Pseudofunctor.IsPrestack.isSheaf (F := intrinsicModulePseudofunctor)
        Scheme.zariskiTopology M N)
  · intro R R' φ hf hs s
    have : Flat (Spec.map φ) := hf
    have : Surjective (Spec.map φ) := hs
    exact isSheafFor_singleton_over (Spec.map φ) M N s

end IntrinsicModuleHomDescent

/-- The ordinary-pullback relative Hom presheaf is an fpqc sheaf whenever its target is
quasi-coherent. -/
theorem isSheaf_intrinsicModuleHomPresheaf_fpqc {B Y : Scheme.{u}} (p : Y ⟶ B)
    (M N : Y.Modules) [N.IsQuasicoherent] :
    Presieve.IsSheaf (Scheme.fpqcTopology.over B) (intrinsicModuleHomPresheaf p M N) := by
  exact (Over.pullback p).op_comp_isSheaf_of_isSheaf_type _
    (Presieve.isSheaf_comp_uliftFunctor _
      (IntrinsicModuleHomDescent.isSheaf_presheafHom_fpqc M N))

/-- The same actual relative Hom presheaf is a sheaf for the fppf topology. -/
theorem isSheaf_intrinsicModuleHomPresheaf_fppf {B Y : Scheme.{u}} (p : Y ⟶ B)
    (M N : Y.Modules) [N.IsQuasicoherent] :
    Presieve.IsSheaf (Scheme.fppfTopology.over B) (intrinsicModuleHomPresheaf p M N) := by
  apply Presieve.isSheaf_of_le _ ?_ (isSheaf_intrinsicModuleHomPresheaf_fpqc p M N)
  intro U R hR
  exact Scheme.fppfTopology_le_fpqcTopology _ hR

/-- The fppf sheaf of all actual module maps after ordinary relative base change. -/
def intrinsicModuleHomSheaf {B Y : Scheme.{u}} (p : Y ⟶ B)
    (M N : Y.Modules) [N.IsQuasicoherent] :
    Sheaf (Scheme.fppfTopology.over B) (Type (u + 1)) :=
  ⟨intrinsicModuleHomPresheaf p M N,
    (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_intrinsicModuleHomPresheaf_fppf p M N)⟩

end Langlands.AlgebraicGeometry.CoherentSheaves

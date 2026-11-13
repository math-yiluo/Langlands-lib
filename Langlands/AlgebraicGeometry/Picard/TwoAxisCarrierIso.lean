import Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedClassPresheaf
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso
import Langlands.AlgebraicGeometry.Modules.StructureUnitScalars
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # Two-axis rigidified bundles with isomorphic carriers -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

variable {S X Z : Scheme.{u}}

/-- Pulling back the discrepancy of two axis trivializations along a section is the
discrepancy of their restrictions. -/
lemma structureAutPullback_axis (s : S ⟶ X) (k : X ⟶ Z) {N N' : Z.Modules}
    (α : structureSheaf X ≅ (Scheme.Modules.pullback k).obj N)
    (α' : structureSheaf X ≅ (Scheme.Modules.pullback k).obj N') (g : N ≅ N') :
    structureAutPullback s (α ≪≫ (Scheme.Modules.pullback k).mapIso g ≪≫ α'.symm) =
      axisRestrictionIso s k N α ≪≫ (Scheme.Modules.pullback (s ≫ k)).mapIso g ≪≫
        (axisRestrictionIso s k N' α').symm := by
  apply Iso.ext
  simp only [structureAutPullback_hom, axisRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv, Functor.map_comp,
    Category.assoc]
  congr 2
  have hn : ((Scheme.Modules.pullbackComp s k).app N).hom ≫
      (Scheme.Modules.pullback (s ≫ k)).map g.hom =
      (Scheme.Modules.pullback s).map ((Scheme.Modules.pullback k).map g.hom) ≫
        ((Scheme.Modules.pullbackComp s k).app N').hom :=
    ((Scheme.Modules.pullbackComp s k).hom.naturality g.hom).symm
  rw [reassoc_of% hn]
  simp

/-- Pulling back the identity automorphism of the structure sheaf gives the identity. -/
@[simp]
lemma structureAutPullback_refl (s : S ⟶ X) :
    structureAutPullback s (Iso.refl (structureModule X)) = Iso.refl _ := by
  apply structureAutScalar_injective
  rw [structureAutScalar_pullback, structureAutScalar_refl, map_one, structureAutScalar_refl]

/-- An automorphism of the structure sheaf of a scheme with a section and with base
global functions is the identity when its restriction along the section is. -/
lemma structureAut_eq_refl_of_section {Y : Scheme.{u}} (q : Y ⟶ S) (t : S ⟶ Y)
    (ht : t ≫ q = 𝟙 S) (hq : IsIso (q.app ⊤))
    (δ : structureModule Y ≅ structureModule Y)
    (hδ : structureAutPullback t δ = Iso.refl _) : δ = Iso.refl _ := by
  apply structureAutScalar_injective
  rw [structureAutScalar_refl]
  have h1 := structureAutScalar_pullback t δ
  rw [hδ, structureAutScalar_refl] at h1
  have hsurj : Function.Surjective q.appTop :=
    (ConcreteCategory.bijective_of_isIso (q.app ⊤)).2
  have hret : ∀ y, t.appTop (q.appTop y) = y := by
    intro y
    have h := Scheme.Hom.comp_appTop t q
    rw [ht] at h
    have h' := congrArg (fun φ ↦ φ y) (congrArg (fun ψ ↦ ψ.hom) h)
    simpa using h'.symm
  have hinj : Function.Injective t.appTop := by
    intro x x' hx
    obtain ⟨y, rfl⟩ := hsurj x
    obtain ⟨y', rfl⟩ := hsurj x'
    rw [hret, hret] at hx
    rw [hx]
  apply Units.ext
  apply hinj
  have h2 := congrArg (fun r : Γ(S, ⊤)ˣ ↦ (r : Γ(S, ⊤))) h1
  simp only [Units.val_one, Units.coe_map] at h2
  rw [Units.val_one, map_one]
  exact h2.symm

/-- The same identity statement, phrased for the Library's structure-sheaf module. -/
lemma structureAutPullback_refl_structureSheaf (s : S ⟶ X) :
    structureAutPullback s (Iso.refl (structureSheaf X)) = Iso.refl _ :=
  structureAutPullback_refl s

section General

variable {Y : Scheme.{u}} {e : S ⟶ X} {t : S ⟶ Y} {i : X ⟶ Z} {j : Y ⟶ Z}
  {h : e ≫ i = t ≫ j} {N N' : Z.Modules}

/-- If an isomorphism of carriers respects the first axis trivializations of two
compatible two-axis rigidifications, the discrepancy on the second axis restricts to
the identity on the common base. -/
lemma secondDiscrepancy_restrict_refl (ρ : TwoAxisRigidification e t i j h N)
    (ρ' : TwoAxisRigidification e t i j h N') (g : N ≅ N')
    (hfirst : ρ.first.hom ≫ (Scheme.Modules.pullback i).map g.hom = ρ'.first.hom) :
    structureAutPullback t (ρ.second ≪≫ (Scheme.Modules.pullback j).mapIso g ≪≫
      ρ'.second.symm) = Iso.refl _ := by
  have h1 : ρ.first ≪≫ (Scheme.Modules.pullback i).mapIso g ≪≫ ρ'.first.symm =
      Iso.refl _ := by
    apply Iso.ext
    change (ρ.first.hom ≫ (Scheme.Modules.pullback i).map g.hom) ≫ ρ'.first.inv = 𝟙 _
    rw [hfirst, Iso.hom_inv_id]
  have h2 := structureAutPullback_axis e i ρ.first ρ'.first g
  rw [h1, structureAutPullback_refl_structureSheaf] at h2
  rw [structureAutPullback_axis, ← ρ.compatible, ← ρ'.compatible]
  have hn : (Scheme.Modules.pullback (e ≫ i)).map g.hom ≫
      ((Scheme.Modules.pullbackCongr h).app N').hom =
        ((Scheme.Modules.pullbackCongr h).app N).hom ≫
          (Scheme.Modules.pullback (t ≫ j)).map g.hom :=
    (Scheme.Modules.pullbackCongr h).hom.naturality g.hom
  have h3 : (axisRestrictionIso e i N ρ.first ≪≫ (Scheme.Modules.pullbackCongr h).app N) ≪≫
      (Scheme.Modules.pullback (t ≫ j)).mapIso g ≪≫
        (axisRestrictionIso e i N' ρ'.first ≪≫ (Scheme.Modules.pullbackCongr h).app N').symm =
      axisRestrictionIso e i N ρ.first ≪≫ (Scheme.Modules.pullback (e ≫ i)).mapIso g ≪≫
        (axisRestrictionIso e i N' ρ'.first).symm := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom,
      Category.assoc]
    congr 1
    rw [← reassoc_of% hn]
    simp
  rw [h3, ← h2]

end General

end Langlands.AlgebraicGeometry.Picard

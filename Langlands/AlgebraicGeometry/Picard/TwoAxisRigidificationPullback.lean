import Langlands.AlgebraicGeometry.Picard.TwoAxisRigidification
import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackProofs
import Langlands.AlgebraicGeometry.Picard.RigidifiedTrivialPullback

/-! # Pullback of compatible two-axis rigidifications -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.SchemeModule.RigidifiedModule

namespace TwoAxisRigidification

variable {S X Y Z S' X' Y' Z' : Scheme.{u}}

/-- Restriction to a named composite, including its canonical comparison. -/
def restrictionHom (e : S ⟶ X) (i : X ⟶ Z) (c : S ⟶ Z) (hc : e ≫ i = c)
    (M : Z.Modules) (α : structureSheaf X ≅ (Scheme.Modules.pullback i).obj M) :
    structureSheaf S ⟶ (Scheme.Modules.pullback c).obj M :=
  (pullbackUnitIso e).inv ≫ (Scheme.Modules.pullback e).map α.hom ≫
    compHom e i c hc M

set_option backward.isDefEq.respectTransparency false in
lemma pullback_rigidification_compHom
    {i : X ⟶ Z} {i' : X' ⟶ Z'} (fz : Z' ⟶ Z) (fx : X' ⟶ X)
    (hi : i' ≫ fz = fx ≫ i) (M : RigidifiedModule i) :
    ((RigidifiedModule.pullback fz fx hi).obj M).rigidification.hom ≫
        compHom i' fz (fx ≫ i) hi M.carrier =
      (pullbackUnitIso fx).inv ≫ (Scheme.Modules.pullback fx).map M.rigidification.hom ≫
        compHom fx i (fx ≫ i) rfl M.carrier := by
  change ((pullbackUnitIso fx).inv ≫ (Scheme.Modules.pullback fx).map M.rigidification.hom ≫
      ((Scheme.Modules.pullbackComp fx i).hom.app M.carrier ≫
        (Scheme.Modules.pullbackCongr hi.symm).hom.app M.carrier ≫
          (Scheme.Modules.pullbackComp i' fz).inv.app M.carrier)) ≫ _ = _
  simp [compHom, Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a pulled-back axis trivialization is compatible with base pullback. -/
lemma restrictionHom_pullback
    (e : S ⟶ X) (i : X ⟶ Z) (c : S ⟶ Z) (h : e ≫ i = c)
    (e' : S' ⟶ X') (i' : X' ⟶ Z') (c' : S' ⟶ Z') (h' : e' ≫ i' = c')
    (fz : Z' ⟶ Z) (fx : X' ⟶ X) (fs : S' ⟶ S)
    (hi : i' ≫ fz = fx ≫ i) (he : e' ≫ fx = fs ≫ e)
    (hc : c' ≫ fz = fs ≫ c) (M : Z.Modules)
    (α : structureSheaf X ≅ (Scheme.Modules.pullback i).obj M) :
    restrictionHom e' i' c' h' ((Scheme.Modules.pullback fz).obj M)
        ((RigidifiedModule.pullback fz fx hi).obj ⟨M, α⟩).rigidification ≫
        compHom c' fz (fs ≫ c) hc M =
      (pullbackUnitIso fs).inv ≫
        (Scheme.Modules.pullback fs).map (restrictionHom e i c h M α) ≫
          compHom fs c (fs ≫ c) rfl M := by
  have hE : e' ≫ (fx ≫ i) = fs ≫ c := by
    rw [← Category.assoc, he, Category.assoc, h]
  have hE' : (fs ≫ e) ≫ i = fs ≫ c := by rw [Category.assoc, h]
  have e1 := compHom_assoc e' i' fz c' (fx ≫ i) (fs ≫ c) h' hi hc hE M
  have e2 := compHom_assoc e' fx i (fs ≫ e) (fx ≫ i) (fs ≫ c) he rfl hE' hE M
  have e3 := compHom_assoc fs e i (fs ≫ e) c (fs ≫ c) rfl h hE' rfl M
  simp only [restrictionHom, Category.assoc]
  rw [e1,
    ← Functor.map_comp_assoc, pullback_rigidification_compHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← e2, ← e3, ← Langlands.Scheme.Modules.compHom_naturality_assoc,
    ← Langlands.Scheme.Modules.compHom_naturality_assoc]
  rw [reassoc_of% pullbackUnitIso_inv_compHom e' fx (fs ≫ e) he,
    reassoc_of% pullbackUnitIso_inv_compHom fs e (fs ≫ e) rfl]

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility expressed as equality of restriction morphisms to one named composite. -/
lemma compatible_iff_restrictionHom
    (e : S ⟶ X) (t : S ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (h : e ≫ i = t ≫ j) (M : Z.Modules)
    (α : structureSheaf X ≅ (Scheme.Modules.pullback i).obj M)
    (β : structureSheaf Y ≅ (Scheme.Modules.pullback j).obj M) :
    axisRestrictionIso e i M α ≪≫ (Scheme.Modules.pullbackCongr h).app M =
        axisRestrictionIso t j M β ↔
      restrictionHom e i (t ≫ j) h M α = restrictionHom t j (t ≫ j) rfl M β := by
  constructor
  · intro hc
    simpa [restrictionHom, axisRestrictionIso, compHom, Scheme.Modules.pullbackCongr,
      Category.assoc] using congrArg Iso.hom hc
  · intro hc
    apply Iso.ext
    simpa [restrictionHom, axisRestrictionIso, compHom, Scheme.Modules.pullbackCongr,
      Category.assoc] using hc

set_option backward.isDefEq.respectTransparency false in
/-- Canonical pullback of two compatible axis rigidifications across a map of diagrams. -/
def pullback
    {e : S ⟶ X} {t : S ⟶ Y} {i : X ⟶ Z} {j : Y ⟶ Z}
    {h : e ≫ i = t ≫ j}
    {e' : S' ⟶ X'} {t' : S' ⟶ Y'} {i' : X' ⟶ Z'} {j' : Y' ⟶ Z'}
    {h' : e' ≫ i' = t' ≫ j'}
    (fz : Z' ⟶ Z) (fx : X' ⟶ X) (fy : Y' ⟶ Y) (fs : S' ⟶ S)
    (hi : i' ≫ fz = fx ≫ i) (hj : j' ≫ fz = fy ≫ j)
    (he : e' ≫ fx = fs ≫ e) (ht : t' ≫ fy = fs ≫ t)
    {M : Z.Modules} (ρ : TwoAxisRigidification e t i j h M) :
    TwoAxisRigidification e' t' i' j' h' ((Scheme.Modules.pullback fz).obj M) := by
  let α := ((RigidifiedModule.pullback fz fx hi).obj ⟨M, ρ.first⟩).rigidification
  let β := ((RigidifiedModule.pullback fz fy hj).obj ⟨M, ρ.second⟩).rigidification
  refine ⟨α, β, ?_⟩
  apply (compatible_iff_restrictionHom e' t' i' j' h' _ α β).mpr
  have hc : (t' ≫ j') ≫ fz = fs ≫ (t ≫ j) := by
    rw [Category.assoc, hj, ← Category.assoc, ht, Category.assoc]
  have hρ := (compatible_iff_restrictionHom e t i j h M ρ.first ρ.second).mp ρ.compatible
  rw [← cancel_mono (compHom (t' ≫ j') fz (fs ≫ (t ≫ j)) hc M)]
  dsimp only [α, β]
  calc
    _ = (pullbackUnitIso fs).inv ≫
        (Scheme.Modules.pullback fs).map (restrictionHom e i (t ≫ j) h M ρ.first) ≫
          compHom fs (t ≫ j) (fs ≫ (t ≫ j)) rfl M :=
      restrictionHom_pullback e i (t ≫ j) h e' i' (t' ≫ j') h'
        fz fx fs hi he hc M ρ.first
    _ = (pullbackUnitIso fs).inv ≫
        (Scheme.Modules.pullback fs).map (restrictionHom t j (t ≫ j) rfl M ρ.second) ≫
          compHom fs (t ≫ j) (fs ≫ (t ≫ j)) rfl M := by rw [hρ]
    _ = _ := (restrictionHom_pullback t j (t ≫ j) rfl t' j' (t' ≫ j') rfl
      fz fy fs hj ht hc M ρ.second).symm

end TwoAxisRigidification

end Langlands.AlgebraicGeometry.Picard

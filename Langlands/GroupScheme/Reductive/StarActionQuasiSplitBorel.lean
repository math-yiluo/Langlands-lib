import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Absolute.BorelFieldExtensionFields
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.FieldTheory.IsSepClosed

/-! # A geometric Borel stays Borel over the separable closure -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

namespace StarActionQuasiSplit

variable {k : Type u} [Field k] {B G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- The base change from `k` to `AlgebraicClosure k` factors through `SeparableClosure k`. -/
theorem separableClosure_comp_eq :
    Spec.map (CommRingCat.ofHom (algebraMap (SeparableClosure k) (AlgebraicClosure k))) ≫
        algebraBaseMap k (SeparableClosure k) = toAlgebraicClosure k := by
  dsimp [algebraBaseMap, toAlgebraicClosure]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq k (SeparableClosure k) (AlgebraicClosure k)]

/-- A geometric Borel subgroup over `k` remains a Borel subgroup over the separable closure. -/
theorem isBorelSubgroup_separableClosure {b : B ⟶ G} (hb : IsGeometricBorelSubgroup b) :
    IsBorelSubgroup ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map b) := by
  let s := algebraBaseMap k (SeparableClosure k)
  let a := toAlgebraicClosure k
  let c : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶
      Spec (CommRingCat.of (SeparableClosure k)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (SeparableClosure k) (AlgebraicClosure k)))
  have hc : c ≫ s = a := separableClosure_comp_eq
  have : IsAffineHom ((GroupScheme.baseChange s).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom s)
    infer_instance
  refine BorelFieldExtension.isBorelSubgroup_baseChange_of_maximal s hb.1 ?_
  intro B' i' f hi' hsm hconn hsolv hf
  have : IsAffineHom B'.X.hom := BorelFieldExtension.isAffineHom_source hi'
  have : Smooth B'.X.hom := hsm
  have : ConnectedSpace B'.X.left := hconn
  obtain ⟨hcSurj, hcFlat, hcQC⟩ := fieldExtension_fpqc (SeparableClosure k) (AlgebraicClosure k)
  let : Surjective c := hcSurj
  let : Flat c := hcFlat
  let : QuasiCompact c := hcQC
  let eB := Descent.pullbackComparison s c a hc B
  let eG := Descent.pullbackComparison s c a hc G
  let F : (GroupScheme.baseChange a).obj B ⟶ (GroupScheme.baseChange c).obj B' :=
    eB.inv ≫ (GroupScheme.baseChange c).map f
  let I : (GroupScheme.baseChange c).obj B' ⟶ (GroupScheme.baseChange a).obj G :=
    (GroupScheme.baseChange c).map i' ≫ eG.hom
  have hFI : F ≫ I = (GroupScheme.baseChange a).map b := by
    simp only [F, I, Category.assoc]
    rw [← Functor.map_comp_assoc, hf, Descent.pullbackComparison_naturality,
      Iso.inv_hom_id_assoc]
  have hI : IsClosedSubgroup I := (hi'.baseChange c).comp_iso eG
  have hsmc : Smooth ((GroupScheme.baseChange c).obj B').X.hom := by
    change Smooth (pullback.snd B'.X.hom c)
    infer_instance
  have hconnc : ConnectedSpace ((GroupScheme.baseChange c).obj B').X.left :=
    connectedSpace_baseChange_of_smooth_affine B' c
  have hsolvc : IsSolvableGroupScheme ((GroupScheme.baseChange c).obj B') :=
    solvableFieldExtensionStatement (SeparableClosure k) (AlgebraicClosure k) c B' hsm hsolv
  have hF : IsIso F := hb.2.maximal _ I F hI hsmc hconnc hsolvc hFI
  have hfc : IsIso ((GroupScheme.baseChange c).map f) := by
    have : (GroupScheme.baseChange c).map f = eB.hom ≫ F := by
      simp only [F, Iso.hom_inv_id_assoc]
    rw [this]
    infer_instance
  exact isIso_of_baseChange c f

end StarActionQuasiSplit

end Langlands.GroupScheme

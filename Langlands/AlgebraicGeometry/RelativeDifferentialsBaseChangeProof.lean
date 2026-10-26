import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChangeStatement
import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChangeTransport

/-! # Global differential base-change reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace Langlands.Scheme

private lemma baseChange_isIso_pullback_of_isIso
    (hopen : RelativeDifferentialsOpenImmersionIsIsoStatement.{u})
    {X₀ X S₀ S T₀ T : AlgebraicGeometry.Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (b₀ : T₀ ⟶ S₀) (f : X ⟶ S) (b : T ⟶ S)
    (i : X₀ ⟶ X) (j : T₀ ⟶ T) (k : S₀ ⟶ S)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion k]
    (wf : i ≫ f = f₀ ≫ k) (wb : j ≫ b = b₀ ≫ k)
    [IsIso (relativeDifferentialsBaseChangeMap f₀ b₀)] :
    IsIso ((pullback (Limits.pullback.map f₀ b₀ f b i j k wf.symm wb.symm)).map
      (relativeDifferentialsBaseChangeMap f b)) := by
  let l := Limits.pullback.map f₀ b₀ f b i j k wf.symm wb.symm
  let p₀ := Limits.pullback.fst f₀ b₀
  let q₀ := Limits.pullback.snd f₀ b₀
  let p := Limits.pullback.fst f b
  let q := Limits.pullback.snd f b
  have wl : l ≫ q = q₀ ≫ j := Limits.pullback.lift_snd ..
  have wp : l ≫ p = p₀ ≫ i := Limits.pullback.lift_fst ..
  have : IsIso (relativeDifferentialsSquareMap i k wf) :=
    hopen _ _ _ _ f f₀ i k inferInstance inferInstance wf
  have : IsIso (relativeDifferentialsSquareMap l j wl) :=
    hopen _ _ _ _ q q₀ l j inferInstance inferInstance wl
  have hleft := relativeDifferentialsSquareMap_comp l p j b wl Limits.pullback.condition
  have hright := relativeDifferentialsSquareMap_comp p₀ i b₀ k Limits.pullback.condition wf
  have hcongr := relativeDifferentialsSquareMap_congr wp wb
    (by rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, wl, Category.assoc])
    (by rw [Category.assoc, wf, ← Category.assoc, Limits.pullback.condition, Category.assoc])
  have heq :
      (pullback l).map (relativeDifferentialsBaseChangeMap f b) ≫
          relativeDifferentialsSquareMap l j wl =
        (pullbackComp l p).hom.app (relativeDifferentials f) ≫
          (pullbackCongr wp).hom.app (relativeDifferentials f) ≫
          (pullbackComp p₀ i).inv.app (relativeDifferentials f) ≫
          (pullback p₀).map (relativeDifferentialsSquareMap i k wf) ≫
          relativeDifferentialsBaseChangeMap f₀ b₀ := by
    apply (cancel_epi ((pullbackComp l p).inv.app (relativeDifferentials f))).mp
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    simp only [Category.assoc, relativeDifferentialsBaseChangeMap]
    rw [hleft, hright, hcongr]
  have : IsIso ((pullback l).map (relativeDifferentialsBaseChangeMap f b) ≫
      relativeDifferentialsSquareMap l j wl) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (relativeDifferentialsSquareMap l j wl)

private lemma baseChange_isIso_of_affine
    (hopen : RelativeDifferentialsOpenImmersionIsIsoStatement.{u})
    (hspec : ∀ (R A B : CommRingCat.{u}) (f : R ⟶ A) (b : R ⟶ B),
      IsIso (relativeDifferentialsBaseChangeMap (Spec.map f) (Spec.map b)))
    {X S T : AlgebraicGeometry.Scheme.{u}} [IsAffine X] [IsAffine S] [IsAffine T]
    (f : X ⟶ S) (b : T ⟶ S) : IsIso (relativeDifferentialsBaseChangeMap f b) := by
  let f₀ := Spec.map f.appTop
  let b₀ := Spec.map b.appTop
  have wf : X.isoSpec.inv ≫ f = f₀ ≫ S.isoSpec.inv :=
    (AlgebraicGeometry.Scheme.isoSpec_inv_naturality f).symm
  have wb : T.isoSpec.inv ≫ b = b₀ ≫ S.isoSpec.inv :=
    (AlgebraicGeometry.Scheme.isoSpec_inv_naturality b).symm
  let l := Limits.pullback.map f₀ b₀ f b X.isoSpec.inv T.isoSpec.inv S.isoSpec.inv
    wf.symm wb.symm
  have : IsIso (relativeDifferentialsBaseChangeMap f₀ b₀) :=
    hspec _ _ _ f.appTop b.appTop
  have h : IsIso ((pullback l).map (relativeDifferentialsBaseChangeMap f b)) :=
    baseChange_isIso_pullback_of_isIso hopen f₀ b₀ f b
      X.isoSpec.inv T.isoSpec.inv S.isoSpec.inv wf wb
  exact relativeDifferentials_isIso_of_openCover_pullback (AlgebraicGeometry.Scheme.coverOfIsIso.{0} l) _
    (fun _ => h)

private lemma baseChange_isIso_of_affineBase
    (hopen : RelativeDifferentialsOpenImmersionIsIsoStatement.{u})
    (hspec : ∀ (R A B : CommRingCat.{u}) (f : R ⟶ A) (b : R ⟶ B),
      IsIso (relativeDifferentialsBaseChangeMap (Spec.map f) (Spec.map b)))
    {X S T : AlgebraicGeometry.Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) (b : T ⟶ S) : IsIso (relativeDifferentialsBaseChangeMap f b) := by
  apply relativeDifferentials_isIso_of_openCover_pullback
    (AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight X.affineCover T.affineCover f b)
  intro ij
  have : IsIso (relativeDifferentialsBaseChangeMap
      (X.affineCover.f ij.1 ≫ f) (T.affineCover.f ij.2 ≫ b)) :=
    baseChange_isIso_of_affine hopen hspec _ _
  exact baseChange_isIso_pullback_of_isIso hopen
    (X.affineCover.f ij.1 ≫ f) (T.affineCover.f ij.2 ≫ b) f b
    (X.affineCover.f ij.1) (T.affineCover.f ij.2) (𝟙 S) (by simp) (by simp)

lemma relativeDifferentialsBaseChangeIsIso_of_local_inputs
    (hopen : RelativeDifferentialsOpenImmersionIsIsoStatement.{u})
    (hspec : ∀ (R A B : CommRingCat.{u}) (f : R ⟶ A) (b : R ⟶ B),
      IsIso (relativeDifferentialsBaseChangeMap (Spec.map f) (Spec.map b)))
    (S : AlgebraicGeometry.Scheme.{u}) : RelativeDifferentialsBaseChangeIsIsoStatement S := by
  intro X T f b
  apply relativeDifferentials_isIso_of_openCover_pullback
    (AlgebraicGeometry.Scheme.Pullback.openCoverOfBase S.affineCover f b)
  intro i
  change S.affineCover.I₀ at i
  have : IsAffine (S.affineCover.X i) :=
    AlgebraicGeometry.Scheme.isAffine_affineCover S i
  have : IsOpenImmersion (S.affineCover.f i) := S.affineCover.map_prop i
  have : IsIso (relativeDifferentialsBaseChangeMap
      (Limits.pullback.snd f (S.affineCover.f i))
      (Limits.pullback.snd b (S.affineCover.f i))) :=
    baseChange_isIso_of_affineBase hopen hspec _ _
  exact baseChange_isIso_pullback_of_isIso hopen
    (Limits.pullback.snd f (S.affineCover.f i))
    (Limits.pullback.snd b (S.affineCover.f i)) f b
    (Limits.pullback.fst f (S.affineCover.f i))
    (Limits.pullback.fst b (S.affineCover.f i)) (S.affineCover.f i)
    Limits.pullback.condition Limits.pullback.condition

end Langlands.Scheme

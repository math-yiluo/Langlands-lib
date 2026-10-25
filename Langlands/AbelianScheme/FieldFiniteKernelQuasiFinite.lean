import Langlands.AbelianScheme.FieldFiniteKernelQuasiFiniteStatement
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AbelianScheme.KernelFiberTranslation

/-! # Finite kernels give locally quasi-finite group morphisms over fields -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace Langlands.GroupScheme

/-- Kernel finiteness survives arbitrary base change. -/
private lemma finite_kernel_baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    {G H : Grp (Over S)} (f : G ⟶ H) [IsFinite (kernel f).X.hom] :
    IsFinite (kernel ((Over.pullback b).mapGrp.map f)).X.hom := by
  let e := (Grp.forget (Over T)).mapIso (kernelBaseChangeIso b f)
  have h : IsFinite (((Over.pullback b).mapGrp.obj (kernel f)).X.hom) :=
    inferInstanceAs (IsFinite (pullback.snd (kernel f).X.hom b))
  have he : e.inv.left ≫ (((Over.pullback b).mapGrp.obj (kernel f)).X.hom) =
      (kernel ((Over.pullback b).mapGrp.map f)).X.hom := e.inv.w
  rw [← he]
  infer_instance

/-- Translation transports kernel finiteness to the fibre over a lifted section. -/
private lemma finite_split_fiber {S : Scheme.{u}} {G H : Grp (Over S)}
    (f : G ⟶ H) (x : 𝟙_ (Over S) ⟶ G.X) [IsFinite (kernel f).X.hom] :
    IsFinite (pullback f.hom.hom (x ≫ f.hom.hom)).hom := by
  rw [← kernelFiberIso_inv_structure f x]
  infer_instance

/-- A finite scheme over a field has finitely many underlying points. -/
private lemma finite_points_over_field {L : Type u} [Field L] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of L)) [IsFinite p] : Finite X := by
  have : IsLocallyArtinian X := IsLocallyArtinian.of_locallyQuasiFinite p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact finite_of_compact_of_discrete

/-- The naturality square for base change is Cartesian. -/
private lemma baseChange_isPullback {S T : Scheme.{u}} (b : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom b) ((Over.pullback b).map f).left
      f.left (pullback.fst Y.hom b) := by
  have h : IsPullback (pullback.fst X.hom b)
      (((Over.pullback b).map f).left ≫ pullback.snd Y.hom b)
      (f.left ≫ Y.hom) b := by
    rw [show ((Over.pullback b).map f).left ≫ pullback.snd Y.hom b =
      pullback.snd X.hom b from ((Over.pullback b).map f).w, f.w]
    exact IsPullback.of_hasPullback X.hom b
  exact h.of_bot (by simp) (IsPullback.of_hasPullback Y.hom b)

/-- Split the fibre over the residue field of a chosen source point. -/
private lemma finite_preimage_image_point {S : Scheme.{u}} {G H : Grp (Over S)}
    (f : G ⟶ H) [IsFinite (kernel f).X.hom] (x : G.X.left) :
    (f.hom.hom.left ⁻¹' {f.hom.hom.left x}).Finite := by
  let T := Spec (G.X.left.residueField x)
  let a : T ⟶ G.X.left := G.X.left.fromSpecResidueField x
  let b : T ⟶ S := a ≫ G.X.hom
  let f' := (Over.pullback b).mapGrp.map f
  let x' : 𝟙_ (Over T) ⟶ ((Over.pullback b).mapGrp.obj G).X :=
    Over.homMk (pullback.lift a (𝟙 T) (by simp [b])) (by simp)
  let F := pullback f'.hom.hom (x' ≫ f'.hom.hom)
  have : IsFinite (kernel f').X.hom := finite_kernel_baseChange b f
  have : IsFinite F.hom := finite_split_fiber f' x'
  have : Finite F.left := finite_points_over_field F.hom
  have hsplit := (IsPullback.of_hasPullback f'.hom.hom (x' ≫ f'.hom.hom)).map
    (Over.forget T)
  rw [toUnit_unique (pullback.snd f'.hom.hom (x' ≫ f'.hom.hom)) (toUnit F)] at hsplit
  change IsPullback (pullback.fst f'.hom.hom (x' ≫ f'.hom.hom)).left
    F.hom f'.hom.hom.left (x' ≫ f'.hom.hom).left at hsplit
  have h := hsplit.paste_horiz (baseChange_isPullback b f.hom.hom)
  have htarget : (x' ≫ f'.hom.hom).left ≫ pullback.fst H.X.hom b =
      a ≫ f.hom.hom.left := by
    simp [x', f', Category.assoc]
  rw [htarget] at h
  have : Finite (pullback (C := Scheme.{u}) f.hom.hom.left (a ≫ f.hom.hom.left)) :=
    Finite.of_injective (α := (pullback (C := Scheme.{u}) f.hom.hom.left (a ≫ f.hom.hom.left)))
      (β := F.left) (fun z => h.isoPullback.inv z) (by
        exact h.isoPullback.inv.homeomorph.injective)
  have hrange : Set.range (a ≫ f.hom.hom.left) = {f.hom.hom.left x} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    change f.hom.hom.left '' Set.range (G.X.left.fromSpecResidueField x) = _
    rw [Scheme.range_fromSpecResidueField, Set.image_singleton]
  rw [← hrange, ← Scheme.Pullback.range_fst]
  exact Set.finite_range _

/-- Finite group-scheme kernel implies local quasi-finiteness over every field. -/
theorem fieldFiniteKernelQuasiFinite : FieldFiniteKernelQuasiFiniteStatement.{u} := by
  intro K _ G _ f _ hproper _ hkernel
  let : IsProper G.X.hom := hproper
  let : IsFinite (kernel f).X.hom := hkernel
  have : IsProper (f.hom.hom.left ≫ G.X.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.hom.hom.left := IsProper.of_comp _ G.X.hom
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  intro y
  by_cases hy : ∃ x, f.hom.hom.left x = y
  · obtain ⟨x, rfl⟩ := hy
    exact finite_preimage_image_point f x
  · have hempty : f.hom.hom.left ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hy ⟨x, hx⟩
    rw [hempty]
    exact Set.finite_empty

end Langlands.GroupScheme

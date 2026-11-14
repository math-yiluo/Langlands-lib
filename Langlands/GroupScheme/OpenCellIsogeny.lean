import Langlands.GroupScheme.DominantHomFlat
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient
import Langlands.GroupScheme.KernelCoreQuotientDimension
import Langlands.GroupScheme.Reductive.FiniteCenterOfNoCentralSubgroups
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-! # Isogenies from finite and surjective maps on open cells -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OpenCellGeometry

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A locally quasi-finite restriction to an open neighbourhood of the unit
forces the full kernel to be finite over an algebraically closed field. -/
theorem kernel_isFinite_of_open_chart_algClosed [IsAlgClosed k]
    (f : G ⟶ H) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsSeparated H.X.hom]
    {C : Over (Spec (CommRingCat.of k))} (c : C ⟶ G.X)
    [IsOpenImmersion c.left] [LocallyQuasiFinite (c ≫ f.hom.hom).left]
    (e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C)
    (he : e ≫ c = η[G.X]) : IsFinite (kernel f).X.hom := by
  have : LocallyOfFiniteType f.hom.hom.left := by
    have : LocallyOfFiniteType (f.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp f.hom.hom.left H.X.hom
  have : IsClosedImmersion (kernelι f).hom.hom.left := inferInstance
  have : IsAffineHom (kernel f).X.hom := by
    rw [← Over.w (kernelι f).hom.hom]
    infer_instance
  have : LocallyOfFiniteType (kernel f).X.hom := by
    rw [← Over.w (kernelι f).hom.hom]
    infer_instance
  let x := e.left (IdentityComponent.basePoint k)
  have hx : c.left x = IdentityComponent.identityPoint G :=
    congrArg (fun a => a.left (IdentityComponent.basePoint k)) he
  have hq : f.hom.hom.left.QuasiFiniteAt (IdentityComponent.identityPoint G) := by
    rw [← hx]
    apply Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mp
    exact (c ≫ f.hom.hom).left.quasiFiniteAt x
  have ho := Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hq
  rw [← (f.hom.hom.left.fiberHomeo _).isOpen_image] at ho
  simp only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply] at ho
  let a : (kernel f).X.left ≃ₜ
      f.hom.hom.left ⁻¹' {f.hom.hom.left (IdentityComponent.identityPoint G)} :=
    (kernelHomeo f).trans (.setCongr (by rw [hom_identityPoint f]))
  have hk : IsOpen ({IdentityComponent.identityPoint (kernel f)} : Set (kernel f).X.left) := by
    apply a.isOpen_image.mp
    simp only [Set.image_singleton]
    convert ho using 1
    congr 1
    apply Subtype.ext
    exact hom_identityPoint (kernelι f)
  exact FiniteCenterOfNoCentralSubgroups.isFinite_of_open_singleton (kernel f) _ hk

/-- The open-chart criterion for full-kernel finiteness holds over every field. -/
theorem kernel_isFinite_of_open_chart
    (f : G ⟶ H) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsSeparated H.X.hom]
    {C : Over (Spec (CommRingCat.of k))} (c : C ⟶ G.X)
    [IsOpenImmersion c.left] [LocallyQuasiFinite (c ≫ f.hom.hom).left]
    (e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C)
    (he : e ≫ c = η[G.X]) : IsFinite (kernel f).X.hom := by
  let K := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := Over.pullback b
  let G' := (GroupScheme.baseChange b).obj G
  let H' := (GroupScheme.baseChange b).obj H
  let f' := (GroupScheme.baseChange b).map f
  let c' := F.map c
  let e' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ F.obj C :=
    Functor.LaxMonoidal.ε F ≫ F.map e
  have he' : e' ≫ c' = η[G'.X] := by
    change (Functor.LaxMonoidal.ε F ≫ F.map e) ≫ F.map c = _
    rw [Category.assoc, ← F.map_comp, he]
    rfl
  have hc' : IsOpenImmersion c'.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b c inferInstance
  have hq' : LocallyQuasiFinite (c' ≫ f'.hom.hom).left := by
    change LocallyQuasiFinite (F.map c ≫ F.map f.hom.hom).left
    rw [← F.map_comp]
    exact MorphismProperty.overPullbackMap (P := @LocallyQuasiFinite) b
      (c ≫ f.hom.hom) inferInstance
  have : IsAffineHom G'.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFiniteType G'.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have : IsSeparated H'.X.hom := by
    change IsSeparated (pullback.snd H.X.hom b)
    infer_instance
  have : IsFinite (kernel f').X.hom :=
    @kernel_isFinite_of_open_chart_algClosed K _ G' H' _ f'
      ‹IsAffineHom G'.X.hom› ‹LocallyOfFiniteType G'.X.hom›
      ‹IsSeparated H'.X.hom› (F.obj C) c' hc' hq' e' he'
  let a := kernelBaseChangeIso b f
  have : IsIso a.hom.hom.hom.left :=
    ((Grp.forget _) ⋙ Over.forget _).map_isIso a.hom
  have hfin : IsFinite ((GroupScheme.baseChange b).obj (kernel f)).X.hom := by
    rw [← Over.w a.hom.hom.hom]
    infer_instance
  change IsFinite (pullback.snd (kernel f).X.hom b) at hfin
  obtain ⟨hs, hf, hqc⟩ := fieldExtension_fpqc k K
  let : Surjective b := hs
  let : Flat b := hf
  let : QuasiCompact b := hqc
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hfin

/-- A surjective map on a nonempty target open cell makes the ambient map dominant. -/
theorem isDominant_of_cell
    (f : G ⟶ H) {C D : Over (Spec (CommRingCat.of k))}
    (c : C ⟶ G.X) (d : D ⟶ H.X) (a : C ⟶ D)
    [IsOpenImmersion d.left] [IrreducibleSpace H.X.left]
    [Nonempty D.left] [Surjective a.left]
    (h : c ≫ f.hom.hom = a ≫ d) : IsDominant f.hom.hom.left := by
  have : IsDominant d.left :=
    ⟨d.left.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have : IsDominant (c.left ≫ f.hom.hom.left) := by
    change IsDominant (c ≫ f.hom.hom).left
    rw [h, Over.comp_left]
    infer_instance
  exact IsDominant.of_comp c.left f.hom.hom.left

/-- A finite surjective map between open cells of smooth connected affine groups
gives an isogeny of the ambient groups. -/
theorem isIsogeny_of_cell
    (f : G ⟶ H) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    {C D : Over (Spec (CommRingCat.of k))}
    (c : C ⟶ G.X) (d : D ⟶ H.X) (a : C ⟶ D)
    [IsOpenImmersion c.left] [IsOpenImmersion d.left]
    [IsFinite a.left] [Surjective a.left]
    (e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C)
    (he : e ≫ c = η[G.X])
    (h : c ≫ f.hom.hom = a ≫ d) : IsIsogeny f := by
  have : GeometricallyIntegral H.X.hom :=
    smoothConnectedAffineGeometry.1 k H inferInstance inferInstance inferInstance
  have : IsIntegral H.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton H.X.hom
  have : Nonempty D.left :=
    ⟨a.left (e.left (IdentityComponent.basePoint k))⟩
  have : IsDominant f.hom.hom.left := isDominant_of_cell f c d a h
  have : LocallyOfFiniteType f.hom.hom.left := by
    have : LocallyOfFiniteType (f.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp f.hom.hom.left H.X.hom
  have : QuasiCompact f.hom.hom.left := by
    have : QuasiCompact (f.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w]
      infer_instance
    exact QuasiCompact.of_comp f.hom.hom.left H.X.hom
  have : IsLocallyNoetherian H.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  have : Flat f.hom.hom.left := DominantHomFlat.flat_of_isDominant f
  have : Surjective f.hom.hom.left := DominantHomFlat.surjective_of_flat f
  have : LocallyQuasiFinite (c ≫ f.hom.hom).left := by
    rw [h, Over.comp_left]
    infer_instance
  have : IsFinite (kernel f).X.hom := kernel_isFinite_of_open_chart f c e he
  exact ⟨isFinite_of_finite_kernel f, inferInstance, inferInstance⟩

/-- The homomorphism restricts to a finite surjective map between open cells,
with the source cell containing the unit section. -/
def HasFiniteSurjectiveOpenCells (f : G ⟶ H) : Prop :=
  ∃ (C D : Over (Spec (CommRingCat.of k))) (c : C ⟶ G.X) (d : D ⟶ H.X)
    (a : C ⟶ D), IsOpenImmersion c.left ∧ IsOpenImmersion d.left ∧
      IsFinite a.left ∧ Surjective a.left ∧
        ∃ (e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C),
          e ≫ c = η[G.X] ∧ c ≫ f.hom.hom = a ≫ d

/-- The bundled open-cell condition implies an isogeny for smooth affine groups
with connected target. -/
theorem HasFiniteSurjectiveOpenCells.isIsogeny
    {f : G ⟶ H} (hf : HasFiniteSurjectiveOpenCells f)
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left] :
    IsIsogeny f := by
  obtain ⟨C, D, c, d, a, hc, hd, ha, hs, e, he, h⟩ := hf
  exact isIsogeny_of_cell f c d a e he h

end Langlands.GroupScheme.OpenCellGeometry

import Langlands.GroupScheme.DominantHomFlat
import Langlands.GroupScheme.AffineHomImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme.DominantHom

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A rational point in the topological image has a rational lift. -/
theorem rational_lift [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    (f : G ⟶ H) (b : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X)
    (hb : b.left (IsLocalRing.closedPoint k) ∈ Set.range f.hom.hom.left) :
    ∃ a : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X, a ≫ f.hom.hom = b := by
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  have hbc : IsClosed ({b.left (IsLocalRing.closedPoint k)} : Set H.X.left) :=
    ((pointEquivClosedPoint H.X.hom) ⟨b.left, b.w⟩).property
  obtain ⟨a, ha, hac⟩ := nonempty_inter_closedPoints
    (show (f.hom.hom.left ⁻¹' {b.left (IsLocalRing.closedPoint k)}).Nonempty from hb)
    (hbc.preimage f.hom.hom.left.continuous).isLocallyClosed
  let a' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom a hac) (by simp)
  refine ⟨a', Over.OverMorphism.ext ?_⟩
  apply ext_of_apply_closedPoint_eq H.X.hom (a' ≫ f.hom.hom).w b.w
  simpa [a'] using ha

/-- An open dominant homomorphism is surjective on rational points. -/
theorem rational_surjective_of_flat (f : G ⟶ H)
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    [Flat f.hom.hom.left] [LocallyOfFinitePresentation f.hom.hom.left]
    [IsDominant f.hom.hom.left] :
    Function.Surjective (fun a : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X =>
      a ≫ f.hom.hom) := by
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  intro b
  let τ := (GrpObj.mulRight b).hom
  have : IsIso τ.left := inferInstanceAs (IsIso ((Over.forget _).map τ))
  let U : H.X.left.Opens := ⟨Set.range f.hom.hom.left, f.hom.hom.left.isOpenMap.isOpen_range⟩
  have hU : ((τ.left ⁻¹ᵁ U) : Set H.X.left).Nonempty := by
    obtain ⟨y, hy⟩ := τ.left.surjective
      (f.hom.hom.left (η[G.X].left (IsLocalRing.closedPoint k)))
    exact ⟨y, by change τ.left y ∈ Set.range f.hom.hom.left; rw [hy]; exact ⟨_, rfl⟩⟩
  obtain ⟨v, hv⟩ := f.hom.hom.left.denseRange.exists_mem_open (τ.left ⁻¹ᵁ U).isOpen hU
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (⟨v, hv⟩ : ((f.hom.hom.left ⁻¹ᵁ (τ.left ⁻¹ᵁ U)) : Set G.X.left).Nonempty)
    (f.hom.hom.left ⁻¹ᵁ (τ.left ⁻¹ᵁ U)).isOpen.isLocallyClosed
  let z' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom z hzc) (by simp)
  obtain ⟨w, hw⟩ := rational_lift f (z' ≫ f.hom.hom ≫ τ) (by
    change τ.left (f.hom.hom.left
      (pointOfClosedPoint G.X.hom z hzc (IsLocalRing.closedPoint k))) ∈ _
    have hz' : τ.left (f.hom.hom.left z) ∈ Set.range f.hom.hom.left := hz
    simpa only [pointOfClosedPoint_apply] using hz')

  refine ⟨z'⁻¹ * w, ?_⟩
  change (z'⁻¹ * w) ≫ f.hom.hom = b
  rw [mul_comp, GrpObj.inv_comp, hw]
  change (z' ≫ f.hom.hom)⁻¹ * ((z' ≫ f.hom.hom) ≫
    ((𝟙 H.X) * (toUnit H.X ≫ b))) = b
  rw [comp_mul]
  simp

/-- Flatness and rational surjectivity imply topological surjectivity. -/
theorem surjective_of_rational (f : G ⟶ H) [LocallyOfFiniteType H.X.hom]
    [Flat f.hom.hom.left]
    (hf : Function.Surjective (fun a : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X =>
      a ≫ f.hom.hom)) : Surjective f.hom.hom.left := by
  have : JacobsonSpace H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  refine ⟨fun y => ?_⟩
  obtain ⟨c, hcy, hc⟩ := nonempty_inter_closedPoints
    (⟨y, subset_closure (Set.mem_singleton y)⟩ : (closure ({y} : Set H.X.left)).Nonempty)
    (isClosed_closure (s := ({y} : Set H.X.left))).isLocallyClosed
  let c' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X :=
    Over.homMk (pointOfClosedPoint H.X.hom c hc) (by simp)
  obtain ⟨a, ha⟩ := hf c'
  have hac : f.hom.hom.left (a.left (IsLocalRing.closedPoint k)) = c := by
    simpa [c'] using congr(($ha).left (IsLocalRing.closedPoint k))
  have hspec : y ⤳ f.hom.hom.left (a.left (IsLocalRing.closedPoint k)) := by
    rw [specializes_iff_mem_closure, hac]
    exact hcy
  obtain ⟨x, -, hx⟩ := Flat.generalizingMap f.hom.hom.left hspec
  exact ⟨x, hx⟩

end AlgClosed

end Langlands.GroupScheme.DominantHom

namespace Langlands.GroupScheme.DominantHom

/-- A schematically dominant homomorphism between affine finite type groups with
smooth target is faithfully flat, over an arbitrary field. -/
theorem flat_surjective {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [LocallyOfFiniteType G.X.hom] [Smooth H.X.hom]
    (f : G ⟶ H) [IsSchemeTheoreticallyDominant f.hom.hom.left] :
    Flat f.hom.hom.left ∧ Surjective f.hom.hom.left := by
  let Ω : Type u := AlgebraicClosure k
  let b : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let G' := (GroupScheme.baseChange b).obj G
  let H' := (GroupScheme.baseChange b).obj H
  let f' : G' ⟶ H' := (GroupScheme.baseChange b).map f
  have : IsAffineHom G'.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have : IsAffineHom H'.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd H.X.hom b))
  have : LocallyOfFiniteType G'.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom b))
  have : Smooth H'.X.hom :=
    inferInstanceAs (Smooth (pullback.snd H.X.hom b))
  have : IsAffine H'.X.left := isAffine_of_isAffineHom H'.X.hom
  have : QuasiSeparated H'.X.hom :=
    HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated).mpr inferInstance
  have : QuasiCompact f'.hom.hom.left := by
    have : QuasiCompact (f'.hom.hom.left ≫ H'.X.hom) := by
      rw [Over.w]
      infer_instance
    exact QuasiCompact.of_comp f'.hom.hom.left H'.X.hom
  have : LocallyOfFiniteType f'.hom.hom.left := by
    have : LocallyOfFiniteType (f'.hom.hom.left ≫ H'.X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp f'.hom.hom.left H'.X.hom
  have : IsLocallyNoetherian H'.X.left := LocallyOfFiniteType.isLocallyNoetherian H'.X.hom
  have : LocallyOfFinitePresentation f'.hom.hom.left := inferInstance
  have : GeometricallyReduced H.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth _
  have : IsReduced H'.X.left :=
    inferInstanceAs (IsReduced (pullback H.X.hom b))
  have houter : IsPullback
      (f'.hom.hom.left ≫ pullback.snd H.X.hom b)
      (pullback.fst G.X.hom b) b (f.hom.hom.left ≫ H.X.hom) := by
    change IsPullback (((Over.pullback b).map f.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w f.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback G.X.hom b).flip
  have hp := houter.of_right
    (show f'.hom.hom.left ≫ pullback.fst H.X.hom b =
        pullback.fst G.X.hom b ≫ f.hom.hom.left by
      change ((Over.pullback b).map f.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback H.X.hom b).flip
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : QuasiSeparated H.X.hom :=
    HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated).mpr inferInstance
  have : QuasiCompact f.hom.hom.left := by
    have : QuasiCompact (f.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w]
      infer_instance
    exact QuasiCompact.of_comp f.hom.hom.left H.X.hom
  have : IsSchemeTheoreticallyDominant f'.hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isPullback hp.flip
  have hflat' : Flat f'.hom.hom.left := DominantHomFlat.flat_of_isDominant f'
  have hsurj' : Surjective f'.hom.hom.left :=
    surjective_of_rational f' (rational_surjective_of_flat f')
  have hflat : Flat f.hom.hom.left := by
    apply Flat.of_stalkMap
    intro x
    obtain ⟨z, hz⟩ := (pullback.fst G.X.hom b).surjective x
    rw [← hz]
    exact DominantHomFlat.flat_stalkMap_of_comm f.hom.hom.left f'.hom.hom.left
      (pullback.fst H.X.hom b) (pullback.fst G.X.hom b) hp.w z
      (Flat.stalkMap f'.hom.hom.left z)
  have hsurj : Surjective f.hom.hom.left := by
    refine ⟨fun y => ?_⟩
    obtain ⟨y', hy'⟩ := (pullback.fst H.X.hom b).surjective y
    obtain ⟨x', hx'⟩ := f'.hom.hom.left.surjective y'
    refine ⟨(pullback.fst G.X.hom b) x', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hp.w, Scheme.Hom.comp_apply]
    exact (congrArg (fun z : H'.X.left => (pullback.fst H.X.hom b) z) hx').trans hy'
  exact ⟨hflat, hsurj⟩

end Langlands.GroupScheme.DominantHom

namespace Langlands.GroupScheme

/-- Dominant homomorphisms to smooth affine groups over a field are faithfully flat. -/
def DominantHomFaithfullyFlatStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [LocallyOfFiniteType G.X.hom] [Smooth H.X.hom]
    (f : G ⟶ H), IsSchemeTheoreticallyDominant f.hom.hom.left →
      Flat f.hom.hom.left ∧ Surjective f.hom.hom.left

/-- The universe-general dominant-homomorphism statement. -/
theorem dominantHomFaithfullyFlat : DominantHomFaithfullyFlatStatement.{u} := by
  intro k _ G H _ _ _ _ f hf
  have := hf
  exact DominantHom.flat_surjective f

namespace AffineHomImage

/-- The original projection onto the schematic image is an fppf cover; the
image is smooth when the source is smooth. -/
theorem projection_geometry {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Smooth G.X.hom] [LocallyOfFiniteType H.X.hom] (f : G ⟶ H) :
    Smooth (image f).X.hom ∧ Flat (projection f).hom.hom.left ∧
      Surjective (projection f).hom.hom.left ∧
      LocallyOfFinitePresentation (projection f).hom.hom.left ∧
      QuasiCompact (projection f).hom.hom.left := by
  have hs : Smooth (image f).X.hom := smooth_image f
  obtain ⟨hflat, hsurj⟩ := DominantHom.flat_surjective (projection f)
  have : LocallyOfFiniteType (projection f).hom.hom.left := by
    have : LocallyOfFiniteType ((projection f).hom.hom.left ≫ (image f).X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp (projection f).hom.hom.left (image f).X.hom
  have : IsLocallyNoetherian (image f).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (image f).X.hom
  exact ⟨hs, hflat, hsurj, inferInstance,
    inferInstanceAs (QuasiCompact (projectionOver f).left)⟩

end AffineHomImage
end Langlands.GroupScheme

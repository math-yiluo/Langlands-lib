import Langlands.GroupScheme.DominantHomFlatStatement
import Langlands.GroupScheme.DominantHomFlat
import Langlands.GroupScheme.BaseChangeReflection
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Dominant homomorphisms to reduced algebraic groups -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace DominantHomFlat

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [LocallyOfFiniteType H.X.hom]
    (f : G ⟶ H) [IsDominant f.hom.hom.left]

omit [QuasiCompact G.X.hom] [LocallyOfFiniteType H.X.hom] in
private theorem exists_rationalPoint_image_mem (U : H.X.left.Opens)
    (hU : (U : Set H.X.left).Nonempty) :
    ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
      (g ≫ f.hom.hom).left (IsLocalRing.closedPoint k) ∈ U := by
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  obtain ⟨z, hz⟩ := f.hom.hom.left.denseRange.exists_mem_open U.isOpen hU
  obtain ⟨c, hc, hclosed⟩ := nonempty_inter_closedPoints
    (⟨z, hz⟩ : (f.hom.hom.left ⁻¹' (U : Set H.X.left)).Nonempty)
    (U.isOpen.preimage f.hom.hom.left.continuous).isLocallyClosed
  refine ⟨Over.homMk (pointOfClosedPoint G.X.hom c hclosed)
    (pointOfClosedPoint_comp G.X.hom c hclosed), ?_⟩
  change f.hom.hom.left (pointOfClosedPoint G.X.hom c hclosed
    (IsLocalRing.closedPoint k)) ∈ U
  rw [pointOfClosedPoint_apply]
  exact hc

omit [IsAlgClosed k] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
  [LocallyOfFiniteType H.X.hom] [IsDominant f.hom.hom.left] in
private theorem translation_comm
    (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X) :
    FiniteIndexTransfer.leftMul G g ≫ f.hom.hom =
      f.hom.hom ≫ FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom) := by
  simp only [FiniteIndexTransfer.leftMul, ← Hom.mul_def]
  rw [MonObj.mul_comp, MonObj.comp_mul]
  simp

omit [QuasiCompact G.X.hom] in
/-- Translates by image points move every point into any nonempty target open. -/
theorem exists_image_translate_mem (U : H.X.left.Opens)
    (hU : (U : Set H.X.left).Nonempty) :
    ∀ w : H.X.left, ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
      (FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom)).left w ∈ U := by
  have : JacobsonSpace H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  by_contra! hne
  obtain ⟨w, hw⟩ := hne
  let Z : Set H.X.left := ⋂ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
    (FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom)).left ⁻¹' (U : Set H.X.left)ᶜ
  have hZ : IsClosed Z := isClosed_iInter fun g =>
    U.isOpen.isClosed_compl.preimage
      (FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom)).left.continuous
  obtain ⟨c, hcZ, hc⟩ :=
    nonempty_inter_closedPoints ⟨w, Set.mem_iInter.mpr hw⟩ hZ.isLocallyClosed
  let c' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X :=
    Over.homMk (pointOfClosedPoint H.X.hom c hc) (pointOfClosedPoint_comp H.X.hom c hc)
  let t := (GrpObj.mulRight c').hom
  have : IsIso t.left := inferInstanceAs (IsIso ((Over.forget _).map t))
  let V : H.X.left.Opens := t.left ⁻¹ᵁ U
  have hV : (V : Set H.X.left).Nonempty := by
    obtain ⟨u, hu⟩ := hU
    obtain ⟨z, hz⟩ := t.left.surjective u
    refine ⟨z, ?_⟩
    change t.left z ∈ U
    rwa [hz]
  obtain ⟨g, hg⟩ := exists_rationalPoint_image_mem f V hV
  have hmove : (g ≫ f.hom.hom) ≫ t =
      c' ≫ FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom) := by
    simp only [t, GrpObj.mulRight, FiniteIndexTransfer.leftMul, ← Hom.mul_def,
      MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc,
      toUnit_unit, Category.id_comp]
  have hm : (FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom)).left c ∈ U := by
    change t.left ((g ≫ f.hom.hom).left (IsLocalRing.closedPoint k)) ∈ U at hg
    have he : t.left ((g ≫ f.hom.hom).left (IsLocalRing.closedPoint k)) =
        (FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom)).left c := by
      have he := congrArg (fun a => a.left (IsLocalRing.closedPoint k)) hmove
      change t.left ((g ≫ f.hom.hom).left (IsLocalRing.closedPoint k)) =
        (FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom)).left
          (pointOfClosedPoint H.X.hom c hc (IsLocalRing.closedPoint k)) at he
      rwa [pointOfClosedPoint_apply] at he
    rwa [he] at hg
  exact Set.mem_iInter.mp hcZ g hm

/-- Dominance and reducedness make a finite-type group homomorphism faithfully flat. -/
theorem flat_surjective [IsReduced H.X.left] :
    Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
      QuasiCompact f.hom.hom.left := by
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  have : QuasiSeparated H.X.hom :=
    HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated).mpr inferInstance
  have : LocallyOfFiniteType f.hom.hom.left := by
    have : LocallyOfFiniteType (f.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w f.hom.hom]
      infer_instance
    exact locallyOfFiniteType_of_comp f.hom.hom.left H.X.hom
  have : QuasiCompact f.hom.hom.left := by
    have : QuasiCompact (f.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w f.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp f.hom.hom.left H.X.hom
  have hflat : Flat f.hom.hom.left := flat_of_isDominant f
  have : Flat f.hom.hom.left := hflat
  let I : H.X.left.Opens :=
    ⟨Set.range f.hom.hom.left, by
      simpa only [Set.image_univ] using f.hom.hom.left.isOpenMap Set.univ isOpen_univ⟩
  have hI : (I : Set H.X.left).Nonempty :=
    ⟨f.hom.hom.left (η[G.X].left (IsLocalRing.closedPoint k)), ⟨_, rfl⟩⟩
  have hsurj : Surjective f.hom.hom.left := by
    refine ⟨fun w => ?_⟩
    obtain ⟨g, hg⟩ := exists_image_translate_mem f I hI w
    obtain ⟨z, hz⟩ := hg
    have : IsIso (FiniteIndexTransfer.leftMul G g).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (FiniteIndexTransfer.leftMul G g)))
    have : IsIso (FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom)).left :=
      inferInstanceAs (IsIso ((Over.forget _).map
        (FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom))))
    obtain ⟨z', hz'⟩ := (FiniteIndexTransfer.leftMul G g).left.surjective z
    refine ⟨z', ?_⟩
    apply (FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom)).left.homeomorph.injective
    change (FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom)).left (f.hom.hom.left z') =
      (FiniteIndexTransfer.leftMul H (g ≫ f.hom.hom)).left w
    have he := congrArg (fun a => a.left z') (translation_comm f g)
    simpa only [Over.comp_left, Scheme.Hom.comp_apply, hz', hz] using he.symm
  exact ⟨hflat, hsurj, inferInstance⟩

end DominantHomFlat

/-- The exact algebraically closed target proposition. -/
theorem dominantGroupHomFlat : DominantGroupHomFlatStatement.{u} := by
  intro k _ _ G H _ _ _ _ f _
  exact DominantHomFlat.flat_surjective f

namespace DominantHomFlat

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- The square of a group-scheme homomorphism after an arbitrary base change. -/
theorem baseChange_isPullback {S' : Scheme.{u}} (b : S' ⟶ Spec (CommRingCat.of k))
    (f : G ⟶ H) :
    IsPullback
      ((GroupScheme.baseChange b).map f).hom.hom.left
      (CategoryTheory.Limits.pullback.fst G.X.hom b)
      (CategoryTheory.Limits.pullback.fst H.X.hom b) f.hom.hom.left := by
  have houter : IsPullback
      (((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.snd H.X.hom b)
      (pullback.fst G.X.hom b) b (f.hom.hom.left ≫ H.X.hom) := by
    change IsPullback (((Over.pullback b).map f.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w f.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback G.X.hom b).flip
  exact houter.of_right
    (show ((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.fst H.X.hom b =
        pullback.fst G.X.hom b ≫ f.hom.hom.left by
      change ((Over.pullback b).map f.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback H.X.hom b).flip

/-- A schematically dominant monomorphism of finite-type groups with
geometrically reduced target is an isomorphism over the original field. -/
theorem isIso_of_schematicallyDominant
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [LocallyOfFiniteType H.X.hom] [GeometricallyReduced H.X.hom]
    (f : G ⟶ H) [Mono f.hom.hom] [IsSchemeTheoreticallyDominant f.hom.hom.left] :
    IsIso f := by
  let b := toAlgebraicClosure k
  have hb := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Surjective b := hb.1
  have : Flat b := hb.2.1
  have : QuasiCompact b := hb.2.2
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  have : QuasiSeparated H.X.hom :=
    HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated).mpr inferInstance
  have hqc : QuasiCompact f.hom.hom.left := by
    have : QuasiCompact (f.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w f.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp f.hom.hom.left H.X.hom
  have : QuasiCompact f.hom.hom.left := hqc
  let fK := (GroupScheme.baseChange b).map f
  have hp := baseChange_isPullback b f
  have : IsSchemeTheoreticallyDominant fK.hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isPullback hp.flip
  have : QuasiCompact fK.hom.hom.left :=
    MorphismProperty.of_isPullback hp.flip hqc
  have : IsReduced ((GroupScheme.baseChange b).obj H).X.left :=
    pullback_of_geometrically
      (GeometricallyReduced.geometrically_isReduced (f := H.X.hom)) (AlgebraicClosure k) b
  have hGft : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have hGqc : QuasiCompact ((GroupScheme.baseChange b).obj G).X.hom := by
    change QuasiCompact (pullback.snd G.X.hom b)
    infer_instance
  have hHft : LocallyOfFiniteType ((GroupScheme.baseChange b).obj H).X.hom := by
    change LocallyOfFiniteType (pullback.snd H.X.hom b)
    infer_instance
  have hK := flat_surjective fK
  have : Flat fK.hom.hom.left := hK.1
  have : Surjective fK.hom.hom.left := hK.2.1
  have : Mono fK.hom.hom := by
    change Mono ((Over.pullback b).map f.hom.hom)
    infer_instance
  have : IsIso fK.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  have hIso : IsIso f.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme.{u})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hp ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : IsIso f.hom.hom.left := hIso
  have : IsIso ((Over.forget _).map f.hom.hom) := by
    change IsIso f.hom.hom.left
    exact hIso
  have : IsIso f.hom.hom := isIso_of_reflects_iso f.hom.hom (Over.forget _)
  let e : G ≅ H := Grp.mkIso' (asIso f.hom.hom)
  change IsIso e.hom
  infer_instance

end DominantHomFlat

end Langlands.GroupScheme

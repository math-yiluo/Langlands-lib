import Langlands.GroupScheme.FiniteTypeMonomorphismStatement
import Langlands.GroupScheme.DominantHomFlatProof
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.GroupScheme.ImageGenerationAppend
import Langlands.GroupScheme.ImageGenerationDominant
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite-type group-scheme monomorphisms are closed immersions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace FiniteTypeMonomorphism

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
  [LocallyOfFiniteType H.X.hom] [IsSeparated H.X.hom]

/-- A monomorphism with reduced source identifies it with its reduced image
closure. Neither group is required to be affine. -/
theorem isClosedImmersion_of_reduced [IsReduced G.X.left]
    (f : G ⟶ H) [Mono f.hom.hom.left] :
    IsClosedImmersion f.hom.hom.left := by
  let Z := TopologicalSpace.Closeds.closure (Set.range f.hom.hom.left)
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let O : Over (Spec (CommRingCat.of k)) := Over.mk (I.subschemeι ≫ H.X.hom)
  let j : O ⟶ H.X := Over.homMk I.subschemeι rfl
  have hj : IsClosedImmersion j.left :=
    inferInstanceAs (IsClosedImmersion I.subschemeι)
  let := hj
  have : Mono j := Over.mono_of_mono_left j
  have : IsReduced O.left :=
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker Z).1
  have hrange : Set.range j.left = closure (Set.range f.hom.hom.left) := by
    change Set.range I.subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hker : I.subschemeι.ker ≤ f.hom.hom.left.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker Z).2
      f.hom.hom.left subset_closure
  let c : G.X ⟶ O :=
    Over.homMk (IsClosedImmersion.lift I.subschemeι f.hom.hom.left hker) (by
      change IsClosedImmersion.lift I.subschemeι f.hom.hom.left hker ≫
        (I.subschemeι ≫ H.X.hom) = _
      rw [← Category.assoc, IsClosedImmersion.lift_fac, Over.w f.hom.hom])
  have hc : c ≫ j = f.hom.hom :=
    Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  have : LocallyOfFiniteType O.hom :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ H.X.hom))
  have : IsSeparated O.hom :=
    inferInstanceAs (IsSeparated (I.subschemeι ≫ H.X.hom))
  have : QuasiCompact c.left := by
    have : QuasiCompact (c.left ≫ O.hom) := by rw [Over.w]; infer_instance
    exact QuasiCompact.of_comp c.left O.hom
  have : IsDominant c.left := by
    rw [isDominant_iff, denseRange_iff_closure_range,
      j.left.isClosedEmbedding.isEmbedding.closure_eq_preimage_closure_image]
    have himage : j.left '' Set.range c.left = Set.range f.hom.hom.left := by
      rw [← Set.range_comp]
      have he := congrArg
        (fun a : G.X ⟶ H.X => (a.left : G.X.left → H.X.left)) hc
      exact congrArg Set.range he
    rw [himage, ← hrange]
    simp
  have : IsSchemeTheoreticallyDominant c.left :=
    IsSchemeTheoreticallyDominant.of_isDominant c.left
  have : IsSchemeTheoreticallyDominant (c ⊗ₘ c).left :=
    ImageGeneration.isSchemeTheoreticallyDominant_tensorHom c
  let e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O := η[G.X] ≫ c
  have he : e ≫ j = η[H.X] := by
    dsimp only [e]
    rw [Category.assoc, hc, IsMonHom.one_hom]
  obtain ⟨m, hm⟩ : ∃ m : O ⊗ O ⟶ O, m ≫ j = (j ⊗ₘ j) ≫ μ[H.X] := by
    refine exists_over_factor_of_schematic_precomp j (c ⊗ₘ c) _
      (μ[G.X] ≫ c) ?_
    rw [Category.assoc, hc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hc]
  obtain ⟨v, hv⟩ : ∃ v : O ⟶ O, v ≫ j = j ≫ ι[H.X] := by
    refine exists_over_factor_of_schematic_precomp j c _ (ι[G.X] ≫ c) ?_
    rw [← Category.assoc c, Category.assoc (ι[G.X]), hc]
    exact (GrpObj.inv_hom f.hom.hom).symm
  let : GrpObj O :=
    Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono j e m v he hm hv
  let : IsMonHom j :=
    Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono j e m v he hm hv
  have : IsMonHom c := by
    constructor
    · apply (cancel_mono j).mp
      rw [Category.assoc, hc, IsMonHom.one_hom, IsMonHom.one_hom]
    · apply (cancel_mono j).mp
      rw [Category.assoc, hc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
        tensorHom_comp_tensorHom_assoc, hc]
  let J : GroupScheme (Spec (CommRingCat.of k)) := { X := O }
  let q : G ⟶ J := Grp.homMk c
  have : IsDominant q.hom.hom.left := inferInstanceAs (IsDominant c.left)
  have hq := DominantHomFlat.flat_surjective q
  have : Flat c.left := hq.1
  have : Surjective c.left := hq.2.1
  have : Mono c.left := mono_of_mono_fac (congrArg (fun a : G.X ⟶ H.X => a.left) hc)
  have : IsIso c.left := Flat.isIso_of_surjective_of_mono c.left
  have heq : f.hom.hom.left = c.left ≫ j.left :=
    (congrArg (fun a : G.X ⟶ H.X => a.left) hc).symm
  rw [heq]
  infer_instance

/-- Over an algebraically closed field the reduction of the source suffices
to prove universal closedness of the given monomorphism. -/
theorem isClosedImmersion (f : G ⟶ H) [Mono f.hom.hom.left] :
    IsClosedImmersion f.hom.hom.left := by
  have : QuasiCompact (reducedSubgroup G).X.hom :=
    inferInstanceAs (QuasiCompact (ReducedSubgroup.redι G.X.left ≫ G.X.hom))
  have : Mono ((reducedSubgroupι G) ≫ f).hom.hom.left := by
    change Mono (ReducedSubgroup.redι G.X.left ≫ f.hom.hom.left)
    infer_instance
  have hred := isClosedImmersion_of_reduced ((reducedSubgroupι G) ≫ f)
  have : IsClosedImmersion (ReducedSubgroup.redι G.X.left ≫ f.hom.hom.left) := hred
  have : Surjective (ReducedSubgroup.redι G.X.left) :=
    ⟨ReducedSubgroup.redι_surjective G.X.left⟩
  have : UniversallyClosed f.hom.hom.left :=
    UniversallyClosed.of_comp_surjective (ReducedSubgroup.redι G.X.left) f.hom.hom.left
  have : LocallyOfFiniteType f.hom.hom.left := by
    have : LocallyOfFiniteType (f.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w f.hom.hom]
      infer_instance
    exact locallyOfFiniteType_of_comp f.hom.hom.left H.X.hom
  have : IsProper f.hom.hom.left := {}
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩

end FiniteTypeMonomorphism

set_option backward.isDefEq.respectTransparency false in
/-- The exact arbitrary-field finite-type group-scheme monomorphism statement. -/
theorem finiteTypeMonomorphism : FiniteTypeMonomorphismStatement.{u} := by
  intro k _ G H _ _ _ _ _ _ f _
  let b := toAlgebraicClosure k
  have hb := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Surjective b := hb.1
  have : Flat b := hb.2.1
  have : QuasiCompact b := hb.2.2
  let fK := (GroupScheme.baseChange b).map f
  have hp := DominantHomFlat.baseChange_isPullback b f
  have : Mono fK.hom.hom.left :=
    MorphismProperty.of_isPullback
      (P := MorphismProperty.monomorphisms Scheme.{u}) hp.flip inferInstance
  have : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have : QuasiCompact ((GroupScheme.baseChange b).obj G).X.hom := by
    change QuasiCompact (pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFiniteType ((GroupScheme.baseChange b).obj H).X.hom := by
    change LocallyOfFiniteType (pullback.snd H.X.hom b)
    infer_instance
  have : IsSeparated ((GroupScheme.baseChange b).obj H).X.hom := by
    change IsSeparated (pullback.snd H.X.hom b)
    infer_instance
  have : IsClosedImmersion fK.hom.hom.left :=
    FiniteTypeMonomorphism.isClosedImmersion fK
  have hcover : (Surjective (pullback.fst H.X.hom b) ∧
      Flat (pullback.fst H.X.hom b)) ∧ QuasiCompact (pullback.fst H.X.hom b) :=
    ⟨⟨MorphismProperty.pullback_fst _ _ (show Surjective b from hb.1),
      MorphismProperty.pullback_fst _ _ (show Flat b from hb.2.1)⟩,
      MorphismProperty.pullback_fst _ _ (show QuasiCompact b from hb.2.2)⟩
  have : UniversallyClosed f.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hp hcover inferInstance
  have : LocallyOfFiniteType f.hom.hom.left := by
    have : LocallyOfFiniteType (f.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w f.hom.hom]
      infer_instance
    exact locallyOfFiniteType_of_comp f.hom.hom.left H.X.hom
  have : IsProper f.hom.hom.left := {}
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩

end Langlands.GroupScheme

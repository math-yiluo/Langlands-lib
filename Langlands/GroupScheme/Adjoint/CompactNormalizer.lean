import Langlands.BruhatTits.RationalPoints.DenseBoundedNormalizerAdjointProof
import Langlands.GroupScheme.Adjoint.Assembly

/-! # Compact closures of normalizers in adjoint groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- The full normalizer of a subgroup has compact closure in the given topology. -/
def HasCompactNormalizerClosure {M : Type*} [Group M] [TopologicalSpace M]
    (H : Subgroup M) : Prop :=
  IsCompact (closure (Subgroup.normalizer (H : Set M) : Set M))

namespace IsAdjoint

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- An adjoint group is its own full-centre quotient. -/
theorem identityQuotient (hG : IsAdjoint G) : IsAdjointQuotient (𝟙 G) := by
  let : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  apply isAdjointQuotient_of_fppf_kernel_range (𝟙 G)
    hG.isSemisimple.isConnectedReductive hG.isSemisimple.isConnectedReductive
    hG.center_eq_bot
    (by change Flat (𝟙 G.X.left); infer_instance)
    (by change Surjective (𝟙 G.X.left); infer_instance)
    (by change LocallyOfFinitePresentation (𝟙 G.X.left); infer_instance)
  rw [hG.center_eq_bot]
  apply le_antisymm
  · intro T x hx
    have hx' := (mem_range_kernelι_iff (𝟙 G) x).mp hx
    simpa only [Grp.id_hom_hom, Category.comp_id, SubgroupFunctor.bot_carrier,
      Subgroup.mem_bot] using hx'
  · intro T x hx
    have hx' : x = 1 := by
      simpa only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hx
    apply (mem_range_kernelι_iff (𝟙 G) x).mpr
    simpa only [Grp.id_hom_hom, Category.comp_id] using hx'

end IsAdjoint

namespace SubgroupFunctor

/-- A dominant group homomorphism sends a dense rational subgroup to a dense
rational subgroup, without requiring surjectivity on rational points. -/
theorem hasDenseRationalPointFamily_map
    {k : Type u} [Field k]
    {G A : GroupScheme (Spec (CommRingCat.of k))}
    (q : G ⟶ A) [IsDominant q.hom.hom.left]
    (H : Subgroup (rationalPoints G))
    (hH : HasDenseRationalPointFamily H.subtype) :
    HasDenseRationalPointFamily (H.map (rationalPoints.map q)).subtype := by
  apply (q.hom.hom.left.denseRange.dense_image q.hom.hom.left.continuous hH).mono
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨h, t, rfl⟩ := Set.mem_iUnion.mp hz
  refine Set.mem_iUnion.mpr ⟨⟨rationalPoints.map q h.val, ⟨h.val, h.property, rfl⟩⟩,
    t, ?_⟩
  rfl

end SubgroupFunctor

/-- In an adjoint group, the normalizer of an algebraically bounded Zariski-dense
rational subgroup has compact closure in the canonical local-field point topology. -/
theorem isCompact_closure_normalizer_of_adjoint
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsAdjoint G)
    (H : Subgroup (rationalPoints G))
    (hHb : letI : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      IsAlgebraicallyBounded F G.X (H : Set (rationalPoints G)))
    (hHd : HasDenseRationalPointFamily H.subtype) :
    letI : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    HasCompactNormalizerClosure H := by
  let : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have hb := Langlands.BruhatTits.RationalPoints.denseBoundedNormalizerAdjoint
    F G hG.isSemisimple.isConnectedReductive G (𝟙 G) hG.identityQuotient H hHb hHd
  have heq : rationalPoints.map (𝟙 G) ''
      (Subgroup.normalizer (H : Set (rationalPoints G)) : Set (rationalPoints G)) =
      (Subgroup.normalizer (H : Set (rationalPoints G)) : Set (rationalPoints G)) := by
    change (fun x : rationalPoints G => x ≫ (𝟙 G : G ⟶ G).hom.hom) '' _ = _
    simp only [Grp.id_hom_hom, Category.comp_id, Set.image_id']
  rw [heq] at hb
  exact hb.isCompact_closure G.X

end Langlands.GroupScheme

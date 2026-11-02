import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMapProofs
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Reductive.Basic
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-! # Closed represented subgroups in the identity-test point topology -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R] [TopologicalSpace R]
    {X Y : Over (Spec (CommRingCat.of R))} [IsAffine X.left] [IsAffine Y.left]

private theorem rationalPointMap_eq (f : X ⟶ Y) :
    let : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
    let : TopologicalSpace (RationalPoint R Y) := rationalPointTopology R Y
    (fun p : RationalPoint R X => p ≫ f) =
      (rationalPointHomeomorph R Y).symm ∘
        (fun p : RingPoint R X R => p ≫ f) ∘ rationalPointHomeomorph R X := by
  let : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
  let : TopologicalSpace (RationalPoint R Y) := rationalPointTopology R Y
  funext p
  apply (rationalPointEquiv R Y).injective
  rw [rationalPointEquiv_natural]
  exact ((rationalPointEquiv R Y).apply_symm_apply _).symm

/-- Functoriality on actual identity-test points for the pinned evaluation topology. -/
theorem continuous_rationalPointMap (f : X ⟶ Y) :
    let : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
    let : TopologicalSpace (RationalPoint R Y) := rationalPointTopology R Y
    Continuous (fun p : RationalPoint R X => p ≫ f) := by
  let : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
  let : TopologicalSpace (RationalPoint R Y) := rationalPointTopology R Y
  rw [rationalPointMap_eq R f]
  exact (rationalPointHomeomorph R Y).symm.continuous.comp
    ((continuous_affineSchemePointMap R R f).comp
      (rationalPointHomeomorph R X).continuous)

/-- A closed immersion induces an embedding on actual identity-test points. -/
theorem isEmbedding_rationalPointMap
    (f : X ⟶ Y) [IsClosedImmersion f.left] :
    let : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
    let : TopologicalSpace (RationalPoint R Y) := rationalPointTopology R Y
    IsEmbedding (fun p : RationalPoint R X => p ≫ f) := by
  let : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
  let : TopologicalSpace (RationalPoint R Y) := rationalPointTopology R Y
  rw [rationalPointMap_eq R f]
  exact (rationalPointHomeomorph R Y).symm.isEmbedding.comp
    ((isEmbedding_affineSchemePointMap R R f).comp
      (rationalPointHomeomorph R X).isEmbedding)

/-- A closed immersion induces a closed embedding on actual identity-test points. -/
theorem isClosedEmbedding_rationalPointMap [T2Space R]
    (f : X ⟶ Y) [IsClosedImmersion f.left] :
    let : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
    let : TopologicalSpace (RationalPoint R Y) := rationalPointTopology R Y
    IsClosedEmbedding (fun p : RationalPoint R X => p ≫ f) := by
  let : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
  let : TopologicalSpace (RationalPoint R Y) := rationalPointTopology R Y
  rw [rationalPointMap_eq R f]
  exact (rationalPointHomeomorph R Y).symm.isClosedEmbedding.comp
    ((isClosedEmbedding_affineSchemePointMap R R f).comp
      (rationalPointHomeomorph R X).isClosedEmbedding)

/-- The actual subgroup of a closed represented subgroup functor is closed in
exactly the ambient identity-test point topology. -/
theorem isClosed_rationalPoint_subgroup [T2Space R]
    {G H : Langlands.GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]
    (S : Langlands.GroupScheme.SubgroupFunctor G) (i : H ⟶ G)
    (hi : S.IsRepresentedBy i) (hc : Langlands.GroupScheme.IsClosedSubgroup i) :
    let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
    IsClosed ((S.carrier (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
      Set (RationalPoint R G.X)) := by
  let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
  have : IsClosedImmersion i.hom.hom.left := hc
  have : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
  let : TopologicalSpace (RationalPoint R H.X) := rationalPointTopology R H.X
  have hr : Set.range (fun p : RationalPoint R H.X => p ≫ i.hom.hom) =
      (S.carrier (Over.mk (𝟙 (Spec (CommRingCat.of R)))) : Set (RationalPoint R G.X)) := by
    rw [← hi.2]
    rfl
  rw [← hr]
  exact (isClosedEmbedding_rationalPointMap R i.hom.hom).isClosed_range

/-- A closed representative's own point topology agrees with the actual
subgroup topology, and the canonical point identification preserves multiplication. -/
def rationalPointSubgroupHomeomorph
    {G H : Langlands.GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]
    (S : Langlands.GroupScheme.SubgroupFunctor G) (i : H ⟶ G)
    (hi : S.IsRepresentedBy i) (hc : Langlands.GroupScheme.IsClosedSubgroup i) :
    have : IsClosedImmersion i.hom.hom.left := hc
    have : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
    let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
    let : TopologicalSpace (RationalPoint R H.X) := rationalPointTopology R H.X
    RationalPoint R H.X ≃ₜ*
      S.carrier (Over.mk (𝟙 (Spec (CommRingCat.of R)))) := by
  have : IsClosedImmersion i.hom.hom.left := hc
  have : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
  let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
  let : TopologicalSpace (RationalPoint R H.X) := rationalPointTopology R H.X
  let e := hi.pointsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of R))))
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp
    (isEmbedding_rationalPointMap R i.hom.hom).isInducing
  exact { e, e.toEquiv.toHomeomorphOfIsInducing he with }

@[simp] theorem rationalPointSubgroupHomeomorph_apply_coe
    {G H : Langlands.GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]
    (S : Langlands.GroupScheme.SubgroupFunctor G) (i : H ⟶ G)
    (hi : S.IsRepresentedBy i) (hc : Langlands.GroupScheme.IsClosedSubgroup i)
    (p : RationalPoint R H.X) :
    (rationalPointSubgroupHomeomorph R S i hi hc p : RationalPoint R G.X) =
      p ≫ i.hom.hom := rfl

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Every closed subgroup of the actual rational-point group has compact open
subgroups cofinal among its open subgroups, for its subspace topology. -/
theorem rationalPoint_subgroup_compactOpenCofinal :
    let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ [IsTopologicalGroup (RationalPoint F G.X)]
      (S : Subgroup (RationalPoint F G.X)), IsClosed (S : Set (RationalPoint F G.X)) →
      ∀ K : OpenSubgroup S, ∃ L : OpenSubgroup S, IsCompact (L : Set S) ∧ L ≤ K := by
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  dsimp only
  intro _ S hS K
  have hG := Langlands.BruhatTits.rationalPoint_isLocallyProfinite F G
  let : T2Space (RationalPoint F G.X) := hG.t2Space
  let : LocallyCompactSpace (RationalPoint F G.X) := hG.locallyCompactSpace
  let : TotallyDisconnectedSpace (RationalPoint F G.X) := hG.totallyDisconnectedSpace
  let : LocallyCompactSpace S := hS.locallyCompactSpace
  have hSL : Langlands.Topology.IsLocallyProfinite S :=
    Langlands.Topology.isLocallyProfinite_of_mathlib
  exact (Langlands.Topology.LocallyProfiniteProof.vanDantzig S).mp hSL |>.2
    (K : Set S) (K.isOpen.mem_nhds K.one_mem)

/-- A closed represented subgroup of the actual rational-point group has the
compact-open cofinality required by the smooth-duality proofs. -/
theorem represented_rationalPoint_subgroup_compactOpenCofinal
    {H : Langlands.GroupScheme (Spec (CommRingCat.of F))}
    (S : Langlands.GroupScheme.SubgroupFunctor G) (i : H ⟶ G)
    (hi : S.IsRepresentedBy i) (hc : Langlands.GroupScheme.IsClosedSubgroup i) :
    let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ [IsTopologicalGroup (RationalPoint F G.X)],
      ∀ K : OpenSubgroup (S.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))),
        ∃ L : OpenSubgroup (S.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))),
          IsCompact (L : Set (S.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))) ∧ L ≤ K := by
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  dsimp only
  intro _
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  exact rationalPoint_subgroup_compactOpenCofinal F G _
    (isClosed_rationalPoint_subgroup F S i hi hc)

end LocalField

end Langlands.AlgebraicGeometry.PointTopology

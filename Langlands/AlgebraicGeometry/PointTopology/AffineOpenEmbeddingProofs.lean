import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMapProofs
import Langlands.AlgebraicGeometry.PointTopology.AffineOpenPoints

/-!
# Affine open point inclusion
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]
variable (X : Over (Spec (CommRingCat.of R)))

/-- The actual relative inclusion between nested open subschemes. -/
def openOverHomOfLE {U V : X.left.Opens} (h : U ≤ V) :
    openOver R X U ⟶ openOver R X V :=
  Over.homMk (X.left.homOfLE h) (by
    change X.left.homOfLE h ≫ (V.ι ≫ X.hom) = U.ι ≫ X.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

@[simp] theorem openOverHomOfLE_ι {U V : X.left.Opens} (h : U ≤ V) :
    openOverHomOfLE R X h ≫ openOverι R X V = openOverι R X U := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι X.left h

variable (S : Type u) [CommRing S] [Algebra R S] [TopologicalSpace S]

variable [IsAffine X.left]

/-- General affine open inclusions are open on points over a local value ring. -/
theorem isOpenMap_affineOpenPointMap [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S]
    (U : X.left.Opens) [IsAffine U] : IsOpenMap (openPointMap R X S U) := by
  intro W hW
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨p, hp, rfl⟩
  let x : U := p.left (IsLocalRing.closedPoint S)
  obtain ⟨f, hfU, hxf⟩ := (isAffineOpen_top X.left).exists_basicOpen_le x (by trivial)
  let D : X.left.Opens := X.left.basicOpen (U := ⊤) f
  let : IsAffine D := (isAffineOpen_top X.left).basicOpen f
  let F : openOver R X D ⟶ openOver R X U := openOverHomOfLE R X hfU
  let g : RingPoint R (openOver R X D) S → RingPoint R (openOver R X U) S :=
    fun q => q ≫ F
  have hg : Continuous g := continuous_affineSchemePointMap R S F
  have hgf : openPointMap R X S U ∘ g = openPointMap R X S D := by
    funext q
    dsimp only [RingPoint] at q
    apply RingPoint.ext
    let k : Spec (CommRingCat.of S) ⟶ D.toScheme := q.left
    change (k ≫ X.left.homOfLE hfU) ≫ U.ι = k ≫ D.ι
    rw [Category.assoc, Scheme.homOfLE_ι]
  have hr : Set.range (openPointMap R X S U p).left ⊆ D :=
    (range_subset_open_iff_closedPoint R X S D _).mpr hxf
  let q := openPointLift R X S D (openPointMap R X S U p) hr
  have hq : openPointMap R X S D q = openPointMap R X S U p :=
    openPointMap_lift R X S D _ hr
  have hpq : g q = p :=
    (openPointMap_injective R X S U) ((congrFun hgf q).trans hq)
  refine ⟨openPointMap R X S D '' (g ⁻¹' W), ?_, ?_, ?_⟩
  · rintro z ⟨r, hrW, rfl⟩
    exact ⟨g r, hrW, congrFun hgf r⟩
  · exact (isOpenEmbedding_basicOpenPointMap R X S f).isOpenMap _ (hW.preimage hg)
  · exact ⟨q, by change g q ∈ W; rw [hpq]; exact hp, hq⟩

/-- General affine open inclusions are open embeddings over a local value ring. -/
theorem isOpenEmbedding_affineOpenPointMap [IsLocalRing S] [ContinuousMul S] [IsOpenUnits S]
    (U : X.left.Opens) [IsAffine U] :
    IsOpenEmbedding (openPointMap R X S U) := by
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  exact ⟨continuous_affineSchemePointMap R S (openOverι R X U),
    openPointMap_injective R X S U, isOpenMap_affineOpenPointMap R X S U⟩

end Langlands.AlgebraicGeometry.PointTopology

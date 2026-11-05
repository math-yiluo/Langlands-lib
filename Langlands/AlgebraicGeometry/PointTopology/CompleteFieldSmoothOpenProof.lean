import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldSmoothOpenStatement
import Langlands.AlgebraicGeometry.PointTopology.SmoothAlgebraOpenProof
import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProofs

/-! # Smooth scheme maps are open on complete-field points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]

/-- On affine schemes, smooth openness transports through the actual global-section
point homeomorphisms. -/
theorem isOpenMap_affineSmoothPointMap
    {X Y : Over (Spec (CommRingCat.of K))} [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) [Smooth f.left] :
    IsOpenMap (X := RingPoint K X K) (Y := RingPoint K Y K)
      (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K)) := by
  let A : Type u := AffineCoordinateRing K Y
  let B : Type u := AffineCoordinateRing K X
  let phi : A →ₐ[K] B := affineCoordinatePullback K f
  let : Algebra A B := phi.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq
    (fun k => (phi.commutes k).symm)
  have hs : RingHom.Smooth f.left.appTop.hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth) (f := f.left)).mp inferInstance
  let : Algebra.Smooth A B := hs
  have hopen : IsOpenMap (AlgPoint.precomp (S := K) phi) := by
    have h := smoothAlgebraPointOpen K A B
    have hphi : IsScalarTower.toAlgHom K A B = phi := by
      ext a
      rfl
    rwa [hphi] at h
  have heq : (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K)) =
      (affineSchemePointHomeomorph K Y K).symm ∘ AlgPoint.precomp phi ∘
        (affineSchemePointHomeomorph K X K) := by
    funext p
    apply (affineSchemePointEquiv K Y K).injective
    change affineSchemePointEquiv K Y K (p ≫ f) =
      (affineSchemePointEquiv K Y K)
        ((affineSchemePointEquiv K Y K).symm
          (AlgPoint.precomp phi (affineSchemePointEquiv K X K p)))
    rw [Equiv.apply_symm_apply]
    exact affineSchemePointEquiv_natural K K f p
  rw [heq]
  exact (affineSchemePointHomeomorph K Y K).symm.isOpenMap.comp
    (hopen.comp (affineSchemePointHomeomorph K X K).isOpenMap)

/-- Smooth openness glues from affine source and target charts. No finiteness
hypothesis on the structure morphisms is needed for this derived helper. -/
theorem isOpenMap_smoothSchemePointMap
    {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y) [Smooth f.left] :
    letI : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
    letI : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
    IsOpenMap (X := RingPoint K X K) (Y := RingPoint K Y K)
      (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K)) := by
  let : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
  let : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
  let g : RingPoint K X K → RingPoint K Y K := fun p => p ≫ f
  change IsOpenMap g
  intro W hW
  apply isOpen_iff_forall_mem_open.mpr
  rintro y ⟨p, hpW, rfl⟩
  obtain ⟨V, hV, hpV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y.left) (x := f.left (p.left (IsLocalRing.closedPoint K)))
    (U := ⊤) (by trivial)
  let : IsAffine V := hV
  have hpPre : p.left (IsLocalRing.closedPoint K) ∈ f.left ⁻¹ᵁ V := hpV
  obtain ⟨D, hD, hpD, hDPre⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.left) (x := p.left (IsLocalRing.closedPoint K))
    (U := f.left ⁻¹ᵁ V) hpPre
  let : IsAffine D := hD
  have hDV : D ≤ f.left ⁻¹ᵁ V := hDPre
  let F : openOver K X D ⟶ openOver K Y V :=
    Over.homMk (f.left.resLE V D hDV) (by
      change f.left.resLE V D hDV ≫ (V.ι ≫ Y.hom) = D.ι ≫ X.hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w f])
  have hF : F ≫ openOverι K Y V = openOverι K X D ≫ f := by
    apply Over.OverMorphism.ext
    change f.left.resLE V D hDV ≫ V.ι = D.ι ≫ f.left
    exact Scheme.Hom.resLE_comp_ι f.left hDV
  let : Smooth F.left := inferInstanceAs (Smooth (f.left.resLE V D hDV))
  let k : RingPoint K (openOver K X D) K → RingPoint K (openOver K Y V) K :=
    fun q => q ≫ F
  have hk : IsOpenMap k := isOpenMap_affineSmoothPointMap K F
  have hcD : Continuous (X := RingPoint K (openOver K X D) K)
      (Y := RingPoint K X K) (openPointMap K X K D) :=
    schemePointTopology_continuous_chart K X K ⟨D, hD⟩
  have hfg : openPointMap K Y K V ∘ k = g ∘ openPointMap K X K D := by
    funext q
    dsimp only [RingPoint] at q
    change (q ≫ F) ≫ openOverι K Y V = (q ≫ openOverι K X D) ≫ f
    exact (Category.assoc q _ _).trans
      ((congrArg (fun t => q ≫ t) hF).trans (Category.assoc q _ _).symm)
  have hr : Set.range p.left ⊆ D :=
    (range_subset_open_iff_closedPoint K X K D p).mpr hpD
  let q := openPointLift K X K D p hr
  have hq : openPointMap K X K D q = p := openPointMap_lift K X K D p hr
  refine ⟨openPointMap K Y K V '' (k '' (openPointMap K X K D ⁻¹' W)), ?_, ?_, ?_⟩
  · rintro z ⟨t, ⟨s, hsW, rfl⟩, rfl⟩
    exact ⟨openPointMap K X K D s, hsW, (congrFun hfg s).symm⟩
  · exact (isOpenEmbedding_schemeAffineChart K K Y ⟨V, hV⟩).isOpenMap _
      (hk _ (hW.preimage hcD))
  · refine ⟨k q, ⟨q, ?_, rfl⟩, ?_⟩
    · change openPointMap K X K D q ∈ W
      rwa [hq]
    · exact (congrFun hfg q).trans (congrArg g hq)

/-- Conrad's local smooth-openness assertion on the actual scheme-point spaces. -/
theorem completeFieldSmoothPointOpen : CompleteFieldSmoothPointOpenStatement.{u} := by
  intro K _ _ X Y _ _ f _
  exact isOpenMap_smoothSchemePointMap K f

end Langlands.AlgebraicGeometry.PointTopology

import Langlands.GroupScheme.Absolute.BorelConjugateCoverProof
import Langlands.GroupScheme.AffineHomImageProof
import Langlands.GroupScheme.ConnectedKernelGeometry
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.Torus.WeylGroupSchemeQuotientPoints
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Rational points and connected kernels of affine group homomorphisms -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SemisimpleCentralizer

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A morphism of affine schemes of finite type over an algebraically closed field is
surjective if every rational point of the target lifts. -/
theorem surjective_of_rational_lifts {X Y : Over (Spec (CommRingCat.of k))}
    [IsAffineHom X.hom] [IsAffineHom Y.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y)
    (hf : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y,
      ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, x ≫ f = y) :
    Surjective f.left := by
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hconstructible : IsConstructible (Set.range f.left) := by
    rw [← Set.image_univ]
    exact f.left.isConstructible_image .univ
  have hclosed : (Set.range f.left)ᶜ ∩ closedPoints Y.left = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hzc⟩
    obtain ⟨y, hy⟩ := Langlands.AlgebraicGeometry.ClosedRationalPoints.exists_rationalPoint_of_isClosed z hzc
    obtain ⟨x, hx⟩ := hf y
    exact hz ⟨x.left (IsLocalRing.closedPoint k), by
      rw [← hy, ← hx]
      rfl⟩
  have he := BorelConjugateCover.eq_empty_of_isConstructible_of_inter_closedPoints
    hconstructible.compl hclosed
  exact ⟨Set.range_eq_univ.mp (Set.compl_empty_iff.mp he)⟩

variable {G Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]

omit [IsAlgClosed k] in
/-- The image on underlying spaces of a homomorphism of affine algebraic groups is closed. -/
theorem isClosed_range (q : G ⟶ Q) : IsClosed (Set.range q.hom.hom.left) := by
  obtain ⟨I, p, i, _, _, hi, hpi, hp⟩ := affineHomImage k G Q q
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Surjective p.hom.hom.left := hp.2.1
  rw [← hpi]
  change IsClosed (Set.range (i.hom.hom.left ∘ p.hom.hom.left))
  rw [Function.Surjective.range_comp p.hom.hom.left.surjective]
  exact i.hom.hom.left.isClosedEmbedding.isClosed_range

/-- Connected target and connected full kernel imply connected source for a homomorphism
surjective on rational points. Its fppf image has the same underlying space as the target. -/
theorem connectedSpace_of_rational_surjective (q : G ⟶ Q) [ConnectedSpace Q.X.left]
    (hq : Function.Surjective (rationalPoints.map q))
    (hk : ConnectedSpace (kernel q).X.left) : ConnectedSpace G.X.left := by
  have hsurj := surjective_of_rational_lifts q.hom.hom hq
  obtain ⟨I, p, i, hIft, hIa, hi, hpi, hp⟩ := affineHomImage k G Q q
  have : IsClosedImmersion i.hom.hom.left := hi
  have hiS : Function.Surjective i.hom.hom.left := by
    rw [← hpi] at hsurj
    intro y
    obtain ⟨x, hx⟩ := hsurj.surj y
    exact ⟨p.hom.hom.left x, hx⟩
  have : ConnectedSpace I.X.left :=
    (i.hom.hom.left.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective hiS).connectedSpace_iff.2
      inferInstance
  have hkq : IsClosedSubgroup (kernelι q) := kernelι_isClosedImmersion q
  have : LocallyOfFiniteType (kernel q).X.hom := hkq.locallyOfFiniteType
  have : IsAffineHom (kernel q).X.hom := hkq.isAffineHom
  have : ConnectedSpace (kernel q).X.left := hk
  have : GeometricallyConnected (kernel q).X.hom := geometricallyConnected_of_connected (kernel q)
  have : GeometricallyConnected (kernel p).X.hom :=
    KernelRepresentative.geometricallyConnected p (kernelι q) hp.2.2.2
  have : Surjective p.hom.hom.left := hp.2.1
  have : Flat p.hom.hom.left := hp.1
  have : LocallyOfFinitePresentation p.hom.hom.left := hp.2.2.1
  have := geometricallyConnected_of_geometricallyConnected_kernel p
  exact GeometricallyConnected.connectedSpace (f := p.hom.hom.left) p.hom.hom.left.isOpenMap

omit [IsAffineHom G.X.hom] in
/-- An algebraic group with only the identity rational point is connected. -/
theorem connectedSpace_of_points_eq_one (h : ∀ x : rationalPoints G, x = 1) :
    ConnectedSpace G.X.left := by
  have hs := Langlands.AlgebraicGeometry.ClosedRationalPoints.subset_singleton_of_rationalPoints
    (X := G.X) (Z := Set.univ) isOpen_univ.isLocallyClosed (1 : rationalPoints G) (fun x _ => h x)
  have hU := Set.Subset.antisymm hs (Set.subset_univ _)
  rw [connectedSpace_iff_univ, hU]
  exact isConnected_singleton

end Langlands.GroupScheme.SemisimpleCentralizer

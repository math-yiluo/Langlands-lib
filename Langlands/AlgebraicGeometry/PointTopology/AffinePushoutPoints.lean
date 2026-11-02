import Langlands.AlgebraicGeometry.PointTopology.AffineAlgebraPushouts
import Langlands.AlgebraicGeometry.PointTopology.AffineTensorPointFibers

/-!
# Actual points of arbitrary algebra pushouts
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- The actual point comparison associated to a pushout cocone. -/
def affinePushoutPointComparison {A B C : CommAlgCat.{u} R}
    {f : C ⟶ A} {g : C ⟶ B} (c : PushoutCocone f g)
    (p : AlgPoint R c.pt S) :
    {q : AlgPoint R A S × AlgPoint R B S //
      AlgPoint.precomp f.hom q.1 = AlgPoint.precomp g.hom q.2} :=
  ⟨(AlgPoint.precomp c.inl.hom p, AlgPoint.precomp c.inr.hom p), by
    apply AlgPoint.ext
    intro a
    exact congrArg (fun h => p (h.hom a)) c.condition⟩

variable [TopologicalSpace S] [IsTopologicalRing S]

/-- Every actual algebra pushout yields the compatible-pair homeomorphism.
The value ring may be in a universe independent of the category. -/
def affinePushoutPointHomeomorph {A B C : CommAlgCat.{u} R}
    {f : C ⟶ A} {g : C ⟶ B} (c : PushoutCocone f g) (hc : IsColimit c) :
    AlgPoint R c.pt S ≃ₜ
      {q : AlgPoint R A S × AlgPoint R B S //
        AlgPoint.precomp f.hom q.1 = AlgPoint.precomp g.hom q.2} := by
  letI : Algebra C A := f.hom.toRingHom.toAlgebra
  letI : Algebra C B := g.hom.toRingHom.toAlgebra
  letI : IsScalarTower R C A := IsScalarTower.of_algHom f.hom
  letI : IsScalarTower R C B := IsScalarTower.of_algHom g.hom
  let t : PushoutCocone f g := affineTensorPushout R C A B
  let ht : IsColimit t := affineTensorPushoutIsColimit R C A B
  let i : t.pt ≅ c.pt := ht.coconePointUniqueUpToIso hc
  let e : t.pt ≃ₐ[R] c.pt := CommAlgCat.algEquivOfIso i
  let H : AlgPoint R c.pt S ≃ₜ CompatibleAlgPointPair R C A B S :=
    (AlgPoint.congr e.symm).trans (tensorFiberPointHomeomorph R C A B S)
  have hi₁ : t.inl ≫ i.hom = c.inl :=
    ht.comp_coconePointUniqueUpToIso_hom hc WalkingSpan.left
  have hi₂ : t.inr ≫ i.hom = c.inr :=
    ht.comp_coconePointUniqueUpToIso_hom hc WalkingSpan.right
  have h : (fun p => H p) = affinePushoutPointComparison R S c := by
    funext p
    apply Subtype.ext
    apply Prod.ext
    · apply AlgPoint.ext
      intro a
      exact congrArg (fun k => p (k.hom a)) hi₁
    · apply AlgPoint.ext
      intro b
      exact congrArg (fun k => p (k.hom b)) hi₂
  exact IsHomeomorph.homeomorph (affinePushoutPointComparison R S c)
    (by rw [← h]; exact H.isHomeomorph)

@[simp] theorem affinePushoutPointHomeomorph_apply
    {A B C : CommAlgCat.{u} R} {f : C ⟶ A} {g : C ⟶ B}
    (c : PushoutCocone f g) (hc : IsColimit c) (p : AlgPoint R c.pt S) :
    affinePushoutPointHomeomorph R S c hc p =
      affinePushoutPointComparison R S c p := rfl

end Langlands.AlgebraicGeometry.PointTopology

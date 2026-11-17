import Langlands.GroupScheme.AffineWeilFiniteFamily
import Langlands.GroupScheme.Reductive.FiniteProductCenter
import Langlands.GroupScheme.Reductive.GeometricNontrivial

/-! # Adjoint Weil presentations from supplied finite products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {I : Type u} [Finite I]

/-- A finite product with a nonidentity point has a nonempty factor index. -/
theorem nonempty_index_of_hasNontrivialPoint_pi (H : I → GroupScheme S)
    (h : HasNontrivialPoint (pi H)) : Nonempty I := by
  classical
  by_contra hi
  let : IsEmpty I := ⟨fun i => hi ⟨i⟩⟩
  obtain ⟨T, x, hx⟩ := h
  apply hx
  apply (piPointsEquiv H T).injective
  exact Subsingleton.elim _ _

variable {A : Type u} [CommRing A]

/-- An actual finite étale Weil presentation with adjoint almost-simple
geometric factors, including the surjectivity of the finite base. -/
structure AffineAdjointWeilPresentation (G : GroupScheme (Spec (CommRingCat.of A))) where
  ring : Type u
  [commRing : CommRing ring]
  [algebra : Algebra A ring]
  [finite : Module.Finite A ring]
  [projective : Module.Projective A ring]
  [etale : Algebra.Etale A ring]
  group : GroupScheme (Spec (CommRingCat.of ring))
  [isAffine : IsAffine group.X.left]
  [locallyOfFiniteType : LocallyOfFiniteType group.X.hom]
  surjective : Surjective (algebraBaseMap A ring)
  reductive : IsReductive group
  fibres : ∀ s : Spec (CommRingCat.of ring),
    IsAdjoint (geometricFiber group s) ∧ IsAlmostSimple (geometricFiber group s)
  iso : G ≅ AffineWeil.groupScheme A ring group

attribute [instance] AffineAdjointWeilPresentation.commRing AffineAdjointWeilPresentation.algebra
  AffineAdjointWeilPresentation.finite AffineAdjointWeilPresentation.projective
  AffineAdjointWeilPresentation.etale AffineAdjointWeilPresentation.isAffine
  AffineAdjointWeilPresentation.locallyOfFiniteType

namespace AffineAdjointWeilPresentation

variable {G : GroupScheme (Spec (CommRingCat.of A))}

/-- Forgetting the supplied data gives precisely the existential form
used by the published affine adjoint Weil-restriction target. -/
theorem exists_pair (P : AffineAdjointWeilPresentation G) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B)
      (_ : Module.Projective A B) (_ : Algebra.Etale A B)
      (G' : GroupScheme (Spec (CommRingCat.of B)))
      (_ : IsAffine G'.X.left) (_ : LocallyOfFiniteType G'.X.hom),
      Surjective (algebraBaseMap A B) ∧ IsReductive G' ∧
        (∀ s : Spec (CommRingCat.of B),
          IsAdjoint (geometricFiber G' s) ∧ IsAlmostSimple (geometricFiber G' s)) ∧
        Nonempty (G ≅ AffineWeil.groupScheme A B G') :=
  ⟨P.ring, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    P.group, inferInstance, inferInstance, P.surjective, P.reductive, P.fibres, ⟨P.iso⟩⟩

/-- Nontrivial geometric fibres of a supplied product force the spectrum
of its finite product ring to cover the base, including the empty base. -/
theorem surjective_productBase (H : I → GroupScheme (Spec (CommRingCat.of A)))
    (e : G ≅ pi H) (hnt : IsFibrewiseNontrivial G) :
    Surjective (algebraBaseMap A (I → A)) := by
  constructor
  intro s
  have hn : HasNontrivialPoint G :=
    (hnt s).of_baseChange (geometricPoint (Spec (CommRingCat.of A)) s)
  let : Nonempty I := nonempty_index_of_hasNontrivialPoint_pi H (hn.of_iso e)
  let : Surjective (algebraBaseMap A (I → A)) :=
    AffineWeil.FiniteFamily.surjective_baseMap A I
  exact (algebraBaseMap A (I → A)).surjective s

/-- A supplied finite almost-simple product of a centre-free group with
nontrivial geometric fibres gives its actual adjoint Weil presentation. -/
def ofProduct (H : I → GroupScheme (Spec (CommRingCat.of A)))
    (e : G ≅ pi H) (hc : center G = ⊥) (hnt : IsFibrewiseNontrivial G)
    (hred : ∀ i, IsReductive (H i))
    (hAS : ∀ i, ∀ s : Spec (CommRingCat.of A), IsAlmostSimple (geometricFiber (H i) s)) :
    AffineAdjointWeilPresentation G := by
  let : ∀ i, IsAffine (H i).X.left :=
    fun i => @isAffine_of_isAffineHom _ _ (H i).X.hom (hred i).isAffineHom inferInstance
  let : ∀ i, Smooth (H i).X.hom := fun i => (hred i).smooth
  let : ∀ i, LocallyOfFiniteType (H i).X.hom := fun _ => inferInstance
  have hadj : ∀ i, IsFibrewiseAdjoint (H i) :=
    isAdjoint_geometricFactor_of_productIso H e hc hAS
  exact
    { ring := I → A
      group := AffineWeil.FiniteFamily.group A I H
      surjective := surjective_productBase H e hnt
      reductive := AffineWeil.FiniteFamily.isReductive A I H hred
      fibres := fun s => ⟨AffineWeil.FiniteFamily.isFibrewiseAdjoint A I H hadj s,
        AffineWeil.FiniteFamily.isFibrewiseAlmostSimple A I H hAS s⟩
      iso := e ≪≫ AffineWeil.FiniteFamily.iso A I H }

end AffineAdjointWeilPresentation

end Langlands.GroupScheme

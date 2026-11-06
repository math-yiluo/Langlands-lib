import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # Pinnings on actual split connected reductive groups over fields -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {J : Type u}

/-- Trivializations of the actual simple-root Lie weight spaces. The relation of
`P` to the roots of the group is supplied separately by `IsRootDatumOf`. -/
structure RootPinning (i : T.toGrp ⟶ G)
    (P : RootDatum J (characterLattice T) (cocharacterLattice T)) (b : P.Base) where
  trivialization : ∀ a : b.support, k ≃ₗ[k] weightSpace i (P.root a)

namespace RootPinning

variable {i : T.toGrp ⟶ G}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)} {b : P.Base}
  (p : RootPinning i P b)

/-- The chosen simple-root vector, as an element of the actual Lie algebra. -/
def rootVector (a : b.support) : Additive (lieKernel G (CommRingCat.of k)) :=
  (p.trivialization a 1).val

theorem rootVector_mem (a : b.support) :
    p.rootVector a ∈ weightSpace i (P.root a) :=
  (p.trivialization a 1).property

theorem rootVector_ne_zero (a : b.support) : p.rootVector a ≠ 0 := by
  intro h
  have he : p.trivialization a 1 = p.trivialization a 0 := by
    apply Subtype.ext
    rw [(p.trivialization a).map_zero]
    exact h
  exact one_ne_zero ((p.trivialization a).injective he)

/-- Evaluation of the trivialization is scalar multiplication by the root vector. -/
theorem trivialization_apply_val (a : b.support) (c : k) :
    (p.trivialization a c).val = c • p.rootVector a := by
  have h : p.trivialization a c = c • p.trivialization a 1 := by
    simpa only [smul_eq_mul, mul_one] using (p.trivialization a).map_smul c (1 : k)
  exact congrArg Subtype.val h

end RootPinning

/-- A field pinning with its actual split maximal torus, finite reduced root datum
and simple-root Lie trivializations. No existence is included in this definition. -/
structure SplitPinning (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] where
  isConnectedReductive : IsConnectedReductive G
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ G
  isSplitTorus : IsSplitTorus torus.toGrp
  isMaximalTorus : IsMaximalTorus inclusion
  rootIndex : Type u
  [finiteRootIndex : Finite rootIndex]
  rootDatum : RootDatum rootIndex (characterLattice torus) (cocharacterLattice torus)
  isRootDatum : IsRootDatumOf inclusion rootDatum
  isReduced : rootDatum.IsReduced
  base : rootDatum.Base
  pinning : RootPinning inclusion rootDatum base

attribute [instance] SplitPinning.finiteRootIndex

namespace SplitPinning

variable {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

/-- An actual pinned isomorphism carries the tori, all roots and coroots, the
simple-root supports, and the chosen Lie vectors to one another. -/
structure Iso (p : SplitPinning G) (q : SplitPinning H) where
  torusIso : p.torus ≅ q.torus
  groupIso : G ≅ H
  square : p.inclusion ≫ groupIso.hom =
    CommGroupScheme.groupHom torusIso.hom ≫ q.inclusion
  indexEquiv : p.rootIndex ≃ q.rootIndex
  root_eq : ∀ a, characterLattice.congr torusIso (p.rootDatum.root a) =
    q.rootDatum.root (indexEquiv a)
  coroot_eq : ∀ a, cocharacterLattice.congr torusIso (p.rootDatum.coroot a) =
    q.rootDatum.coroot (indexEquiv a)
  simple_iff : ∀ a, a ∈ p.base.support ↔ indexEquiv a ∈ q.base.support
  rootVector_eq : ∀ a : p.base.support,
    Lie.targetMapLinear groupIso.hom (CommRingCat.of k) (p.pinning.rootVector a) =
      q.pinning.rootVector ⟨indexEquiv a, (simple_iff a).mp a.property⟩

end SplitPinning

end Langlands.GroupScheme

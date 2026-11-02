import Langlands.GroupScheme.Rational.RelativeRoots
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-! # Statements: the relative root system, the rational Bruhat decomposition and generic
centralizers -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The relative root system of `i`, possibly nonreduced: on `V = relativeRootSpan i` there is a
crystallographic Mathlib root system indexed by a finite type, whose pairing is the evaluation
pairing of `V` with its dual, whose roots are exactly the images `1 ⊗ α` of the relative roots
`α`, and whose Weyl group has image in `GL(V)` equal to the range of the injective
`relativeWeylAction i`. -/
def HasRelativeRootSystem (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom] :
    Prop :=
  ∃ (J : Type u) (_ : Finite J)
    (P : RootPairing J ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i))),
    P.IsRootSystem ∧ P.IsCrystallographic ∧
    P.toLinearMap = Module.Dual.eval ℚ (relativeRootSpan i) ∧
    Subtype.val '' Set.range P.root = toRat '' relativeRoots i ∧
    P.weylGroup.map (RootPairing.Equiv.weightHom P) = (relativeWeylAction i).range ∧
    Function.Injective (relativeWeylAction i)

/-- The rational Bruhat decomposition for `i` and the cocharacter `ν`, with
`P(k) = (Dynamic.parabolic (ν ≫ i))(k)`: every point of `G(k)` lies in a double coset
`P(k) n P(k)` with `n` normalizing `i`, and two normalizing points lie in the same double coset
exactly when they have the same class in `relativeWeylGroup i`. -/
def HasRationalBruhatDecomposition (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) : Prop :=
  (∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, ∃ n ∈ normalizerPoints i,
    ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
    ∃ q ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
      g = p * n * q) ∧
  ∀ n n' : normalizerPoints i,
    (∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
      ∃ q ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
        (n' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) = p * n * q) ↔
      (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk n'

/-- **The relative root system** (Milne 25.16–25.17, Borel–Tits 5.8 with 5.1–5.3). For a
maximal split torus `i` of a connected reductive group `G` over a field, the relative roots form
a root system, possibly nonreduced, in the `ℚ`-span of their images, and the relative Weyl group
acts faithfully on that span with image the Weyl group of this root system. -/
def RelativeRootSystemStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    HasRelativeRootSystem i

/-- **The rational Bruhat decomposition** (Milne 25.27, Borel–Tits 5.15). For a maximal split
torus `i` of a connected reductive group `G` over a field and a generic cocharacter `ν` of it,
`G(k)` is the union of the double cosets `P(k) n P(k)` of the rational parabolic
`P = Dynamic.parabolic (ν ≫ i)` over the normalizing points `n`, and these double cosets are
indexed by the relative Weyl group. -/
def RationalBruhatStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i → ∀ ν : cocharacterLattice T,
    haveI := hG.isAffineHom
    IsGenericCocharacter i ν → HasRationalBruhatDecomposition i ν

/-- **Generic centralizers** (Borel–Tits 4.15 a), Milne 25.6). For a maximal split torus `i` of a
connected reductive group `G` over a field and a generic cocharacter `ν` of it, the dynamic Levi
subgroup `Dynamic.centralizer (ν ≫ i)` is the centralizer of the whole torus. -/
def GenericCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i → ∀ ν : cocharacterLattice T,
    haveI := hG.isAffineHom
    IsGenericCocharacter i ν →
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i

end Langlands.GroupScheme

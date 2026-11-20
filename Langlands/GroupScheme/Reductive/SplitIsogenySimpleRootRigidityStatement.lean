import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Isogenies of split reductive groups are determined by `T` and the simple root groups
(Milne 21.63) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 21.63: let `(G, T)` and `(G', T')` be split reductive groups over a
field `k`, with split maximal tori `i : T ⟶ G` and `i' : T' ⟶ G'`, and let `ν` be a generic
cocharacter of `T`, which determines the base `simpleRelativeRoots i ν` of the roots. Two
isogenies `φ₁ φ₂ : G ⟶ G'` of split reductive groups (surjective, finite kernel, `T` mapped
into `T'`) that agree on `T` and on every root subgroup `RelativeRoot.subgroup i α` with `α`
simple are equal. -/
def SplitIsogenySimpleRootRigidityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G), IsConnectedReductive G' →
    ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (i' : T'.toGrp ⟶ G'),
      IsSplitTorus T.toGrp → IsMaximalTorus i → IsSplitTorus T'.toGrp → IsMaximalTorus i' →
      haveI := hG.isAffineHom
      ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
        let IsSplitIsogeny : (G ⟶ G') → Prop := fun φ =>
          Surjective φ.hom.hom.left ∧ IsFinite (kernel φ).X.hom ∧
            ∃ f : T.toGrp ⟶ T'.toGrp, f ≫ i' = i ≫ φ
        ∀ φ₁ φ₂ : G ⟶ G', IsSplitIsogeny φ₁ → IsSplitIsogeny φ₂ →
          i ≫ φ₁ = i ≫ φ₂ →
          (∀ α ∈ simpleRelativeRoots i ν, ∀ (X : Over (Spec (CommRingCat.of k)))
              (g : X ⟶ G.X), g ∈ (RelativeRoot.subgroup i α).carrier X →
                g ≫ φ₁.hom.hom = g ≫ φ₂.hom.hom) →
            φ₁ = φ₂

end Langlands.GroupScheme

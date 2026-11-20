import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Isogenies of split reductive groups with the same root characters agree on the torus
(Milne 23.8, corrected) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 23.8, in corrected form: let `(G, T)` and `(G', T')` be split
reductive groups over a field `k`, one of them semisimple, and let `φ₁ φ₂ : G ⟶ G'` be
isogenies (surjective, finite kernel) that map `T` into `T'` through `t₁ t₂ : T ⟶ T'`. If the
character maps of `t₁` and `t₂` agree on every root of `T'`, then `φ₁` and `φ₂` agree on `T`.
Milne's hypothesis that `φ₁` and `φ₂` only induce the same correspondence of roots is not
enough in positive characteristic (the identity and the Frobenius isogeny of `SL₂`). -/
def SplitIsogenyTorusRigidityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G'),
    IsSemisimple G ∨ IsSemisimple G' →
    ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (i' : T'.toGrp ⟶ G'),
      IsSplitTorus T.toGrp → IsMaximalTorus i → IsSplitTorus T'.toGrp → IsMaximalTorus i' →
      haveI := hG.isAffineHom
      haveI := hG'.isAffineHom
      ∀ (φ₁ φ₂ : G ⟶ G') (t₁ t₂ : T ⟶ T'),
        Surjective φ₁.hom.hom.left → IsFinite (kernel φ₁).X.hom →
        CommGroupScheme.groupHom t₁ ≫ i' = i ≫ φ₁ →
        Surjective φ₂.hom.hom.left → IsFinite (kernel φ₂).X.hom →
        CommGroupScheme.groupHom t₂ ≫ i' = i ≫ φ₂ →
        (∀ α' ∈ roots i', t₁ ≫ α' = t₂ ≫ α') →
          i ≫ φ₁ = i ≫ φ₂

end Langlands.GroupScheme

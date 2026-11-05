import Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterStatement
import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # Actual cocenter character restriction and based-root Galois descent -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace characterLattice

/-- Pull back actual characters along the base change of a descended
commutative-group homomorphism. -/
def baseChangePullback (k E : Type u) [Field k] [Field E] [Algebra k E]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))} (g : T ⟶ Q) :
    characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj Q) →ₗ[ℤ]
      characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) :=
  (precompose ((CommGroupScheme.baseChange (algebraBaseMap k E)).map g)).toIntLinearMap

/-- Actual character pullback commutes with the ordinary Galois action. -/
theorem baseChangePullback_galois (k E : Type u) [Field k] [Field E] [Algebra k E]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))} (g : T ⟶ Q)
    (σ : E ≃ₐ[k] E)
    (x : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj Q)) :
    baseChangePullback k E g (galoisRepresentation k E Q σ x) =
      galoisRepresentation k E T σ (baseChangePullback k E g x) :=
  (galoisRepresentation_precompose k E g σ x).symm

end characterLattice

/-- Root-theoretic descent data for an actual cocenter character pullback:
its image annihilates the selected simple coroots, and pairing-preserving
twisted Galois maps permute all simple coroots while preserving the selection.
The character corrections fix the entire actual pullback image. -/
def CocenterRootDescentData (k E : Type u) [Field k] [Field E] [Algebra k E]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))} (g : T ⟶ Q)
    {J : Type u}
    (P : RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)))
    (B : P.Base) (s : Set B.support) : Prop :=
  let f := characterLattice.baseChangePullback k E g
  Function.Injective f ∧
    (∀ x, x ∈ f.range ↔ ∀ i ∈ s, P.toLinearMap x (P.coroot i) = 0) ∧
    ∃ (w : (E ≃ₐ[k] E) →
        characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) →ₗ[ℤ]
          characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (v : (E ≃ₐ[k] E) →
        cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) →ₗ[ℤ]
          cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (e : (E ≃ₐ[k] E) → Equiv.Perm B.support),
      (∀ σ x, w σ (f x) = f x) ∧
      (∀ σ x y,
        P.toLinearMap
          (w σ (characterLattice.galoisRepresentation k E T σ x))
          (v σ (cocharacterLattice.galoisRepresentation k E T σ y)) =
            P.toLinearMap x y) ∧
      (∀ σ (i : B.support),
        v σ (cocharacterLattice.galoisRepresentation k E T σ (P.coroot i)) =
          P.coroot (e σ i)) ∧
      (∀ σ (i : B.support), i ∈ s ↔ e σ i ∈ s)

/-- A root model of the actual cocenter of a split-torus centralizer, for
arbitrary connected reductive groups. Simple connectedness and integral
coroot generation are not assumptions or conclusions of this statement. -/
def SplitTorusCentralizerCocenterRootModelStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G),
    IsSplitSubtorus a →
    ∀ (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
      (torusCentralizer a).IsRepresentedBy j → IsConnectedReductive M →
    ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ M),
      IsDerivedSubgroup d →
    ∀ (Q : CommGroupScheme (Spec (CommRingCat.of k))) (q : M ⟶ Q.toGrp),
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q → IsTorus Q.toGrp →
      haveI := hG.isAffineHom
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ M),
        IsMaximalTorus t ∧
        ∃ (E : Type u) (_ : Field E) (_ : Algebra k E),
          FiniteDimensional k E ∧ IsGalois k E ∧
          IsSplitTorus (GaloisPointComparison.baseChanged k E T.toGrp) ∧
          IsSplitTorus (GaloisPointComparison.baseChanged k E Q.toGrp) ∧
          haveI : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom :=
            MorphismProperty.baseChange_obj (P := @IsAffineHom)
              (algebraBaseMap k E) G.X hG.isAffineHom
          IsMaximalTorus
            (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
            ((GroupScheme.baseChange (algebraBaseMap k E)).map (t ≫ j)) ∧
          ∃ (J : Type u) (_ : Finite J)
            (P : RootDatum J
              (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
              (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))),
            IsRootDatumOf
              (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
              ((GroupScheme.baseChange (algebraBaseMap k E)).map (t ≫ j)) P ∧
            P.IsReduced ∧
            ∃ (B : P.Base) (s : Set B.support),
              CocenterRootDescentData k E (Additive.ofMul (t ≫ q) : T ⟶ Q) P B s

end Langlands.GroupScheme

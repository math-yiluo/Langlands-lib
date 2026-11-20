import Langlands.GroupScheme.Rational.StandardLeviWeylStatements

/-! # Maximal standard Levi transporter cosets on rational points -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology

/-- The point-side count and opposite-parabolic comparison in the opening of Renard VII.1.3. -/
def MaximalStandardLeviPointCosetsStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
    ∀ I : Finset (SimpleRoot i ν),
      let conj : RationalPoint k G.X → (RationalPoint k G.X →* RationalPoint k G.X) :=
        fun g => MulAut.conj g
      let pointCosets : Set (RationalPoint k G.X ⧸ levi i ν I) :=
        QuotientGroup.mk '' {g | ∃ J : Finset (SimpleRoot i ν),
          (levi i ν I).map (conj g) = levi i ν J}
      let isMaximal : Prop :=
        parabolic i ν I ≠ ⊤ ∧
          ∀ J : Finset (SimpleRoot i ν), parabolic i ν I < parabolic i ν J →
            parabolic i ν J = ⊤
      (isMaximal ↔ Nat.card pointCosets = 2) ∧
        (isMaximal →
          ∀ (g : RationalPoint k G.X) (J : Finset (SimpleRoot i ν)),
            g ∉ levi i ν I →
            (levi i ν I).map (conj g) = levi i ν J →
            ∀ ζ : cocharacterLattice T, IsStandardCocharacter i ν (rootSet i ν J) ζ →
              (parabolic i ν I).map (conj g) =
                (Dynamic.parabolic (CommGroupScheme.groupHom (-ζ) ≫ i)).carrier
                  (Over.mk (𝟙 _)))

end Langlands.GroupScheme

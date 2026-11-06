import Langlands.AbelianScheme.GroupScheme
import Langlands.AbelianScheme.Tate.FiniteMonodromy
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Realization of invariant subgroups of finite étale group schemes -/

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- A monodromy-invariant subgroup of the actual geometric points of a finite
étale commutative group scheme is the exact image of an actual finite étale
closed subgroup scheme. This is a statement target, not a proof. -/
def InvariantSubgroupRealizationStatement : Prop :=
  ∀ (S : Scheme.{u}) [ConnectedSpace S] [IsLocallyNoetherian S]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ S)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (G : Langlands.CommGroupScheme S) [IsFinite G.X.hom] [Etale G.X.hom]
    (M : AddSubgroup (Additive (Over.mk s ⟶ G.X))),
    (∀ (gamma : FundamentalGroup s hs) (x : Additive (Over.mk s ⟶ G.X)),
      groupMonodromy s hs G.toGrp gamma x ∈ M ↔ x ∈ M) →
    ∃ (K : Langlands.CommGroupScheme S) (i : K ⟶ G),
      IsFinite K.X.hom ∧ Etale K.X.hom ∧
        IsClosedImmersion (Langlands.CommGroupScheme.hom i) ∧
        ∀ x : Additive (Over.mk s ⟶ G.X),
          x ∈ M ↔ ∃ y : Additive (Over.mk s ⟶ K.X),
            Additive.ofMul
              (y.toMul ≫ (Langlands.CommGroupScheme.groupHom i).hom.hom) = x

end Langlands.AlgebraicGeometry.FiniteEtale

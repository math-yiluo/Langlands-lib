import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Sharp conjugacy of maximally split maximal tori over the unramified closure -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- The structural conjugacy input to KP Lemma 2.6.24: over the maximal unramified
extension of a nonarchimedean local field, maximally split maximal tori are conjugate
by the image of any simply connected cover of the derived subgroup. -/
def UnramifiedSharpTorusConjugacyStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H D C : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    (d : D ⟶ H) (π : C ⟶ D), IsSimplyConnectedDerivedCover d π →
    ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
      (i : T.toGrp ⟶ H) (i' : T'.toGrp ⟶ H),
      IsMaximallySplitMaximalTorus i → IsMaximallySplitMaximalTorus i' →
      ∃ g ∈ simplyConnectedImage d π, ∃ e : T.toGrp ≅ T'.toGrp,
        i ≫ (H.innerIso g).hom = e.hom ≫ i'

end Langlands.Geometry.Building

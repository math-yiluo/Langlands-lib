import Langlands.Geometry.Building.FullValidity.UnramifiedDescent

/-! # The full Bruhat–Tits availability and descent certificate -/

universe u

open AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- The completion certificate of KP Theorem 9.2.7 over nonarchimedean local
fields. A single assignment satisfies corrected Definition 4.1.26 and its
datum for every connected reductive group satisfies Axiom 4.1.27 with UR 3
in its set-equality form. -/
def BruhatTitsCompletionCertificateStatement : Prop :=
  ∃ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid ∧
    ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      (hG : IsConnectedReductive G),
      (𝔅.datum F G hG).SatisfiesUnramifiedDescent

end Langlands.Geometry.Building

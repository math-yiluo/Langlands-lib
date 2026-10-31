import Langlands.AlgebraicGeometry.Picard.SquareFirstProjectionAcyclicityStatement
import Langlands.AlgebraicGeometry.Picard.SquareFirstFibre
import Langlands.AlgebraicGeometry.Modules.RationalFibreVanishing
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsProof
import Langlands.AlgebraicGeometry.Modules.PushforwardVanishing

/-! # Total acyclicity from acyclicity on first-projection fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- A line bundle on an abelian square is acyclic if its restriction to every
rational fibre of the first projection is acyclic. -/
theorem algClosedFieldSquareFirstProjectionAcyclicity :
    AlgClosedFieldSquareFirstProjectionAcyclicityStatement.{u} := by
  intro K _ _ A
  dsimp only
  intro Q hQ n
  let p₁ := pullback.fst A.X.hom A.X.hom
  let U : A.X.left.Opens := ⊤
  have hLocal : ∀ q : ℕ,
      IsZero ((Scheme.Modules.pullback U.ι).obj ((higherDirectImage p₁ q).obj Q.obj)) := by
    intro q
    apply isZero_pullback_higherDirectImage_of_rationalFibres universalPerfectSections K A.X.hom p₁ Q U
    intro x hx q
    let x' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X :=
      Over.homMk (x ≫ U.ι) (by simpa using hx)
    exact (hQ x' q).of_iso
      (squareFirstFibreCohomologyIso A.X.hom x'.left x'.w Q.obj q)
  have hImage : ∀ q : ℕ, IsZero ((higherDirectImage p₁ q).obj Q.obj) := by
    intro q
    let M := (higherDirectImage p₁ q).obj Q.obj
    have h := (Scheme.Modules.pullback A.X.left.topIso.inv).map_isZero (hLocal q)
    let e : (Scheme.Modules.pullback A.X.left.topIso.inv).obj
        ((Scheme.Modules.pullback U.ι).obj M) ≅ M :=
      (Scheme.Modules.pullbackComp A.X.left.topIso.inv U.ι).app M ≪≫
        (Scheme.Modules.pullbackCongr A.X.left.topIso.inv_hom_id).app M ≪≫
        (Scheme.Modules.pullbackId A.X.left).app M
    exact h.of_iso e.symm
  exact isZero_relativeCohomology_of_higherDirectImage p₁ A.X.hom Q.obj hImage n

end Langlands.AbelianScheme

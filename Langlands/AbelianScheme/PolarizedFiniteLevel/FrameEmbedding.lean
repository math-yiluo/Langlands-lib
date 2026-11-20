import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocus
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.TwistOne
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation

/-! # Frame-normalized cubic embeddings of ordinary polarized data -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n m : ℕ}

/-- A frame-normalized cubic embedding of a datum `a` over `S` for the family `ρ` of
`m + 2` level coefficient tuples: a closed immersion `ψ` of the abelian scheme into
relative projective `m`-space over `S`, under which `𝒪(1)` pulls back to the cubic bundle
twisted by a line bundle from `S`, the torsion point `ρ j` (for `j ≤ m`) goes to the
`j`-th coordinate point (all other coordinates vanish there), and the torsion point
`ρ (m + 1)` goes to the point with all coordinates equal. -/
structure Datum.IsFrameEmbedding (a : Datum P S g d n)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n)
    (ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m) : Prop where
  /-- The embedding is a morphism over the base. -/
  toBase : ψ ≫ RelativeProjectiveSpace.toBase S m = a.abelian.X.hom
  /-- The embedding is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion ψ
  /-- `ψ^* 𝒪(1)` is the cubic bundle twisted by a line bundle pulled back from the base. -/
  cubic : ∃ N : LineBundle S,
    Nonempty ((LineBundle.pullback ψ).obj (RelativeProjectiveSpace.twistOne S m) ≅
      LineBundle.tensor P.preservation a.cubicBundle
        ((LineBundle.pullback a.abelian.X.hom).obj N))
  /-- For `j ≤ m`, every coordinate other than the `j`-th vanishes at the torsion point
  `ρ j`. -/
  basis : ∀ j k : Fin (m + 1), k ≠ j →
    VanishesAlong (RelativeProjectiveSpace.twistOne S m)
      (a.torsionPoint (ρ j.castSucc) ≫ ψ)
      (RelativeProjectiveSpace.twistOneCoordinate S m k)
  /-- All coordinates agree at the torsion point `ρ (m + 1)`: their pullbacks along it are
  equal. -/
  unit : ∀ i k : Fin (m + 1),
    Langlands.SchemeModule.pullbackSection (a.torsionPoint (ρ (Fin.last (m + 1))) ≫ ψ)
        (RelativeProjectiveSpace.twistOne S m).obj
        (RelativeProjectiveSpace.twistOneCoordinate S m i) =
      Langlands.SchemeModule.pullbackSection (a.torsionPoint (ρ (Fin.last (m + 1))) ≫ ψ)
        (RelativeProjectiveSpace.twistOne S m).obj
        (RelativeProjectiveSpace.twistOneCoordinate S m k)

/-- The embedded family realized by a morphism `ψ` of the abelian scheme to relative
projective space: the ideal sheaf `I` is the kernel of `ψ` (so for a closed immersion it
cuts out the image of `ψ`), and for every level coefficient tuple `r` the integral
projective point `σ r` is the image of the torsion point with coefficients `r`. -/
def Datum.Realizes (a : Datum P S g d n)
    (ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m)
    (I : (RelativeProjectiveSpace S m).IdealSheafData)
    (σ : (Fin (2 * g) → ZMod n) → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)) : Prop :=
  ψ.ker = I ∧ ∀ r, a.torsionPoint r ≫ ψ ≫ RelativeProjectiveSpace.toIntegral S m = σ r

end Langlands.AbelianScheme.PolarizedFiniteLevel

import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicEvaluation
import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelEnumeration

/-! # Torsion evaluations of the cubic direct image and the projective frame locus -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}

/-- The torsion section of a datum with coefficient tuple `r` in its ordered level. -/
def Datum.torsionPoint (a : Datum P S g d n) (r : Fin (2 * g) → ZMod n) :
    S ⟶ a.abelian.X.left :=
  (Additive.toMul (enumerateTuple a.level.sections r)).val.left

@[reassoc (attr := simp)]
theorem Datum.torsionPoint_hom (a : Datum P S g d n) (r : Fin (2 * g) → ZMod n) :
    a.torsionPoint r ≫ a.abelian.X.hom = 𝟙 S := by
  exact Over.w (Additive.toMul (enumerateTuple a.level.sections r)).val

/-- Evaluation of the cubic direct image at the torsion section with coefficients `r`. -/
def Datum.torsionEvaluation (a : Datum P S g d n) (r : Fin (2 * g) → ZMod n) :
    a.rigidificationModule ⟶
      (Scheme.Modules.pullback (a.torsionPoint r)).obj a.cubicBundle.obj :=
  (Scheme.Modules.pullbackId S).inv.app _ ≫
    (Scheme.Modules.pullbackCongr (a.torsionPoint_hom r).symm).hom.app _ ≫
    (Scheme.Modules.pullbackComp (a.torsionPoint r) a.abelian.X.hom).inv.app _ ≫
    (Scheme.Modules.pullback (a.torsionPoint r)).map a.cubicEvaluationAdjoint

/-- Joint evaluation at all entries of `ρ` except the entry `k`. -/
def Datum.frameEvaluation {m : ℕ} (a : Datum P S g d n)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (k : Fin (m + 2)) :
    a.rigidificationModule ⟶
      ∏ᶜ (fun j : {j : Fin (m + 2) // j ≠ k} =>
        (Scheme.Modules.pullback (a.torsionPoint (ρ j))).obj a.cubicBundle.obj) :=
  Pi.lift fun j => a.torsionEvaluation (ρ j)

/-- The projective frame locus of `ρ`: the union of all opens on which, for every
omitted entry `k`, joint evaluation at the other entries is an isomorphism. -/
def Datum.frameLocus {m : ℕ} (a : Datum P S g d n)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) : S.Opens :=
  sSup {W : S.Opens | ∀ k, IsIso ((Scheme.Modules.pullback W.ι).map (a.frameEvaluation ρ k))}

end Langlands.AbelianScheme.PolarizedFiniteLevel

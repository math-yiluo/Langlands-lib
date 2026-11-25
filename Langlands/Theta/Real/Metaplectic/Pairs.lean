import Langlands.Theta.Real.Metaplectic.Basic
import Langlands.Theta.Metaplectic.Defs

/-!
# The real metaplectic group in the group of pairs

Outside GKT (the archimedean theory). The pairs construction of GKT §2.1.2 is stated for any model
of the Heisenberg representation (`Langlands.Theta.MetaplecticGroup`); here it is applied to the
Schwartz model over `ℝ`, and the real metaplectic group of `Langlands.Theta.Real.Metaplectic.Defs`
is identified with a subgroup of it.

* `Real.schrodingerSchwartzRep l`: the Schrödinger representation of the Heisenberg group of
  `(ℝ^{2l}, stdSymplecticForm l ℝ)` on `𝓢(ℝˡ, ℂ)`, `(w, t) ↦ e^{2πit} schrodingerSchwartz w`; its
  operators are those of `Real.schrodingerUnitary` on Schwartz functions
  (`Real.toLp_schrodingerSchwartzRep`).
* `RealMetaplecticGroup.toPairs :
  RealMetaplecticGroup l →* MetaplecticGroup (schrodingerSchwartzRep l)`, `(s, U, V) ↦ (s, V)`,
  injective (`toPairs_injective`), over the identification
  `Matrix.symplecticGroup.toIsometryGroup` of symplectic matrices with isometries
  (`proj_toPairs`), with Weil representation `weilSchwartz` (`weil_toPairs`), and with image in the
  pairs whose operator preserves the `L²` inner product (`toPairs_mem_unitary`).
-/

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix

namespace Langlands.Theta

open Langlands.Theta.Real Langlands.HeisenbergGroup
open Langlands.Theta.RealMetaplecticGroup.Internal (weil_toLp_aux)
open Langlands.LinearMap.BilinForm (isometryGroup)

variable {l : Type} [Fintype l] [DecidableEq l]

namespace Real

omit [DecidableEq l] in
private theorem toLp_aux (g : HeisenbergGroup (stdSymplecticForm l ℝ)) (f : RealSchwartz l) :
    schwartzToL2 l (fourierCharℂ g.cen • schrodingerSchwartz g.vec f) =
      schrodingerUnitary g (schwartzToL2 l f) := by
  rw [map_smul, schrodingerUnitary_apply]
  congr 1
  exact (schrodingerL2_toLp g.vec f).symm

variable (l) in
/-- **The Schrödinger representation on Schwartz space**: `(w, t)` acts by
`e^{2πit} schrodingerSchwartz w`. -/
def schrodingerSchwartzRep :
    Representation ℂ (HeisenbergGroup (stdSymplecticForm l ℝ)) (RealSchwartz l) where
  toFun g := fourierCharℂ g.cen • (schrodingerSchwartz g.vec).toLinearMap
  map_one' := LinearMap.ext fun f => injective_toLp 2 volume <| by
    change schwartzToL2 l (fourierCharℂ (1 : HeisenbergGroup (stdSymplecticForm l ℝ)).cen •
      schrodingerSchwartz (1 : HeisenbergGroup (stdSymplecticForm l ℝ)).vec f) = schwartzToL2 l f
    rw [toLp_aux, map_one]
    rfl
  map_mul' g h := LinearMap.ext fun f => injective_toLp 2 volume <| by
    change schwartzToL2 l (fourierCharℂ (g * h).cen • schrodingerSchwartz (g * h).vec f) =
      schwartzToL2 l (fourierCharℂ g.cen • schrodingerSchwartz g.vec
        (fourierCharℂ h.cen • schrodingerSchwartz h.vec f))
    rw [toLp_aux, toLp_aux, toLp_aux, map_mul]
    rfl

omit [DecidableEq l] in
theorem schrodingerSchwartzRep_apply (g : HeisenbergGroup (stdSymplecticForm l ℝ))
    (f : RealSchwartz l) :
    schrodingerSchwartzRep l g f = fourierCharℂ g.cen • schrodingerSchwartz g.vec f := rfl

omit [DecidableEq l] in
/-- On Schwartz functions the operators are those of the unitary representation on `L²`. -/
theorem toLp_schrodingerSchwartzRep (g : HeisenbergGroup (stdSymplecticForm l ℝ))
    (f : RealSchwartz l) :
    schwartzToL2 l (schrodingerSchwartzRep l g f) = schrodingerUnitary g (schwartzToL2 l f) :=
  toLp_aux g f

variable (l) in
/-- The `L²` inner product on Schwartz space. -/
def schwartzL2Inner : RealSchwartz l →ₗ⋆[ℂ] RealSchwartz l →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun f f' => inner ℂ (schwartzToL2 l f) (schwartzToL2 l f'))
    (fun f f' g => by rw [map_add, inner_add_left])
    (fun c f g => by rw [map_smul, inner_smul_left]; rfl)
    (fun f g g' => by rw [map_add, inner_add_right])
    (fun c f g => by rw [map_smul, inner_smul_right]; rfl)

omit [DecidableEq l] in
theorem schwartzL2Inner_apply (f f' : RealSchwartz l) :
    schwartzL2Inner l f f' = inner ℂ (schwartzToL2 l f) (schwartzToL2 l f') := rfl

end Real

namespace RealMetaplecticGroup

/-- The operator of Schwartz space of an element, as a linear automorphism. -/
private def weilSchwartzEquiv (g : RealMetaplecticGroup l) :
    RealSchwartz l ≃ₗ[ℂ] RealSchwartz l :=
  LinearEquiv.ofLinearMap (weilSchwartz g).toLinearMap (weilSchwartz g⁻¹).toLinearMap
    (LinearMap.ext fun f => by
      change (weilSchwartz g * weilSchwartz g⁻¹) f = f
      rw [← map_mul, mul_inv_cancel, map_one]; rfl)
    (LinearMap.ext fun f => by
      change (weilSchwartz g⁻¹ * weilSchwartz g) f = f
      rw [← map_mul, inv_mul_cancel, map_one]; rfl)

/-- The pair `(s, V)` of an element satisfies the relation (2.2) for the Schwartz model. -/
private theorem isMetaplecticPair (g : RealMetaplecticGroup l) :
    IsMetaplecticPair (schrodingerSchwartzRep l)
      (_root_.Langlands.Matrix.symplecticGroup.toIsometryGroup l ℝ (proj g))
      (weilSchwartzEquiv g) := fun k => LinearMap.ext fun f => injective_toLp 2 volume <| by
  change schwartzToL2 l (weilSchwartz g (schrodingerSchwartzRep l k f)) =
    schwartzToL2 l (schrodingerSchwartzRep l ⟨(proj g).1 *ᵥ k.vec, k.cen⟩ (weilSchwartz g f))
  rw [← weil_toLp_aux, toLp_schrodingerSchwartzRep, toLp_schrodingerSchwartzRep,
    schrodingerUnitary_apply, schrodingerUnitary_apply, LinearIsometryEquiv.map_smul,
    weil_schrodingerL2, weil_toLp_aux]

/-- **The real metaplectic group in the pairs of the Schwartz model** (GKT §2.1.2 over `ℝ`):
`(s, U, V) ↦ (s, V)`. -/
def toPairs : RealMetaplecticGroup l →* MetaplecticGroup (schrodingerSchwartzRep l) where
  toFun g := ⟨(_root_.Langlands.Matrix.symplecticGroup.toIsometryGroup l ℝ (proj g),
    weilSchwartzEquiv g), isMetaplecticPair g⟩
  map_one' := MetaplecticGroup.ext _
    (show _root_.Langlands.Matrix.symplecticGroup.toIsometryGroup l ℝ (proj 1) = 1 by
      rw [map_one, map_one])
    (LinearEquiv.ext fun f => by
      change weilSchwartz 1 f = f
      rw [map_one]; rfl)
  map_mul' g h := MetaplecticGroup.ext _
    (show _root_.Langlands.Matrix.symplecticGroup.toIsometryGroup l ℝ (proj (g * h)) =
        _root_.Langlands.Matrix.symplecticGroup.toIsometryGroup l ℝ (proj g) *
          _root_.Langlands.Matrix.symplecticGroup.toIsometryGroup l ℝ (proj h) by
      rw [map_mul, map_mul])
    (LinearEquiv.ext fun f => by
      change weilSchwartz (g * h) f = weilSchwartz g (weilSchwartz h f)
      rw [map_mul]; rfl)

/-- The isometry of `toPairs g` is the symplectic matrix of `g`. -/
@[simp] theorem proj_toPairs (g : RealMetaplecticGroup l) :
    MetaplecticGroup.proj _ (toPairs g) =
      _root_.Langlands.Matrix.symplecticGroup.toIsometryGroup l ℝ (proj g) := rfl

/-- The Weil representation of `toPairs g` is the operator of `g` on Schwartz space. -/
@[simp] theorem weil_toPairs (g : RealMetaplecticGroup l) (f : RealSchwartz l) :
    MetaplecticGroup.weil _ (toPairs g) f = weilSchwartz g f := rfl

/-- `toPairs` is injective: an element is determined by its symplectic matrix and its operator of
Schwartz space (`RealMetaplecticGroup.ext`). -/
theorem toPairs_injective : Function.Injective (toPairs (l := l)) := fun g h e => by
  refine RealMetaplecticGroup.ext ?_ (ContinuousLinearMap.ext fun f => ?_)
  · have := congrArg (MetaplecticGroup.proj _) e
    rw [proj_toPairs, proj_toPairs] at this
    exact (_root_.Langlands.Matrix.symplecticGroup.toIsometryGroup l ℝ).injective this
  · have := congrArg (fun x => MetaplecticGroup.weil _ x f) e
    simpa only [weil_toPairs] using this

/-- The operators of `toPairs` preserve the `L²` inner product: the image is in the unitary pairs
(GKT `Mp(W)^{ℂ¹}`, p. 49, over `ℝ`). -/
theorem toPairs_mem_unitary (g : RealMetaplecticGroup l) :
    toPairs g ∈ MetaplecticGroup.unitary _ (schwartzL2Inner l) := fun f f' => by
  change inner ℂ (schwartzToL2 l (weilSchwartz g f)) (schwartzToL2 l (weilSchwartz g f')) =
    inner ℂ (schwartzToL2 l f) (schwartzToL2 l f')
  rw [← weil_toLp_aux, ← weil_toLp_aux, LinearIsometryEquiv.inner_map_map]

end RealMetaplecticGroup

end Langlands.Theta

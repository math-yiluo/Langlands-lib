import Langlands.Group.GL.Basic
import Langlands.LocalField.LocalFieldArithmetic
import Langlands.AllField.Group.GL.NormalizedCharacter
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Determinant windows on `GL_n(E)` for a finite extension of a local field

For a nonarchimedean local field `F`, an `F`-algebra `E` and `m : ℕ`, the function
`determinantWindow F m` on `GL_n(E)` is the indicator of the set of matrices `x` whose
determinant has norm `N_{E/F}(det x)` of normalized order in `[0, m)`. With `0 < n`,
`m = n [E : F]` and `E` a field finite over `F`, every orbit of the scalar matrices `F^×` meets
this set in exactly one `O_F^×`-coset, so the window serves as a cut-off normalized over the
scalars `F^×`.
The module also proves that the window is locally constant when `E` is finite over `F` and
carries its module topology. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open Topology

universe u v

/-- The **determinant window** of length `m`: the indicator function, with complex values,
of the matrices `x ∈ GL_n(E)` with `0 ≤ ord_F (N_{E/F} (det x)) < m`, where `N_{E/F}` is
`Algebra.norm F` and `ord_F` is the normalized integer order of the local field `F`
(`LocalFieldData.ord` for the data of the instances of `F`). -/
def determinantWindow (F : Type u) [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F] {E : Type v} [Field E] [Algebra F E] {n : ℕ} (m : ℕ)
    (x : GeneralLinear n E) : ℂ :=
  Set.indicator
    {y : GeneralLinear n E |
      (LocalFieldData.ofInstances F).ord
          (Algebra.norm F ((GeneralLinear.determinant y : Eˣ) : E)) ∈ Set.Ico (0 : ℤ) m}
    (fun _ => (1 : ℂ)) x

section LocallyConstant

variable {F : Type u} [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]

/-- The field norm of a finite algebra with its module topology is continuous. -/
theorem continuous_algebraNorm_of_isModuleTopology {E : Type v} [CommRing E] [Algebra F E]
    [Module.Finite F E] [TopologicalSpace E] [IsModuleTopology F E] :
    Continuous (Algebra.norm F : E → F) := by
  let b := Module.finBasis F E
  change Continuous (fun x : E => Algebra.norm F x)
  simp_rw [Algebra.norm_eq_matrix_det b]
  exact (IsModuleTopology.continuous_of_linearMap
    (Algebra.leftMulMatrix b).toLinearMap).matrix_det

/-- A unit of `F` has order zero exactly when it lies in the kernel of the normalized absolute
value. -/
theorem ord_eq_zero_iff_mem_ker_normalizedAbsUnits (a : Fˣ) :
    (LocalFieldData.ofInstances F).ord (a : F) = 0 ↔
      a ∈ (LocalFieldData.ofInstances F).normalizedAbsUnits.ker := by
  set T := LocalFieldData.ofInstances F
  rw [MonoidHom.mem_ker, ← Units.val_inj, ← NNReal.coe_inj]
  change _ ↔ T.normalizedAbs (a : F) = 1
  rw [T.normalizedAbs_of_ne_zero a.ne_zero]
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  rw [zpow_eq_one_iff_right₀ (by positivity) hq.ne', neg_eq_zero]

/-- The determinant window is locally constant: it is invariant under right multiplication by
the open subgroup of matrices whose determinant has a norm of order zero. -/
theorem isLocallyConstant_determinantWindow {E : Type v} [Field E] [Algebra F E]
    [Module.Finite F E] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
    {n : ℕ} (m : ℕ) :
    IsLocallyConstant (determinantWindow F (E := E) (n := n) m) := by
  set T := LocalFieldData.ofInstances F
  let g : GeneralLinear n E →* Fˣ :=
    (Units.map (Algebra.norm F : E →* F)).comp GeneralLinear.determinant
  have hg : Continuous g :=
    (continuous_algebraNorm_of_isModuleTopology (F := F) (E := E)).units_map
      (Algebra.norm F : E →* F) |>.comp Matrix.GeneralLinearGroup.continuous_det
  have hU : IsOpen (g ⁻¹' (T.normalizedAbsUnits.ker : Set Fˣ)) :=
    T.isOpen_ker_normalizedAbsUnits.preimage hg
  have hgval (x : GeneralLinear n E) :
      ((g x : Fˣ) : F) = Algebra.norm F ((GeneralLinear.determinant x : Eˣ) : E) := rfl
  have key (x y : GeneralLinear n E) (hy : g (x⁻¹ * y) ∈ T.normalizedAbsUnits.ker) :
      T.ord (Algebra.norm F ((GeneralLinear.determinant y : Eˣ) : E)) =
        T.ord (Algebra.norm F ((GeneralLinear.determinant x : Eˣ) : E)) := by
    have h0 : T.ord ((g (x⁻¹ * y) : Fˣ) : F) = 0 :=
      (ord_eq_zero_iff_mem_ker_normalizedAbsUnits _).mpr hy
    have hy' : y = x * (x⁻¹ * y) := by group
    rw [← hgval, ← hgval, hy', map_mul, Units.val_mul,
      T.ord_mul (g x).ne_zero (g (x⁻¹ * y)).ne_zero, h0, add_zero]
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hmem : ∀ᶠ y in 𝓝 x, g (x⁻¹ * y) ∈ T.normalizedAbsUnits.ker := by
    have hc : Continuous fun y : GeneralLinear n E => x⁻¹ * y := continuous_const.mul continuous_id
    have hx : x⁻¹ * x ∈ g ⁻¹' (T.normalizedAbsUnits.ker : Set Fˣ) := by
      simp only [inv_mul_cancel, Set.mem_preimage, map_one, SetLike.mem_coe, one_mem]
    exact hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
  filter_upwards [hmem] with y hy
  have hk : (LocalFieldData.ofInstances F).ord
      (Algebra.norm F ((GeneralLinear.determinant y : Eˣ) : E)) =
      (LocalFieldData.ofInstances F).ord
        (Algebra.norm F ((GeneralLinear.determinant x : Eˣ) : E)) := key x y hy
  simp only [determinantWindow, Set.indicator, Set.mem_ofPred_eq, hk]

end LocallyConstant

end Langlands.BaseChange

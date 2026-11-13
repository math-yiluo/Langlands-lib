import Langlands.Geometry.Analytic.DrinfeldFacetGSpaces
import Langlands.Geometry.Analytic.SetInducedSpaceContinuityStatement
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix

/-! # The level-one base `Ω × Δ` of Drinfeld's tower, for the matrix factor `GL_{d+1}(F)` -/

noncomputable section

universe u

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

open _root_.CategoryTheory SaturatedAtlasPresentation

variable {F : Type u} [NontriviallyNormedField F] {d : ℕ}

/-! ## The index set `Δ` -/

variable (F d) in
/-- The elements of `GL_{d+1}(F)` whose determinant has absolute value one: the kernel of
`g ↦ ‖det g‖`. -/
def detNormOne : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F) :=
  ((Units.map (normHom : F →*₀ ℝ).toMonoidHom).comp Matrix.GeneralLinearGroup.det).ker

theorem mem_detNormOne {γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F} :
    γ ∈ detNormOne F d ↔ ‖((Matrix.GeneralLinearGroup.det γ : Fˣ) : F)‖ = 1 := by
  rw [detNormOne, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  rfl

instance : (detNormOne F d).Normal :=
  MonoidHom.normal_ker _

theorem facetStabilizerNormOne_eq (S : Set (NormClass F (Fin (d + 1) → F))) :
    facetStabilizerNormOne S = facetStabilizer S ⊓ detNormOne F d :=
  rfl

theorem facetStabilizerNormOne_le_detNormOne (S : Set (NormClass F (Fin (d + 1) → F))) :
    facetStabilizerNormOne S ≤ detNormOne F d :=
  inf_le_right

variable (F d) in
/-- The index set of the components of the level-one space: `GL_{d+1}(F)` modulo the elements
with `|det| = 1`, with `GL_{d+1}(F)` acting by left multiplication. -/
abbrev LevelOneIndex : Type u :=
  Matrix.GeneralLinearGroup (Fin (d + 1)) F ⧸ detNormOne F d

/-- The absolute value of the determinant, on the index set: `γ (|det| = 1) ↦ ‖det γ‖`. -/
def levelOneIndexNorm (δ : LevelOneIndex F d) : ℝ :=
  ((QuotientGroup.lift (detNormOne F d)
    ((Units.map (normHom : F →*₀ ℝ).toMonoidHom).comp Matrix.GeneralLinearGroup.det)
    le_rfl δ : ℝˣ) : ℝ)

@[simp]
theorem levelOneIndexNorm_mk (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) :
    levelOneIndexNorm (QuotientGroup.mk γ : LevelOneIndex F d) =
      ‖((Matrix.GeneralLinearGroup.det γ : Fˣ) : F)‖ :=
  rfl

/-- The absolute value of the determinant identifies the index set with a subset of `ℝ`. -/
theorem levelOneIndexNorm_injective : Function.Injective (levelOneIndexNorm (F := F) (d := d)) := by
  intro δ δ' h
  induction δ using QuotientGroup.induction_on with | H γ => ?_
  induction δ' using QuotientGroup.induction_on with | H γ' => ?_
  rw [QuotientGroup.eq, mem_detNormOne]
  simp only [levelOneIndexNorm_mk] at h
  have hγ : ‖((Matrix.GeneralLinearGroup.det γ : Fˣ) : F)‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Units.ne_zero _)
  rw [map_mul, map_inv, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, h,
    inv_mul_cancel₀ (h ▸ hγ)]

/-- The image of the index set in `ℝ` is the value group `{‖x‖ : x ∈ Fˣ}`. -/
theorem range_levelOneIndexNorm :
    Set.range (levelOneIndexNorm (F := F) (d := d)) = Set.range fun x : Fˣ => ‖(x : F)‖ := by
  ext r
  constructor
  · rintro ⟨δ, rfl⟩
    induction δ using QuotientGroup.induction_on with
    | H γ => exact ⟨_, (levelOneIndexNorm_mk γ).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨γ, hγ⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin (d + 1)) x
    exact ⟨QuotientGroup.mk γ, by rw [levelOneIndexNorm_mk, hγ]⟩

/-- The action of `g` on the index set multiplies the absolute value by `‖det g‖`. -/
theorem levelOneIndexNorm_smul (g : Matrix.GeneralLinearGroup (Fin (d + 1)) F)
    (δ : LevelOneIndex F d) :
    levelOneIndexNorm (g • δ) = ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ *
      levelOneIndexNorm δ := by
  induction δ using QuotientGroup.induction_on with | H γ => ?_
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, levelOneIndexNorm_mk, levelOneIndexNorm_mk,
    map_mul, Units.val_mul, norm_mul]

/-- Elements with `|det| = 1` fix every index. -/
theorem smul_levelOneIndex_of_mem {g : Matrix.GeneralLinearGroup (Fin (d + 1)) F}
    (hg : g ∈ detNormOne F d) (δ : LevelOneIndex F d) : g • δ = δ :=
  levelOneIndexNorm_injective (by rw [levelOneIndexNorm_smul, mem_detNormOne.1 hg, one_mul])

/-- The stabilizer of every index is the subgroup of elements with `|det| = 1`. -/
theorem stabilizer_levelOneIndex (δ : LevelOneIndex F d) :
    MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin (d + 1)) F) δ = detNormOne F d := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  refine ⟨fun h => ?_, fun h => smul_levelOneIndex_of_mem h δ⟩
  have h' := congrArg levelOneIndexNorm h
  rw [levelOneIndexNorm_smul] at h'
  induction δ using QuotientGroup.induction_on with | H γ => ?_
  rw [levelOneIndexNorm_mk] at h'
  have hγ : ‖((Matrix.GeneralLinearGroup.det γ : Fˣ) : F)‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Units.ne_zero _)
  exact mem_detNormOne.2 (mul_right_cancel₀ hγ (h'.trans (one_mul _).symm))

/-- For an ultrametric `F`, the elements with `|det| = 1` form an open subgroup. -/
theorem isOpen_detNormOne [IsUltrametricDist F] :
    IsOpen (detNormOne F d : Set (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) := by
  have hc : Continuous fun γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F =>
      ((Matrix.GeneralLinearGroup.det γ : Fˣ) : F) :=
    Units.continuous_val.matrix_det
  have h := (IsUltrametricDist.isOpen_sphere (0 : F) one_ne_zero).preimage hc
  convert h using 1
  ext γ
  simp [mem_detNormOne]

theorem isOpen_stabilizer_levelOneIndex [IsUltrametricDist F] (δ : LevelOneIndex F d) :
    IsOpen (MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin (d + 1)) F) δ :
      Set (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) := by
  rw [stabilizer_levelOneIndex]
  exact isOpen_detNormOne

/-! ## The level-one space `Ω × Δ` -/

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] [ProperSpace F] [NeZero d]

/-- The level-one space `Ω × Δ`: one copy of Drinfeld's upper half space `Ω` for each index
`δ`, with `g` acting on `Ω` and sending the copy indexed by `δ` to the copy indexed by `g • δ`.
It is Berkovich's space `X_Σ` of the `GL_{d+1}(F)`-set `Σ = LevelOneIndex F d`. -/
abbrev levelOneBase : Action (LocalizedCategory.{u, u, u} (K := K))
    (Matrix.GeneralLinearGroup (Fin (d + 1)) F) :=
  SetInducedSpace.setInduced (omegaAction F K d) (LevelOneIndex F d)

/-- The inclusion of the copy `Ω × {δ}`. -/
abbrev levelOneCopy (δ : LevelOneIndex F d) :
    (omegaAction F K d).V ⟶ (levelOneBase (F := F) (d := d) K).V :=
  SetInducedSpace.copy (omegaAction F K d) (LevelOneIndex F d) δ

theorem levelOneCopy_ρ (g : Matrix.GeneralLinearGroup (Fin (d + 1)) F)
    (δ : LevelOneIndex F d) :
    levelOneCopy K δ ≫ (levelOneBase K).ρ g = (omegaAction F K d).ρ g ≫ levelOneCopy K (g • δ) :=
  SetInducedSpace.copy_actionMap _ _ g δ

/-- The projection `Ω × Δ → Ω`, a morphism of `GL_{d+1}(F)`-objects. -/
abbrev levelOneProjection : levelOneBase (F := F) (d := d) K ⟶ omegaAction F K d :=
  SetInducedSpace.projection (omegaAction F K d) (LevelOneIndex F d)

@[reassoc (attr := simp)]
theorem levelOneCopy_projection (δ : LevelOneIndex F d) :
    levelOneCopy K δ ≫ (levelOneProjection (F := F) (d := d) K).hom = 𝟙 _ :=
  SetInducedSpace.copy_projectionHom _ _ δ

/-- For a subgroup `H` of elements with `|det| = 1`, the inclusion of the copy `Ω × {δ}` is
`H`-equivariant. -/
def levelOneCopyHom (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F))
    (hH : H ≤ detNormOne F d) (δ : LevelOneIndex F d) :
    (Action.res _ H.subtype).obj (omegaAction F K d) ⟶
      (Action.res _ H.subtype).obj (levelOneBase (F := F) (d := d) K) where
  hom := levelOneCopy K δ
  comm h := by
    change (omegaAction F K d).ρ (h : Matrix.GeneralLinearGroup (Fin (d + 1)) F) ≫
        levelOneCopy K δ = levelOneCopy K δ ≫ (levelOneBase K).ρ h
    rw [levelOneCopy_ρ, smul_levelOneIndex_of_mem (hH h.2)]

@[simp]
theorem levelOneCopyHom_hom (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F))
    (hH : H ≤ detNormOne F d) (δ : LevelOneIndex F d) :
    (levelOneCopyHom K H hH δ).hom = levelOneCopy K δ :=
  rfl

/-- Harris's `U(e, 1, δ) = U(e) × {δ}` in `Ω × Δ`, for a finite set of vertices `f` and a
subgroup `H` of the elements of `S(f)` with `|det| = 1`: the inclusion of `U(f)` into the copy
indexed by `δ`, as a morphism of `H`-objects. -/
def facetLevelOneInclusion {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F))
    (hH : H ≤ facetStabilizerNormOne S) (δ : LevelOneIndex F d) :
    facetAction K hS ε H (hH.trans (facetStabilizerNormOne_le S)) ⟶
      (Action.res _ H.subtype).obj (levelOneBase (F := F) (d := d) K) :=
  facetInclusion K hS ε H (hH.trans (facetStabilizerNormOne_le S)) ≫
    levelOneCopyHom K H (hH.trans (facetStabilizerNormOne_le_detNormOne S)) δ

@[simp]
theorem facetLevelOneInclusion_hom {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite)
    (ε : ℝ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F))
    (hH : H ≤ facetStabilizerNormOne S) (δ : LevelOneIndex F d) :
    (facetLevelOneInclusion K hS ε H hH δ).hom =
      (facetInclusion K hS ε H (hH.trans (facetStabilizerNormOne_le S))).hom ≫
        levelOneCopy K δ :=
  rfl

/-! ## The level-one space as a `GL_{d+1}(F)`-space -/

/-- `Ω × Δ` as a `GL_{d+1}(F)`-space, for ultrametric `F`, given that the action on `Ω` is
continuous and granted the published statement `SetInducedSpace.ContinuityStatement`. -/
def levelOneGSpace [IsUltrametricDist F] (hΩ : IsContinuousAction (omegaAction F K d).ρAut)
    (hSI : SetInducedSpace.ContinuityStatement.{u, u, u}) :
    GSpace.{u, u, u} K (Matrix.GeneralLinearGroup (Fin (d + 1)) F) :=
  ⟨levelOneBase K, hSI K (Matrix.GeneralLinearGroup (Fin (d + 1)) F) (omegaAction F K d)
    (LevelOneIndex F d) isOpen_stabilizer_levelOneIndex (omegaGSpace K hΩ).property⟩

@[simp]
theorem levelOneGSpace_obj [IsUltrametricDist F] (hΩ : IsContinuousAction (omegaAction F K d).ρAut)
    (hSI : SetInducedSpace.ContinuityStatement.{u, u, u}) :
    (levelOneGSpace K hΩ hSI).obj = levelOneBase K :=
  rfl

/-- The projection `Ω × Δ → Ω` as a morphism of `GL_{d+1}(F)`-spaces. -/
def levelOneGSpaceProjection [IsUltrametricDist F]
    (hΩ : IsContinuousAction (omegaAction F K d).ρAut)
    (hSI : SetInducedSpace.ContinuityStatement.{u, u, u}) :
    levelOneGSpace K hΩ hSI ⟶ omegaGSpace K hΩ :=
  ObjectProperty.homMk (levelOneProjection K)

end Langlands.Analytic.DrinfeldUpperHalfSpace

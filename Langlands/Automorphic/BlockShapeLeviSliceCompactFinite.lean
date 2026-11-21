import Langlands.Automorphic.BlockShapeLeviSliceFactors
import Langlands.Automorphic.CompactAction
import Langlands.Global.AdelicGLStandardCompact

/-! An individual Levi slice at a standard compact parameter is compact-finite. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Matrix

universe u

namespace Langlands.Automorphic

open Langlands.GeneralLinear Langlands.Global NumberField

variable {n : ℕ} (B : BlockShape n)

private theorem unitary_reindex_blockDiagonal {𝕜 : Type*} [RCLike 𝕜]
    (M : ∀ i : Fin B.length, Matrix (Fin (B.size i)) (Fin (B.size i)) 𝕜)
    (hM : ∀ i, M i ∈ Matrix.unitaryGroup (Fin (B.size i)) 𝕜) :
    Matrix.reindex B.indexEquiv B.indexEquiv (Matrix.blockDiagonal' M) ∈
      Matrix.unitaryGroup (Fin n) 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
    Matrix.blockDiagonal'_conjTranspose]
  let e := Matrix.reindexRingEquiv 𝕜 B.indexEquiv
  change e (Matrix.blockDiagonal' M) * e (Matrix.blockDiagonal' fun i => (M i)ᴴ) = 1
  have h : (fun i => M i * (M i)ᴴ) = 1 := funext fun i =>
    (Matrix.mem_unitaryGroup_iff.mp (hM i))
  rw [← map_mul, ← Matrix.blockDiagonal'_mul, h, Matrix.blockDiagonal'_one, map_one]

private theorem mapMatrix_leviEmbedding {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (m : B.Levi R) :
    φ.mapMatrix (B.leviEmbedding R m).val =
      Matrix.reindex B.indexEquiv B.indexEquiv
        (Matrix.blockDiagonal' (fun i => φ.mapMatrix (m i).val)) := by
  change Matrix.reindex B.indexEquiv B.indexEquiv
      ((Matrix.blockDiagonal' fun i => (m i).val).map φ) = _
  rw [Matrix.blockDiagonal'_map _ _ (map_zero φ)]
  rfl

variable (F : Type u) [Field F] [NumberField F]

omit [NumberField F] in
private theorem leviEmbedding_mem_standardInfiniteCompact
    (k : ∀ i : Fin B.length, standardInfiniteCompact F (B.size i)) :
    B.leviEmbedding (InfiniteAdeleRing F) (fun i => (k i).val) ∈
      standardInfiniteCompact F n := by
  refine (mem_standardInfiniteCompact_iff F n _).mpr ⟨fun v => ?_, fun v => ?_⟩
  · let φ := (PrimitiveAdelicHeight.realCoord v).comp
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
    change φ.mapMatrix (B.leviEmbedding (InfiniteAdeleRing F) (fun i => (k i).val)).val ∈ _
    rw [mapMatrix_leviEmbedding B φ]
    exact unitary_reindex_blockDiagonal B _ fun i =>
      ((mem_standardInfiniteCompact_iff F (B.size i) (k i).val).mp (k i).property).1 v
  · let φ := (PrimitiveAdelicHeight.complexCoord v).comp
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
    change φ.mapMatrix (B.leviEmbedding (InfiniteAdeleRing F) (fun i => (k i).val)).val ∈ _
    rw [mapMatrix_leviEmbedding B φ]
    exact unitary_reindex_blockDiagonal B _ fun i =>
      ((mem_standardInfiniteCompact_iff F (B.size i) (k i).val).mp (k i).property).2 v

/-- Insert the actual standard compact of one block into the ambient standard compact. -/
def blockShapeInfiniteCompactEmbedding (i : Fin B.length) :
    standardInfiniteCompact F (B.size i) →* standardInfiniteCompact F n :=
  ((B.leviEmbedding (InfiniteAdeleRing F)).comp
    ((MonoidHom.mulSingle (fun j => InfiniteAdelicGL F (B.size j)) i).comp
      (standardInfiniteCompact F (B.size i)).subtype)).codRestrict _ (by
    intro k
    have h : Pi.mulSingle i k.val =
        fun j => (Pi.mulSingle (M := fun j => standardInfiniteCompact F (B.size j)) i k j).val := by
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Pi.mulSingle_eq_same]
      · simp only [Pi.mulSingle_eq_of_ne hj, Subgroup.coe_one]
    change B.leviEmbedding (InfiniteAdeleRing F) (Pi.mulSingle i k.val) ∈ _
    rw [h]
    exact leviEmbedding_mem_standardInfiniteCompact B F _)

private theorem fullLeviEmbedding_ofInfinite (m : AdelicBlockParabolic.InfiniteLevi F B) :
    B.leviEmbedding (Adeles F) (fun i => AdelicGL.ofInfinite F (B.size i) (m i)) =
      AdelicGL.ofInfinite F n (B.leviEmbedding (InfiniteAdeleRing F) m) := by
  let x : AdelicBlockParabolic.FullLevi F B := fun i => AdelicGL.ofInfinite F (B.size i) (m i)
  have hi : AdelicBlockParabolic.leviInfinite F B x = m := by
    funext j
    exact AdelicGL.infinite_ofInfinite F (B.size j) (m j)
  have hf : AdelicBlockParabolic.leviFinite F B x = 1 := by
    funext j
    exact AdelicGL.finite_ofInfinite F (B.size j) (m j)
  apply AdelicGL.ext_infinite_finite F n
  · have h := congrArg Subtype.val (AdelicBlockParabolic.infinite_leviInParabolic F B x)
    change AdelicGL.infinite F n (B.leviEmbedding (Adeles F) x) =
      B.leviEmbedding (InfiniteAdeleRing F) (AdelicBlockParabolic.leviInfinite F B x) at h
    rw [AdelicGL.infinite_ofInfinite, h, hi]
  · have h := congrArg Subtype.val (AdelicBlockParabolic.finite_leviInParabolic F B x)
    change AdelicGL.finite F n (B.leviEmbedding (Adeles F) x) =
      B.leviEmbedding (FiniteAdeles F) (AdelicBlockParabolic.leviFinite F B x) at h
    rw [AdelicGL.finite_ofInfinite, h, hf, map_one]

local instance leviSliceCompactRationalGroup {d : ℕ} :
    AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance leviSliceCompactContinuousGroup {d : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance leviSliceCompactSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance leviSliceCompactFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

/-- Taking one coordinate of the block Levi slice is linear in the original form. -/
def blockShapeLeviSliceFactorLinear (g : AdelicGL F n)
    (m : AdelicBlockParabolic.FullLevi F B) (i : Fin B.length) :
    FiniteSmoothRationalFunctions F n →ₗ[ℂ] ContinuousRationalFunctions F (B.size i) where
  toFun f := blockShapeLeviSliceFactor B F f g m i
  map_add' f f' := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact congrFun ((finiteSmoothBlockConstantTerm F (standardBlockWeight B.cuts)).map_add f f') _
  map_smul' a f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact congrFun ((finiteSmoothBlockConstantTerm F (standardBlockWeight B.cuts)).map_smul a f) _

private theorem blockShapeLeviSliceFactor_compact_translate
    (f : FiniteSmoothRationalFunctions F n) (k : standardInfiniteCompact F n) (d : FiniteAdelicGL F n)
    (m : AdelicBlockParabolic.FullLevi F B) (i : Fin B.length)
    (a : standardInfiniteCompact F (B.size i)) :
    let g := AdelicGL.pair F n k.val d
    let b := k⁻¹ * blockShapeInfiniteCompactEmbedding B F i a * k
    blockShapeLeviSliceFactorLinear B F g m i (finiteSmoothCompactRightAction F n b f) =
      infiniteSubgroupRightAction F (B.size i) (standardInfiniteCompact F (B.size i)) a
        (blockShapeLeviSliceFactorLinear B F g m i f) := by
  dsimp only
  apply Subtype.ext
  apply Subtype.ext
  funext x
  let g := AdelicGL.pair F n k.val d
  let c := blockShapeInfiniteCompactEmbedding B F i a
  let b := k⁻¹ * c * k
  let h := AdelicGL.ofInfinite F n b.val
  let z := AdelicGL.ofInfinite F (B.size i) a.val
  have hcoord : Function.update m i (x * z) = Function.update m i x * Pi.mulSingle i z := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Pi.mul_apply, Function.update_self, Pi.mulSingle_eq_same]
    · simp only [Pi.mul_apply, Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj, mul_one]
  have hone : Pi.mulSingle i z = fun j =>
      AdelicGL.ofInfinite F (B.size j)
        (Pi.mulSingle (M := fun j => InfiniteAdelicGL F (B.size j)) i a.val j) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Pi.mulSingle_eq_same, z]
    · simp only [Pi.mulSingle_eq_of_ne hj, map_one]
  have hdiag : B.leviEmbedding (Adeles F) (Pi.mulSingle i z) = AdelicGL.ofInfinite F n c.val := by
    rw [hone, fullLeviEmbedding_ofInfinite]
    rfl
  have hgh : g * h = AdelicGL.ofInfinite F n c.val * g := by
    change AdelicGL.pair F n k.val d * AdelicGL.ofInfinite F n b.val =
      AdelicGL.ofInfinite F n c.val * AdelicGL.pair F n k.val d
    simp only [AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, mul_one, one_mul]
    congr 1
    simp [b, mul_assoc]
  change blockShapeLeviSlice F B (finiteSmoothRightAction F n h f) g (Function.update m i x) =
    blockShapeLeviSlice F B f g (Function.update m i (x * z))
  rw [blockShapeLeviSlice_rightAction, hgh, hcoord]
  unfold blockShapeLeviSlice
  rw [map_mul, hdiag, mul_assoc]

/-- The block compact orbit lies in the linear image of the ambient compact orbit. -/
theorem blockShapeLeviSliceFactor_isInfiniteFinite (f : FiniteSmoothRationalFunctions F n)
    (hf : FiniteVectors.IsFiniteVector (finiteSmoothCompactRightAction F n) f)
    (k : standardInfiniteCompact F n) (d : FiniteAdelicGL F n)
    (m : AdelicBlockParabolic.FullLevi F B) (i : Fin B.length) :
    IsInfiniteFinite F (B.size i) (standardInfiniteCompact F (B.size i))
      (blockShapeLeviSliceFactor B F f (AdelicGL.pair F n k.val d) m i) := by
  let g := AdelicGL.pair F n k.val d
  let L := blockShapeLeviSliceFactorLinear B F g m i
  let π := finiteSmoothCompactRightAction F n
  let σ := infiniteSubgroupRightAction F (B.size i) (standardInfiniteCompact F (B.size i))
  have : Module.Finite ℂ (FiniteVectors.orbitSpan π f) := hf
  change Module.Finite ℂ (FiniteVectors.orbitSpan σ (L f))
  refine Submodule.finiteDimensional_of_le (S₂ := (FiniteVectors.orbitSpan π f).map L) ?_
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  let b := k⁻¹ * blockShapeInfiniteCompactEmbedding B F i a * k
  exact ⟨π b f, FiniteVectors.action_mem_orbitSpan π b f,
    blockShapeLeviSliceFactor_compact_translate B F f k d m i a⟩

/-- Every actual automorphic form gives a compact-finite block slice at a standard compact parameter. -/
theorem blockShapeLeviSliceFactor_isInfiniteFinite_of_form (f : AutomorphicForms F n)
    (k : standardInfiniteCompact F n) (d : FiniteAdelicGL F n)
    (m : AdelicBlockParabolic.FullLevi F B) (i : Fin B.length) :
    IsInfiniteFinite F (B.size i) (standardInfiniteCompact F (B.size i))
      (blockShapeLeviSliceFactor B F f.val (AdelicGL.pair F n k.val d) m i) :=
  blockShapeLeviSliceFactor_isInfiniteFinite B F f.val
    ((automorphicCompactRightAction_isFiniteVector F n f).map
      (automorphicCompactFiniteSmoothInclusion F n)) k d m i

end Langlands.Automorphic

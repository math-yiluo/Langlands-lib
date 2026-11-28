import Langlands.TraceFormula.TwistedOrbitalFibreVanishing
import Langlands.Group.GL.UnipotentEntries
import Langlands.Group.GL.ParabolicQuotient
import Langlands.BaseChange.Norm

/-!
# The unipotent fibre of a block Levi for σ-conjugation on `GL_n(E)`

Let `F` be a field, `E` a commutative topological `F`-algebra with `σ : E ≃ₐ[F] E`, and `B` a
block shape of `n` with at most two blocks. For `δ` in the block diagonal subgroup `M(E)` whose
σ-centralizer lies in `M(E)`, the unipotent radical `U(E)` of the standard parabolic `P(E)`, with
the Levi projection `P(E) → M(E) ⊆ GL_n(E)`, is a `TwistedFibreData` for the entrywise action of
`σ` (`leviTwistedFibreData`). When `E` is a finite `F`-module, the twisted conjugation
`u ↦ δ⁻¹ u δ (u^σ)⁻¹` maps `U(E)` onto itself (`leviTwistedFibreData_twist_surjective`): writing
`u = 1 + Y`, it is `Y ↦ δ⁻¹ Y δ - Y^σ` on the matrices with vanishing blocks on and below the
diagonal, an injective `F`-linear endomorphism of a finite-dimensional `F`-vector space.
-/

namespace Langlands.BaseChange

open Langlands.TraceFormula Langlands.GeneralLinear

universe u v

section FibreData

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E]
  [IsTopologicalRing E] [T2Space E] {n : ℕ} (B : BlockShape n) (σ : E ≃ₐ[F] E)
  (δ : GeneralLinear n E)

/-- For a block shape with at most two blocks and `δ` in the block diagonal subgroup `M(E)` with
σ-centralizer in `M(E)`: the unipotent radical `U(E)`, the parabolic `P(E)` and the Levi
projection `P(E) → M(E)` form a `TwistedFibreData` for the entrywise action of `σ` at `δ`. -/
def leviTwistedFibreData (hB : B.length ≤ 2) (hδ : δ ∈ B.leviSubgroup E)
    (hH : twistedCentralizer (entrywiseAut σ n).toMonoidHom δ ≤ B.leviSubgroup E) :
    TwistedFibreData (entrywiseAut σ n).toMonoidHom δ where
  U := B.unipotentSubgroup E
  isClosed_U := B.isClosed_unipotentSubgroup E
  comm _ ha _ hb := B.unipotentSubgroup_mul_comm E hB ha hb
  map_mem _ ha := B.map_mem_unipotentSubgroup E (σ : E →+* E) ha
  P := B.parabolic E
  isClosed_P := B.isClosed_parabolic E
  π := (B.leviEmbedding E).comp (B.leviProjection E)
  continuous_π :=
    (B.leviEmbeddingContinuous E).continuous.comp (B.leviProjectionContinuous E).continuous
  π_eq_one_iff p := by
    change B.leviEmbedding E (B.leviProjection E p) = 1 ↔ _
    constructor
    · intro h
      have h' : B.leviProjection E p = 1 :=
        B.leviEmbedding_injective E (h.trans (map_one _).symm)
      exact ⟨p, h', rfl⟩
    · rintro ⟨q, hq, hqp⟩
      have hq' : q = p := Subtype.ext hqp
      subst hq'
      rw [show B.leviProjection E q = 1 from hq, map_one]
  U_le_P := Subgroup.map_subtype_le _
  centralizer_le_P := hH.trans (B.leviSubgroup_le_parabolic E)
  π_eq_self p hp := by
    obtain ⟨m, hm⟩ := hH hp
    have hpm : p = B.leviInParabolic E m := Subtype.ext hm.symm
    change B.leviEmbedding E (B.leviProjection E p) = p.val
    rw [hpm, BlockShape.leviProjection_section, BlockShape.leviInParabolic_val]
  mem_P := B.leviSubgroup_le_parabolic E hδ

@[simp] theorem leviTwistedFibreData_U (hB : B.length ≤ 2) (hδ : δ ∈ B.leviSubgroup E)
    (hH : twistedCentralizer (entrywiseAut σ n).toMonoidHom δ ≤ B.leviSubgroup E) :
    (leviTwistedFibreData B σ δ hB hδ hH).U = B.unipotentSubgroup E := rfl

/-- When `E` is a finite `F`-module, the twisted conjugation `u ↦ δ⁻¹ u δ (u^σ)⁻¹` maps the
unipotent radical onto itself. -/
theorem leviTwistedFibreData_twist_surjective [Module.Finite F E] (hB : B.length ≤ 2)
    (hδ : δ ∈ B.leviSubgroup E)
    (hH : twistedCentralizer (entrywiseAut σ n).toMonoidHom δ ≤ B.leviSubgroup E) :
    Function.Surjective (leviTwistedFibreData B σ δ hB hδ hH).twist := by
  set D := leviTwistedFibreData B σ δ hB hδ hH
  let V : Submodule F (Matrix (Fin n) (Fin n) E) := B.upperBlocks E F
  let s : Matrix (Fin n) (Fin n) E →+* Matrix (Fin n) (Fin n) E := RingHom.mapMatrix (σ : E →+* E)
  have hs : ∀ g : GeneralLinear n E,
      ((entrywiseAut σ n).toMonoidHom g : Matrix (Fin n) (Fin n) E) = s g := fun _ => rfl
  have hcrit : ∀ g : GeneralLinear n E, g ∈ D.U ↔ (g : Matrix (Fin n) (Fin n) E) - 1 ∈ V :=
    fun g => B.mem_unipotentSubgroup_iff_sub_one_mem E F g
  have hsq : ∀ {Y Z : Matrix (Fin n) (Fin n) E}, Y ∈ V → Z ∈ V → Y * Z = 0 :=
    fun hY hZ => B.upperBlocks_mul_eq_zero E hB hY hZ
  -- the unipotent element `1 + Y`
  let w : V → GeneralLinear n E := fun Y =>
    { val := 1 + Y.val
      inv := 1 - Y.val
      val_inv := by
        calc (1 + Y.val) * (1 - Y.val) = 1 - Y.val * Y.val := by noncomm_ring
          _ = 1 := by rw [hsq Y.2 Y.2, sub_zero]
      inv_val := by
        calc (1 - Y.val) * (1 + Y.val) = 1 - Y.val * Y.val := by noncomm_ring
          _ = 1 := by rw [hsq Y.2 Y.2, sub_zero] }
  have hw_val : ∀ Y : V, (w Y : Matrix (Fin n) (Fin n) E) = 1 + Y.val := fun _ => rfl
  have hw_inv : ∀ Y : V, ((w Y)⁻¹ : GeneralLinear n E).val = 1 - Y.val := fun _ => rfl
  have hw : ∀ Y : V, w Y ∈ D.U := fun Y => (hcrit _).2 (by rw [hw_val, add_sub_cancel_left]; exact Y.2)
  have hδinv : ((δ⁻¹ : GeneralLinear n E) : Matrix (Fin n) (Fin n) E) * δ = 1 := Units.inv_mul δ
  have hconj : ∀ Y : V, ((δ⁻¹ : GeneralLinear n E) : Matrix (Fin n) (Fin n) E) * Y.val * δ ∈ V := by
    intro Y
    have h := (hcrit _).1 (D.inv_mul_mul_mem D.mem_P (hw Y))
    rwa [Units.val_mul, Units.val_mul, hw_val, mul_add, mul_one, add_mul, hδinv,
      add_sub_cancel_left] at h
  have hmap : ∀ Y : V, s Y.val ∈ V := by
    intro Y
    have h := (hcrit _).1 (D.map_mem _ (hw Y))
    rwa [hs, hw_val, map_add, map_one, add_sub_cancel_left] at h
  have hs_smul : ∀ (c : F) (Y : Matrix (Fin n) (Fin n) E), s (c • Y) = c • s Y := by
    intro c Y
    ext i j
    simp [s, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]
  let L : V →ₗ[F] V :=
    { toFun := fun Y => ⟨((δ⁻¹ : GeneralLinear n E) : Matrix (Fin n) (Fin n) E) * Y.val * δ -
          s Y.val, V.sub_mem (hconj Y) (hmap Y)⟩
      map_add' := by
        intro Y Z
        apply Subtype.ext
        simp only [Submodule.coe_add, mul_add, add_mul, map_add]
        abel
      map_smul' := by
        intro c Y
        apply Subtype.ext
        simp only [SetLike.val_smul, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul,
          hs_smul, smul_sub] }
  have hL : ∀ Y : V, (L Y).val =
      ((δ⁻¹ : GeneralLinear n E) : Matrix (Fin n) (Fin n) E) * Y.val * δ - s Y.val := fun _ => rfl
  -- `twist (1 + Y) = 1 + L Y`
  have htwist : ∀ Y : V, ((D.twist ⟨w Y, hw Y⟩ : GeneralLinear n E) :
      Matrix (Fin n) (Fin n) E) = 1 + (L Y).val := by
    intro Y
    rw [TwistedFibreData.twist_apply_coe]
    change (((δ⁻¹ * w Y * δ * ((entrywiseAut σ n).toMonoidHom (w Y))⁻¹ : GeneralLinear n E)) :
      Matrix (Fin n) (Fin n) E) = _
    rw [← map_inv, Units.val_mul, Units.val_mul, Units.val_mul, hs, hw_val, hw_inv, map_sub,
      map_one, mul_add, mul_one, add_mul, hδinv, hL]
    have h0 := hsq (hconj Y) (hmap Y)
    calc (1 + ((δ⁻¹ : GeneralLinear n E) : Matrix (Fin n) (Fin n) E) * Y.val * δ) * (1 - s Y.val)
        = 1 + (((δ⁻¹ : GeneralLinear n E) : Matrix (Fin n) (Fin n) E) * Y.val * δ - s Y.val) -
          ((δ⁻¹ : GeneralLinear n E) : Matrix (Fin n) (Fin n) E) * Y.val * δ * s Y.val := by
          noncomm_ring
      _ = _ := by rw [h0, sub_zero]
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun Y hY => ?_
    have h1 : D.twist ⟨w Y, hw Y⟩ = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [htwist, hY, Submodule.coe_zero, add_zero]
      rfl
    have h2 : (⟨w Y, hw Y⟩ : D.U) = 1 := D.twist_injective (h1.trans (map_one _).symm)
    have h3' : w Y = 1 := congrArg Subtype.val h2
    have h3 : (w Y : Matrix (Fin n) (Fin n) E) = 1 := by rw [h3', Units.val_one]
    apply Subtype.ext
    rw [hw_val] at h3
    rw [Submodule.coe_zero]
    simpa using h3
  have : Module.Finite F (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (Module.Finite F (Fin n → Fin n → E))
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.1 hinj
  intro v
  obtain ⟨Y, hY⟩ := hsurj ⟨(v.val : Matrix (Fin n) (Fin n) E) - 1, (hcrit _).1 v.2⟩
  refine ⟨⟨w Y, hw Y⟩, Subtype.ext (Units.ext ?_)⟩
  rw [htwist, hY]
  exact add_sub_cancel _ _

end FibreData

end Langlands.BaseChange

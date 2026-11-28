import Langlands.Algebra.CentralSimple.LandherrTensorQuadratic
import Langlands.Algebra.CentralSimple.LandherrPowNeighborhood

/-! # Local reduced norms from approximate norm-one corrections -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root
open Filter Topology
open scoped TensorProduct

universe u

variable (F E : Type u) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F]
  (B : Type u) [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]

omit [Algebra F B] [IsScalarTower F E B] [FiniteDimensional E B] [Algebra.IsCentral E B]
  [IsSimpleRing B] in
theorem conjugation_add_mul_skewRoot (p q : F) :
    conjugation F E (algebraMap F E p + algebraMap F E q * skewRoot F E) =
      algebraMap F E p - algebraMap F E q * skewRoot F E := by
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, conjugation_skewRoot, mul_neg,
    ← sub_eq_add_neg]

/-- **Local reduced norms near a Hilbert 90 point.** Let `E_w` be a complete nontrivially
normed field of characteristic zero over `E`, and let `φ : K_v → E_w` be a continuous
ring map compatible with `F → E → E_w`. Let `x` be a unit of `K_v ⊗_F B` and
`ω_v = qm P₀ Q₀` a unit with `ν(x) σ(ω_v) = (t₀ ⊗ 1) ω_v`. For `p, q ∈ F` with images close
to `(P₀, Q₀)` in `K_v × K_v`, the image of `t₀ ω / σ(ω)` for `ω = p + q r` is the reduced
norm of a unit of `E_w ⊗_E B`. -/
theorem exists_reducedNorm_near_hilbert90
    {Kv : Type u} [Field Kv] [TopologicalSpace Kv] [Algebra F Kv]
    {Ew : Type u} [NontriviallyNormedField Ew] [CompleteSpace Ew] [CharZero Ew] [Algebra E Ew]
    (φ : Kv →+* Ew) (hφ : Continuous φ)
    (hφF : ∀ x : F, φ (algebraMap F Kv x) = algebraMap E Ew (algebraMap F E x))
    (x : (Kv ⊗[F] B)ˣ) (t₀ : E) (P₀ Q₀ : Kv) (hω : IsUnit (qm F E Kv P₀ Q₀))
    (hδ : relNorm F E B Kv x * tensorConj F E Kv (qm F E Kv P₀ Q₀) =
      (t₀ ⊗ₜ[F] (1 : Kv)) * qm F E Kv P₀ Q₀) :
    ∃ U ∈ 𝓝 (P₀, Q₀), ∀ p q : F, (algebraMap F Kv p, algebraMap F Kv q) ∈ U →
      algebraMap F E p + algebraMap F E q * skewRoot F E ≠ 0 ∧
      ∃ z : (Ew ⊗[E] B)ˣ, reducedNorm E B Ew (z : Ew ⊗[E] B) =
        algebraMap E Ew (t₀ * (algebraMap F E p + algebraMap F E q * skewRoot F E) /
          conjugation F E (algebraMap F E p + algebraMap F E q * skewRoot F E)) := by
  classical
  let _ : Algebra F Ew := ((algebraMap E Ew).comp (algebraMap F E)).toAlgebra
  have : IsScalarTower F E Ew := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let φF : Kv →ₐ[F] Ew := { φ with commutes' := fun x => hφF x }
  let ψ : E ⊗[F] Kv →ₐ[E] Ew :=
    Algebra.TensorProduct.lift (Algebra.ofId E Ew) φF (fun _ _ => Commute.all _ _)
  have hψ : ∀ (e : E) (k : Kv), ψ (e ⊗ₜ k) = algebraMap E Ew e * φ k := fun e k => by
    simp [ψ, φF, Algebra.ofId_apply]
  set rw := algebraMap E Ew (skewRoot F E) with hrw
  have hψqm : ∀ P Q : Kv, ψ (qm F E Kv P Q) = φ P + rw * φ Q := fun P Q => by
    rw [qm, map_add, hψ, hψ, map_one, one_mul]
  have hψconj : ∀ P Q : Kv, ψ (tensorConj F E Kv (qm F E Kv P Q)) = φ P - rw * φ Q := fun P Q => by
    rw [tensorConj_qm, hψqm, map_neg, mul_neg, sub_eq_add_neg]
  have hψt : ψ (t₀ ⊗ₜ[F] (1 : Kv)) = algebraMap E Ew t₀ := by rw [hψ, map_one, mul_one]
  set N₀ := φ P₀ + rw * φ Q₀ with hN₀
  set D₀ := φ P₀ - rw * φ Q₀ with hD₀
  have hN0 : N₀ ≠ 0 := by
    rw [hN₀, ← hψqm]
    exact (hω.map ψ).ne_zero
  have hD0 : D₀ ≠ 0 := by
    rw [hD₀, ← hψconj]
    exact ((hω.map (tensorConj F E Kv)).map ψ).ne_zero
  set δw := ψ (relNorm F E B Kv x) with hδw
  have hδw0 : δw ≠ 0 := by
    have hu : IsUnit (relNorm F E B Kv x) :=
      ((x.isUnit.map (UnitaryPoints.tensorEquiv F E B Kv)).map (reducedNorm E B (E ⊗[F] Kv)))
    exact (hu.map ψ).ne_zero
  have hrel : δw * D₀ = algebraMap E Ew t₀ * N₀ := by
    have := congrArg ψ hδ
    rwa [map_mul, map_mul, hψconj, hψt, hψqm] at this
  set κ := D₀ / N₀ with hκ
  have hn : reducedDegree E B ≠ 0 := (reducedDegree_pos E B).ne'
  have h1 : κ * N₀ / D₀ = 1 := by
    rw [hκ]
    field_simp
  obtain hU := ratio_preimage_mem_nhds φ hφ rw κ P₀ Q₀ hD0 h1 (powSet_mem_nhds (K := Ew) hn)
  refine ⟨_, hU, fun p q hpq => ?_⟩
  obtain ⟨s, hs0, hs⟩ := hpq
  dsimp only at hs
  set ω := algebraMap F E p + algebraMap F E q * skewRoot F E with hω_def
  have hωw : algebraMap E Ew ω = φ (algebraMap F Kv p) + rw * φ (algebraMap F Kv q) := by
    rw [hω_def, map_add, map_mul, hφF, hφF, hrw, mul_comm]
  have hσωw : algebraMap E Ew (conjugation F E ω) =
      φ (algebraMap F Kv p) - rw * φ (algebraMap F Kv q) := by
    rw [hω_def, conjugation_add_mul_skewRoot, map_sub, map_mul, hφF, hφF, hrw, mul_comm]
  have hsn : s ^ reducedDegree E B ≠ 0 := pow_ne_zero _ hs0
  rw [hs] at hsn
  have hden : φ (algebraMap F Kv p) - rw * φ (algebraMap F Kv q) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hsn
    exact hsn rfl
  have hnum : φ (algebraMap F Kv p) + rw * φ (algebraMap F Kv q) ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_div] at hsn
    exact hsn rfl
  refine ⟨fun h0 => hnum (by rw [← hωw, h0, map_zero]), ?_⟩
  let xw : (Ew ⊗[E] B)ˣ := Units.map
    ((Algebra.TensorProduct.map ψ (AlgHom.id E B)).toMonoidHom.comp
      (UnitaryPoints.tensorEquiv F E B Kv).toMonoidHom) x
  have hxw : reducedNorm E B Ew (xw : Ew ⊗[E] B) = δw := by
    change reducedNorm E B Ew (Algebra.TensorProduct.map ψ (AlgHom.id E B)
      (UnitaryPoints.tensorEquiv F E B Kv x)) = _
    rw [reducedNorm_naturality]
    rfl
  let sw : (Ew ⊗[E] B)ˣ := Units.map (Algebra.TensorProduct.includeLeft (R := E) (S := E)
    (A := Ew) (B := B)).toMonoidHom (Units.mk0 s hs0)
  have hsw : reducedNorm E B Ew (sw : Ew ⊗[E] B) = s ^ reducedDegree E B := by
    change reducedNorm E B Ew (s ⊗ₜ[E] (1 : B)) = _
    rw [reducedNorm_scalar]
  refine ⟨xw * sw, ?_⟩
  rw [Units.val_mul, map_mul, hxw, hsw, hs, map_div₀, map_mul, hωw, hσωw]
  have ht : algebraMap E Ew t₀ = δw * D₀ / N₀ := by
    rw [hrel]
    field_simp
  rw [ht, hκ]
  field_simp

end Langlands.CentralSimple.Landherr

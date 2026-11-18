import Langlands.Representation.Jacquet.RationalInducedFixedVectors
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Jacquet.NormalizedFixedVectorBridge
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDirectSum

/-! # Uniform nilpotence on fixed levels of unramified induced Jacquet families -/

noncomputable section

open scoped NNReal

namespace Langlands.HarishChandraSchwartz

/-- A simultaneous generalized eigenvector in a finite-dimensional stable
space is killed at each group element by the corresponding linear factor raised
to any bound on that space's dimension. -/
theorem pow_eq_zero_of_mem_jointGenEigenspace_of_finrank_le
    {A : Type*} [CommGroup A] {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (T : A →* Module.End ℂ Y) (W : Submodule ℂ Y) [FiniteDimensional ℂ W]
    (hW : ∀ a, ∀ x ∈ W, T a x ∈ W) {d : ℕ} (hd : Module.finrank ℂ W ≤ d)
    {χ : A → ℂ} {y : Y} (hyW : y ∈ W) (hy : y ∈ jointGenEigenspace T χ) (a : A) :
    ((T a - χ a • 1) ^ d) y = 0 := by
  obtain ⟨k, hk⟩ := mem_jointGenEigenspace.mp hy a
  have hmaps : ∀ x ∈ W, (T a - χ a • 1) x ∈ W := fun x hx => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact W.sub_mem (hW a x hx) (W.smul_mem _ hx)
  let f := (T a - χ a • 1).restrict hmaps
  have hpow : ∀ n, ((f ^ n) ⟨y, hyW⟩ : Y) = ((T a - χ a • 1) ^ n) y := fun n => by
    rw [Module.End.pow_restrict]
    rfl
  have hk' : (⟨y, hyW⟩ : W) ∈ LinearMap.ker (f ^ k) := by
    rw [LinearMap.mem_ker]
    ext
    rw [hpow, hk]
    rfl
  have hfin := Module.End.ker_pow_le_ker_pow_finrank f k hk'
  rw [LinearMap.mem_ker] at hfin
  have hzero : ((T a - χ a • 1) ^ Module.finrank ℂ W) y = 0 := by
    rw [← hpow, hfin]
    rfl
  calc
    ((T a - χ a • 1) ^ d) y =
        ((T a - χ a • 1) ^ (d - Module.finrank ℂ W))
          (((T a - χ a • 1) ^ Module.finrank ℂ W) y) := by
      rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel hd]
    _ = 0 := by rw [hzero, map_zero]

end Langlands.HarishChandraSchwartz

namespace Langlands.Jacquet

open Aubert.General Plancherel

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M)

/-- The compact-open fixed dimension of the untwisted actual normalized
induction; this integer will bound all twisted Jacquet nilpotence orders at the
corresponding fixed Levi level. -/
def inducedFixedNilpotenceOrder (K : OpenSubgroup G) : ℕ :=
  Module.finrank ℂ (fixedVectors ((normalizedInductionFunctor h hU).obj A).representation
    K.toSubgroup)

variable (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (K0 : OpenSubgroup G) (hK0 : IsCompact (K0 : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K0, g = (p : G) * (k : G))
  (hA : A.IsAdmissible)
  (N' M' Nbar' : Subgroup G) (hN' : IsClosed (N' : Set G))
  (hM' : IsClosed (M' : Set G)) (hM'N' : M' ≤ Subgroup.normalizer N')

include hP hm hν hK0 hPK hA hM' in
/-- On a compact-open Iwahori contraction level, every unramified twist of the
actual normalized induction has a normalized Jacquet fixed space of dimension at
most the untwisted induced fixed dimension. -/
theorem finrank_fixed_normalizedJacquet_unramifiedInduction_le
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {g : G}
    (hcontr : IsIwahoriContraction K N' M' Nbar' g)
    (ψ : unramifiedCharacters ν) :
    let Vψ := (normalizedInductionFunctor h hU).obj
      (A.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ))
    let Jψ := (normalizedJacquetFunctor N' M' hN' hM'N').obj Vψ
    FiniteDimensional ℂ (fixedVectors Jψ.representation (K.toSubgroup.comap M'.subtype)) ∧
      Module.finrank ℂ (fixedVectors Jψ.representation (K.toSubgroup.comap M'.subtype)) ≤
        inducedFixedNilpotenceOrder h hU A K := by
  let : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK0 (fun g => by
      obtain ⟨p, k, hg⟩ := hPK g
      exact ⟨p, p.property, k, k.property, hg⟩)
  have hbase := normalizedInductionFunctor_obj_isAdmissible h hU hm A hA
  have := hbase.2 K
  let Vψ := (normalizedInductionFunctor h hU).obj
    (A.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ))
  let Jψ := (normalizedJacquetFunctor N' M' hN' hM'N').obj Vψ
  let e := normalizedInductionCompactTrivialTwistFixedVectorsEquiv h hU hP A K hK
    ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ)
    (Induction.compactSubgroup_le_unramifiedPullback_ker ν hν h.projection hm ψ)
  have hfin : FiniteDimensional ℂ (fixedVectors Vψ.representation K.toSubgroup) :=
    Module.Finite.of_injective e.toLinearMap e.injective
  have hsurj := fixedJacquetMap_surjective_of_iwahoriContraction
    Vψ.representation Vψ.isSmooth hK hcontr hM'N' hfin
  have hunfin := finiteDimensional_fixedVectors_action_of_iwahoriContraction
    Vψ.representation Vψ.isSmooth hK hcontr hM'N' hfin
  let eJ := NormalizedJacquetBridge.normalizedFixedVectorsEquiv N' M' hN' hM'N' hM' K hK Vψ
  have hjfin : FiniteDimensional ℂ
      (fixedVectors Jψ.representation (K.toSubgroup.comap M'.subtype)) :=
    Module.Finite.of_injective eJ.toLinearMap eJ.injective
  refine ⟨hjfin, ?_⟩
  calc
    Module.finrank ℂ (fixedVectors Jψ.representation (K.toSubgroup.comap M'.subtype)) =
        Module.finrank ℂ (fixedVectors (action Vψ.representation N' M' hM'N')
          (K.toSubgroup.comap M'.subtype)) := eJ.finrank_eq
    _ ≤ Module.finrank ℂ (fixedVectors Vψ.representation K.toSubgroup) :=
      LinearMap.finrank_le_finrank_of_surjective hsurj
    _ = inducedFixedNilpotenceOrder h hU A K := e.finrank_eq

include hP hm hν hK0 hPK hA hM' in
/-- Every simultaneous generalized eigenvector of a central component in the
fixed normalized Jacquet space has nilpotence order bounded by the same untwisted
induced fixed dimension, independently of the unramified parameter. -/
theorem pow_inducedFixedNilpotenceOrder_eq_zero
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {g : G}
    (hcontr : IsIwahoriContraction K N' M' Nbar' g)
    {C : Type*} [CommGroup C] (j : C →* M')
    (hj : ∀ c m, j c * m = m * j c) (ψ : unramifiedCharacters ν)
    {χ : C → ℂ} :
    let Vψ := (normalizedInductionFunctor h hU).obj
      (A.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ))
    let Jψ := (normalizedJacquetFunctor N' M' hN' hM'N').obj Vψ
    ∀ y : Jψ, y ∈ fixedVectors Jψ.representation (K.toSubgroup.comap M'.subtype) →
      y ∈ HarishChandraSchwartz.jointGenEigenspace (Jψ.representation.comp j) χ →
      ∀ c, ((Jψ.representation (j c) - χ c • 1) ^
        inducedFixedNilpotenceOrder h hU A K) y = 0 := by
  intro Vψ Jψ y hy hχ c
  obtain ⟨hfin, hdim⟩ := finrank_fixed_normalizedJacquet_unramifiedInduction_le
    h hU A hP hm ν hν K0 hK0 hPK hA N' M' Nbar' hN' hM' hM'N' K hK hcontr ψ
  have := hfin
  exact HarishChandraSchwartz.pow_eq_zero_of_mem_jointGenEigenspace_of_finrank_le
    (Jψ.representation.comp j) (fixedVectors Jψ.representation (K.toSubgroup.comap M'.subtype))
    (fun a x hx => HarishChandraSchwartz.apply_mem_fixedVectors_of_central
      Jψ.representation j hj _ a hx) hdim hy hχ c

end Langlands.Jacquet

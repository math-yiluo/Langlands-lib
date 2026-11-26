import Langlands.BushnellKutzko.PureStratumApproximationChainLift
import Langlands.BushnellKutzko.TameCorestrictionProof
import Langlands.BushnellKutzko.RefinementProof

/-! # Two chains normalized by one field

For two lattice chains normalized by the same field `E`, a common relative splitting basis
reads both endomorphism filtrations from the line chain `{𝔭_E^i}`, block by block. This gives
the comparison of filtrations through their intersections with `B = End_E(V)` (BK93 (1.2.10),
printed p. 27) and lifts of corestriction values into an intersection of two filtration steps
(BK93 (1.3.12) and the remark after it, printed p. 31), in the form used in the proof of (2.4.5), printed p. 68.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

section CommonBasis

variable (𝓛 𝓛' : LatticeChain 𝒪[F] F V)
  (hL : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
  (hL' : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛'.stabilizer)

include hL hL' in
/-- Two chains normalized by `E` have a common relative splitting basis (BK93 (1.2.8) and the
common-basis property of two lattice chains, (1.1.9)). -/
theorem exists_relSplits_basis_both :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) E V),
      RelSplits (L := E) 𝓛 w ∧ RelSplits (L := E) 𝓛' w := by
  classical
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  have := LocalField.FiniteExtension.isLocalField F E
  have := 𝓛.finiteDimensional
  have : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  let C := (𝓛.subfieldChain E hL).transfer (subfieldIntegerEquiv F E) (fun _ => rfl)
  let C' := (𝓛'.subfieldChain E hL').transfer (subfieldIntegerEquiv F E) (fun _ => rfl)
  let f := (Module.finBasis E V).equivFun
  let D := C.linearEquivMap f
  let D' := C'.linearEquivMap f
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨r, β, hβ, hβ'⟩ := D.exists_basis_splits_both hπ D'
  refine ⟨r, β.map f.symm, ?_, ?_⟩
  · intro i c hc j
    have hsum : ∑ k, c k • β k ∈ D.lattice i := by
      rw [LatticeChain.mem_linearEquivMap]
      have h2 : f.symm (∑ k, c k • β k) ∈ 𝓛.lattice i := by simpa [map_sum] using hc
      exact h2
    have hterm : f.symm (c j • β j) ∈ 𝓛.lattice i :=
      (LatticeChain.mem_linearEquivMap C f i _).mp (hβ c i hsum j)
    simpa using hterm
  · intro i c hc j
    have hsum : ∑ k, c k • β k ∈ D'.lattice i := by
      rw [LatticeChain.mem_linearEquivMap]
      have h2 : f.symm (∑ k, c k • β k) ∈ 𝓛'.lattice i := by simpa [map_sum] using hc
      exact h2
    have hterm : f.symm (c j • β j) ∈ 𝓛'.lattice i :=
      (LatticeChain.mem_linearEquivMap C' f i _).mp (hβ' c i hsum j)
    simpa using hterm

end CommonBasis

section Blocks

variable {n : ℕ} (w : Module.Basis (Fin n) E V)

/-- The `E`-linear map `v ↦ (w.repr v l) • c • w j`, an `E`-multiple of a matrix unit. -/
def elementaryE (c : E) (j l : Fin n) : Module.End E V := (w.coord l).smulRight (c • w j)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] in
theorem elementaryE_apply (c : E) (j l : Fin n) (v : V) :
    elementaryE w c j l v = (w.repr v l * c) • w j := by
  simp [elementaryE, smul_smul]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [FiniteDimensional F E] in
theorem blockEntry_elementaryE (c : E) (j l j' l' : Fin n) :
    blockEntry w ((elementaryE w c j l).restrictScalars F) j' l' =
      if j' = j ∧ l' = l then LinearMap.mulLeft F c else 0 := by
  ext a
  simp only [blockEntry_apply, LinearMap.coe_restrictScalars, elementaryE_apply,
    map_smul, Module.Basis.repr_self, Finsupp.smul_apply]
  by_cases hj : j' = j <;> by_cases hl : l' = l <;>
    simp [hj, hl, mul_comm]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [FiniteDimensional F E] in
/-- The block of `x` in position `(j,l)` is the sandwich of `x` between two `E`-linear
idempotents. -/
theorem lineIncl_comp_blockEntry (x : Module.End F V) (j l : Fin n) :
    lineIncl F w j ∘ₗ blockEntry w x j l ∘ₗ lineProj F w l =
      (elementaryE w 1 j j).restrictScalars F * x * (elementaryE w 1 l l).restrictScalars F := by
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply, lineIncl_apply, lineProj_apply,
    blockEntry_apply, Module.End.mul_apply, LinearMap.coe_restrictScalars, elementaryE_apply,
    mul_one]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] in
theorem sum_elementaryE_one : ∑ j, elementaryE w 1 j j = 1 := by
  ext v
  simp only [LinearMap.sum_apply, elementaryE_apply, mul_one, Module.End.one_apply,
    w.sum_repr]

variable (𝓛 : LatticeChain 𝒪[F] F V) (hL : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

/-- An extension-uniformizer power acts on the line chain `{𝔭_E^i}` with exact depth. -/
theorem mulLeft_zpow_mem_iff {ϖ : subfieldIntegers F E} (hϖ : Irreducible ϖ) (k m : ℤ) :
    LinearMap.mulLeft F ((ϖ : E) ^ k) ∈
        (subfieldBasisChain (F := F) (Module.Basis.singleton Unit E) hϖ).endFiltration m ↔
      m ≤ k := by
  let C : LatticeChain 𝒪[F] F E :=
    subfieldBasisChain (F := F) (Module.Basis.singleton Unit E) hϖ
  have hC : ∀ u : Eˣ, subfieldUnits F E E u ∈ C.stabilizer :=
    subfieldBasisChain_normalized (Module.Basis.singleton Unit E) hϖ
  have h1 := uniformizerShift_eq_one_of_cyclic C hC hϖ (one_ne_zero : (1 : E) ≠ 0)
    (fun x => ⟨x, by simp⟩)
  have h := subfieldEmbedding_unit_mem_iff C hC (subfieldIntegerUnit E hϖ.ne_zero ^ k) m
  rw [map_zpow, Int.toAdd_zpow, h1] at h
  have he : subfieldEmbedding F E E ((subfieldIntegerUnit E hϖ.ne_zero ^ k : Eˣ) : E) =
      LinearMap.mulLeft F ((ϖ : E) ^ k) := by
    ext x
    simp [subfieldEmbedding_apply, subfieldIntegerUnit, Units.val_zpow_eq_zpow_val]
  rw [he] at h
  simpa using h

include hL in
/-- Membership in the filtration of a chain normalized by `E` is read blockwise from the line
chain `{𝔭_E^i}`, for a relative splitting basis. -/
theorem exists_blockLevels (hw : RelSplits (L := E) 𝓛 w) {ϖ : subfieldIntegers F E}
    (hϖ : Irreducible ϖ) :
    ∃ (d : ℤ) (p : Fin n → ℤ), 0 < d ∧ ∀ (x : Module.End F V) (t : ℤ),
      x ∈ 𝓛.endFiltration t ↔ ∀ j l, blockEntry w x j l ∈
        (subfieldBasisChain (F := F) (Module.Basis.singleton Unit E) hϖ).endFiltration
          (ceilDiv (t + p l - p j) d) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let C : LatticeChain 𝒪[F] F E :=
    subfieldBasisChain (F := F) (Module.Basis.singleton Unit E) hϖ
  have hC : ∀ u : Eˣ, subfieldUnits F E E u ∈ C.stabilizer :=
    subfieldBasisChain_normalized (Module.Basis.singleton Unit E) hϖ
  let d := (𝓛.fieldShift E hL (subfieldIntegerUnit E hϖ.ne_zero)).toAdd
  let p (i : Fin n) := 𝓛.index hπ (w i) - d * C.index hπ 1
  have hd : 0 < d := 𝓛.fieldShift_uniformizer_pos E hL hϖ
  have hc : ScaledLatticeCoordinates 𝓛 C w d p :=
    scaledLatticeCoordinates_of_normalizing 𝓛 C w hL hC hπ hϖ
  exact ⟨d, p, hd, fun x t => blockFiltration 𝓛 C w d p hw hd hc x t⟩

end Blocks

section Comparison

variable (𝓛 𝓛' : LatticeChain 𝒪[F] F V)
  (hL : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
  (hL' : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛'.stabilizer)

include hL hL' in
/-- **BK93 (1.2.10)**, as used on printed p. 68: for two chains normalized by `E`, an inclusion
of filtration steps holds as soon as it holds for their `E`-linear elements. -/
theorem endFiltration_le_of_restrict_le {t t' : ℤ}
    (h : ∀ y : Module.End E V, y.restrictScalars F ∈ 𝓛.endFiltration t →
      y.restrictScalars F ∈ 𝓛'.endFiltration t') :
    𝓛.endFiltration t ≤ 𝓛'.endFiltration t' := by
  classical
  obtain ⟨n, w, hw, hw'⟩ := exists_relSplits_basis_both 𝓛 𝓛' hL hL'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  obtain ⟨d, p, hd, hB⟩ := exists_blockLevels w 𝓛 hL hw hϖ
  obtain ⟨d', p', hd', hB'⟩ := exists_blockLevels w 𝓛' hL' hw' hϖ
  set C := subfieldBasisChain (F := F) (Module.Basis.singleton Unit E) hϖ
  have hlev : ∀ j l, ceilDiv (t' + p' l - p' j) d' ≤ ceilDiv (t + p l - p j) d := by
    intro j l
    let k := ceilDiv (t + p l - p j) d
    have hy : (elementaryE w ((ϖ : E) ^ k) j l).restrictScalars F ∈ 𝓛.endFiltration t := by
      rw [hB]
      intro j' l'
      rw [blockEntry_elementaryE]
      split_ifs with hjl
      · obtain ⟨rfl, rfl⟩ := hjl
        exact (mulLeft_zpow_mem_iff hϖ k _).mpr le_rfl
      · exact zero_mem _
    have hy' := (hB' _ t').mp (h _ hy) j l
    simp only [blockEntry_elementaryE, and_self, ↓reduceIte] at hy'
    exact (mulLeft_zpow_mem_iff hϖ k _).mp hy'
  intro x hx
  rw [hB']
  intro j l
  exact C.endFiltration_antitone (hlev j l) ((hB x t).mp hx j l)

include hL hL' in
/-- **BK93 (1.3.12)**, in the form used on printed p. 68: a corestriction value lying in a
filtration step of a second chain is the corestriction value of an element lying in the
corresponding steps of both chains. -/
theorem exists_corestriction_eq_of_mem (s : TameCorestriction 𝒪[F] F E V) {t t' : ℤ}
    {b : Module.End F V} (hb : b ∈ 𝓛.endFiltration t)
    (hsb : (s b).restrictScalars F ∈ 𝓛'.endFiltration t') :
    ∃ p : Module.End F V, p ∈ 𝓛.endFiltration t ∧ p ∈ 𝓛'.endFiltration t' ∧ s p = s b := by
  classical
  have := 𝓛.finiteDimensional
  obtain ⟨Z, hZ, hZb⟩ : ∃ Z, Z ∈ 𝓛'.endFiltration t' ∧ s Z = s b := by
    have h := (tameCorestriction F V E).2.2 s 𝓛' hL' t'
    have hmem : s b ∈ s '' (𝓛'.endFiltration t' : Set (Module.End F V)) := by
      rw [h]
      exact hsb
    obtain ⟨Z, hZ, hZb⟩ := hmem
    exact ⟨Z, hZ, hZb⟩
  obtain ⟨n, w, hw, hw'⟩ := exists_relSplits_basis_both 𝓛 𝓛' hL hL'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  obtain ⟨d, p, hd, hB⟩ := exists_blockLevels w 𝓛 hL hw hϖ
  obtain ⟨d', p', hd', hB'⟩ := exists_blockLevels w 𝓛' hL' hw' hϖ
  set C := subfieldBasisChain (F := F) (Module.Basis.singleton Unit E) hϖ
  let lev₁ (j l : Fin n) := ceilDiv (t + p l - p j) d
  let lev₂ (j l : Fin n) := ceilDiv (t' + p' l - p' j) d'
  let X (j l : Fin n) : Module.End F V := if lev₂ j l ≤ lev₁ j l then b else Z
  let q := assembleBlocks w (fun j l => blockEntry w (X j l) j l)
  have hbB := (hB b t).mp hb
  have hZB := (hB' Z t').mp hZ
  refine ⟨q, ?_, ?_, ?_⟩
  · rw [hB]
    intro j l
    rw [blockEntry_assembleBlocks]
    by_cases hjl : lev₂ j l ≤ lev₁ j l
    · simp only [X, hjl, ↓reduceIte]
      exact hbB j l
    · simp only [X, hjl, ↓reduceIte]
      exact C.endFiltration_antitone (le_of_lt (not_le.mp hjl)) (hZB j l)
  · rw [hB']
    intro j l
    rw [blockEntry_assembleBlocks]
    by_cases hjl : lev₂ j l ≤ lev₁ j l
    · simp only [X, hjl, ↓reduceIte]
      exact C.endFiltration_antitone hjl (hbB j l)
    · simp only [X, hjl, ↓reduceIte]
      exact hZB j l
  · have hX : ∀ j l, s (X j l) = s b := fun j l => by
      by_cases hjl : lev₂ j l ≤ lev₁ j l
      · simp only [X, hjl, ↓reduceIte]
      · simp only [X, hjl, ↓reduceIte, hZb]
    have hsand : ∀ (x : Module.End F V) (j l : Fin n),
        s ((elementaryE w 1 j j).restrictScalars F * x * (elementaryE w 1 l l).restrictScalars F) =
          elementaryE w 1 j j * s x * elementaryE w 1 l l := by
      intro x j l
      have h1 : s ((elementaryE w 1 j j).restrictScalars F *
          (x * (elementaryE w 1 l l).restrictScalars F)) =
          elementaryE w 1 j j * s (x * (elementaryE w 1 l l).restrictScalars F) :=
        s.map_mul_left _ _
      have h2 : s (x * (elementaryE w 1 l l).restrictScalars F) =
          s x * elementaryE w 1 l l := s.map_mul_right _ _
      rw [mul_assoc, h1, h2, mul_assoc]
    have hq : q = ∑ j, ∑ l, (elementaryE w 1 j j).restrictScalars F * X j l *
        (elementaryE w 1 l l).restrictScalars F := by
      simp only [q, assembleBlocks, lineIncl_comp_blockEntry]
    have hb' : s b = ∑ j, ∑ l, elementaryE w 1 j j * s b * elementaryE w 1 l l := by
      rw [← Finset.sum_mul_sum, ← Finset.sum_mul, sum_elementaryE_one, one_mul, mul_one]
    rw [hq, map_sum s.toAddMonoidHom, hb']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum s.toAddMonoidHom]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsand, hX]

end Comparison

end Langlands.BushnellKutzko.PureApproximation

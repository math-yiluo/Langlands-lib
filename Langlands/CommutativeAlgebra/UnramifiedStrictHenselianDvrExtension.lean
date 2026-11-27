import Langlands.CommutativeAlgebra.UnramifiedStrictHenselianDvrExtensionStatement
import Langlands.CommutativeAlgebra.StrictHenselianDvrExtension
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.FieldTheory.SeparableDegree

/-! # Unramified strictly Henselian DVR extensions with separable residue extension -/

noncomputable section

universe u

open Polynomial IsLocalRing Module

namespace Langlands.CommutativeAlgebra

section Predicates

variable {R Ω : Type*} [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]

/-- Every element of `S` is, modulo the image of `t`, a root of a monic polynomial over
`R` whose reduction modulo the maximal ideal of `R` is separable. -/
def SeparableResidues (t : R) (S : Subalgebra R Ω) : Prop :=
  ∀ y : S, ∃ f : R[X], f.Monic ∧ (f.map (residue R)).Separable ∧
    ∃ z : S, aeval y f = algebraMap R S t * z

/-- The fixed-uniformizer condition together with separability of residues. -/
def SeparableFixedUniformizer (t : R) (S : Subalgebra R Ω) : Prop :=
  FixedUniformizer t S ∧ SeparableResidues t S

end Predicates

/-- In a discrete valuation ring `T` over `R` in which the image of `t` is a uniformizer
and whose residue field is separable over that of `R`, every element is a root modulo
`t` of a monic polynomial with separable reduction. -/
theorem exists_monic_separable_of_isSeparable {R : Type*} [CommRing R] [IsLocalRing R]
    {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Algebra R T]
    [IsLocalHom (algebraMap R T)] {t : R} (htT : Irreducible (algebraMap R T t))
    [Algebra.IsSeparable (ResidueField R) (ResidueField T)] (w : T) :
    ∃ f : R[X], f.Monic ∧ (f.map (residue R)).Separable ∧
      ∃ z : T, aeval w f = algebraMap R T t * z := by
  let c := residue T w
  let p := minpoly (ResidueField R) c
  have hpm : p.Monic := minpoly.monic (Algebra.IsSeparable.isIntegral _ c)
  have hpsep : p.Separable := Algebra.IsSeparable.isSeparable _ c
  obtain ⟨f, hfmap, _, hf⟩ := lifts_and_degree_eq_and_monic
    (mem_lifts_of_surjective (residue_surjective (R := R)) p) hpm
  refine ⟨f, hf, hfmap ▸ hpsep, ?_⟩
  have h0 : residue T (aeval w f) = 0 := by
    have h1 : residue T (aeval w f) = aeval c f := by
      rw [← ResidueField.algebraMap_eq, ← aeval_algebraMap_apply]
      rfl
    have h2 : aeval c f = aeval c p := by
      rw [← hfmap, ← ResidueField.algebraMap_eq, aeval_map_algebraMap]
    rw [h1, h2]
    exact minpoly.aeval _ c
  have hmem : aeval w f ∈ maximalIdeal T := (residue_eq_zero_iff _).mp h0
  rw [htT.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz⟩

namespace SeparableFixedUniformizer

variable {R Ω : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field Ω] [Algebra R Ω]

theorem bot [FaithfulSMul R Ω] {t : R} (ht : Irreducible t) :
    SeparableFixedUniformizer t (⊥ : Subalgebra R Ω) := by
  refine ⟨FixedUniformizer.bot ht, fun y => ?_⟩
  obtain ⟨r, hr⟩ := Algebra.mem_bot.mp y.property
  have hy : y = algebraMap R (⊥ : Subalgebra R Ω) r := Subtype.ext hr.symm
  refine ⟨X - C r, monic_X_sub_C r, ?_, 0, ?_⟩
  · rw [Polynomial.map_sub, map_X, map_C]
    exact separable_X_sub_C
  · rw [hy, mul_zero, map_sub, aeval_X, aeval_C, sub_self]

theorem iSup {ι : Type*} [Nonempty ι] {t : R} (S : ι → Subalgebra R Ω)
    (hS : ∀ i, SeparableFixedUniformizer t (S i)) (hdir : Directed (· ≤ ·) S) :
    SeparableFixedUniformizer t (⨆ i, S i) := by
  refine ⟨FixedUniformizer.iSup S (fun i => (hS i).1) hdir, fun y => ?_⟩
  have hmem : (y : Ω) ∈ ⋃ i, (S i : Set Ω) := by
    rw [← Subalgebra.coe_iSup_of_directed hdir]
    exact y.property
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨f, hf, hsep, z, hz⟩ := (hS i).2 ⟨y, hi⟩
  let j : S i →ₐ[R] (⨆ i, S i : Subalgebra R Ω) := Subalgebra.inclusion (le_iSup S i)
  refine ⟨f, hf, hsep, j z, ?_⟩
  have hy : y = j ⟨y, hi⟩ := rfl
  rw [hy, aeval_algHom_apply, hz, map_mul, AlgHom.commutes]

theorem exists_maximal [FaithfulSMul R Ω] {t : R} (ht : Irreducible t) :
    ∃ S : Subalgebra R Ω, Maximal (SeparableFixedUniformizer t) S := by
  classical
  apply zorn_le_nonempty₀ {S : Subalgebra R Ω | SeparableFixedUniformizer t S} ?_
    (⊥ : Subalgebra R Ω) (bot ht) |>.imp fun S h => h.2
  intro c hc hchain S₀ hS₀
  let : Nonempty c := ⟨⟨S₀, hS₀⟩⟩
  let F : c → Subalgebra R Ω := Subtype.val
  have hdir : Directed (· ≤ ·) F := by
    intro i j
    rcases hchain.total i.property j.property with h | h
    · exact ⟨j, h, le_rfl⟩
    · exact ⟨i, le_rfl, h⟩
  exact ⟨⨆ i, F i, iSup F (fun i => hc i.property) hdir,
    fun S hS => le_iSup F ⟨S, hS⟩⟩

/-- Separable residues give a separable residue field extension. -/
theorem isSeparable_residueField {t : R} {S : Subalgebra R Ω}
    (hS : SeparableFixedUniformizer t S) [IsDiscreteValuationRing S]
    [IsLocalHom (algebraMap R S)] :
    Algebra.IsSeparable (ResidueField R) (ResidueField S) := by
  refine ⟨fun c => ?_⟩
  obtain ⟨y, rfl⟩ := residue_surjective c
  obtain ⟨f, _, hsep, z, hz⟩ := hS.2 y
  have hroot : aeval (residue S y) (f.map (residue R)) = 0 := by
    have h1 : aeval (residue S y) (f.map (residue R)) = residue S (aeval y f) := by
      rw [← ResidueField.algebraMap_eq (R := R), aeval_map_algebraMap,
        ← ResidueField.algebraMap_eq (R := S), aeval_algebraMap_apply]
    rw [h1, hz, map_mul, (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hS.1.1),
      zero_mul]
  exact hsep.of_dvd (minpoly.dvd _ _ hroot)

variable [IsAlgClosed Ω] [FaithfulSMul R Ω] {t : R} {S : Subalgebra R Ω}
  (ht : Irreducible t) (hmax : Maximal (SeparableFixedUniformizer t) S)
  [IsDiscreteValuationRing S]

include ht hmax

/-- A local essentially etale extension of a maximal separable fixed-uniformizer
subalgebra is already generated by its base. -/
theorem algebraMap_surjective
    (T : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra S T] [IsLocalHom (algebraMap S T)] [Algebra.EssFiniteType S T]
    [Algebra.FormallyUnramified S T] [Module.Flat S T] :
    Function.Surjective (algebraMap S T) := by
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  have hRS : IsLocalHom (algebraMap R S) := FixedUniformizer.isLocalHom ht hmax.1.1
  have hRT : IsLocalHom (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R S T]
    infer_instance
  have : Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
    isSeparable_residueField hmax.1
  have : Algebra.IsSeparable (ResidueField R) (ResidueField T) :=
    Algebra.IsSeparable.trans (ResidueField R) (ResidueField S) (ResidueField T)
  obtain ⟨e, he⟩ := EtaleDvrExtensions.exists_injective_algHom (R := S) T Ω
  let eR : T →ₐ[R] Ω := e.restrictScalars R
  let U : Subalgebra R Ω := eR.range
  let eU : T ≃ₐ[R] U := AlgEquiv.ofInjective eR he
  have htT : Irreducible (algebraMap S T (algebraMap R S t)) :=
    EtaleDvrExtensions.irreducible_algebraMap (FixedUniformizer.irreducible hmax.1.1)
  have htT' : Irreducible (algebraMap R T t) := by
    rwa [IsScalarTower.algebraMap_apply R S T]
  have hT := FixedUniformizer.of_irreducible htT
  have hcomm : eU (algebraMap S T (algebraMap R S t)) = algebraMap R U t := by
    rw [← IsScalarTower.algebraMap_apply R S T, eU.commutes]
  have hU : SeparableFixedUniformizer t U := by
    refine ⟨⟨?_, fun y => ?_⟩, fun y => ?_⟩
    · intro h
      apply hT.1
      simpa only [← hcomm, eU.symm_apply_apply] using h.map eU.symm
    · rcases hT.2 (eU.symm y) with h0 | ⟨n, z, hz, h⟩
      · exact Or.inl (eU.symm.injective (by simpa only [map_zero] using h0))
      · refine Or.inr ⟨n, eU z, hz.map eU, ?_⟩
        simpa only [eU.apply_symm_apply, map_mul, map_pow, hcomm] using congrArg eU h
    · obtain ⟨f, hf, hsep, z, hz⟩ := exists_monic_separable_of_isSeparable htT' (eU.symm y)
      refine ⟨f, hf, hsep, eU z, ?_⟩
      calc aeval y f = aeval (eU (eU.symm y)) f := by rw [eU.apply_symm_apply]
        _ = eU (aeval (eU.symm y) f) := aeval_algHom_apply (eU : T →ₐ[R] U) _ _
        _ = algebraMap R U t * eU z := by rw [hz, map_mul, eU.commutes]
  have hSU : S ≤ U := by
    intro x hx
    exact ⟨algebraMap S T ⟨x, hx⟩, e.commutes ⟨x, hx⟩⟩
  have hUS : U ≤ S := hmax.2 hU hSU
  intro y
  let a : S := ⟨e y, hUS (eR.mem_range_self y)⟩
  exact ⟨a, he (e.commutes a)⟩

/-- Every prescribed simple root at a field point comes from the maximal subalgebra. -/
theorem exists_root_of_simple (f : S[X]) (hf : f.Monic)
    {K : Type*} [Field K] (φ : S →+* K) (hφ : RingHom.ker φ = maximalIdeal S)
    (x : K) (hx : f.eval₂ φ x = 0) (hx' : f.derivative.eval₂ φ x ≠ 0) :
    ∃ a : S, aeval a f = 0 ∧ φ a = x := by
  obtain ⟨T, _, _, _, _, _, _, _, _, y, ψ, hy, hcomp, hψ⟩ :=
    EtaleDvrExtensions.exists_root_extension S f hf φ hφ x hx hx'
  have : Module.FaithfullyFlat S T := .of_flat_of_isLocalHom
  obtain ⟨a, ha⟩ := algebraMap_surjective ht hmax T y
  refine ⟨a, ?_, ?_⟩
  · apply FaithfulSMul.algebraMap_injective S T
    rw [← aeval_algebraMap_apply, ha, hy, map_zero]
  · rw [← hcomp, RingHom.comp_apply, ha, hψ]

/-- The maximal subalgebra is Henselian. -/
theorem henselianLocalRing : HenselianLocalRing S := by
  constructor
  intro f hf a₀ h₀ h'
  obtain ⟨a, ha, ha₀⟩ := exists_root_of_simple ht hmax f hf (residue S) ker_residue
    (residue S a₀)
    (by simpa only [eval₂_at_apply, residue_eq_zero_iff] using h₀)
    (by simpa only [eval₂_at_apply] using (h'.map (residue S)).ne_zero)
  refine ⟨a, ?_, ?_⟩
  · simpa [aeval_def, IsRoot.def] using ha
  · rw [← residue_eq_zero_iff, map_sub, ha₀, sub_self]

/-- The residue field of the maximal subalgebra is separably closed. -/
theorem isSepClosed_residueField : IsSepClosed (ResidueField S) := by
  apply IsSepClosed.of_exists_root
  intro p hp hirr hsep
  obtain ⟨f, hfmap, _, hf⟩ := lifts_and_degree_eq_and_monic
    (mem_lifts_of_surjective (residue_surjective (R := S)) p) hp
  let K := AlgebraicClosure (ResidueField S)
  let φ : S →+* K := (algebraMap (ResidueField S) K).comp (residue S)
  have hφ : RingHom.ker φ = maximalIdeal S := by
    ext s
    change algebraMap (ResidueField S) K (residue S s) = 0 ↔ s ∈ maximalIdeal S
    rw [← (algebraMap (ResidueField S) K).map_zero,
      (algebraMap (ResidueField S) K).injective.eq_iff, residue_eq_zero_iff]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero K p
    (degree_pos_of_irreducible hirr).ne'
  have hxf : f.eval₂ φ x = 0 := by
    dsimp only [φ]
    rw [← eval₂_map, hfmap]
    exact hx
  have hxf' : f.derivative.eval₂ φ x ≠ 0 := by
    dsimp only [φ]
    rw [← eval₂_map, ← derivative_map, hfmap]
    exact hsep.aeval_derivative_ne_zero hx
  obtain ⟨a, ha, _⟩ := exists_root_of_simple ht hmax f hf φ hφ x hxf hxf'
  refine ⟨residue S a, ?_⟩
  have hae : f.eval a = 0 := by simpa [aeval_def] using ha
  rw [← hfmap, eval_map, eval₂_at_apply, hae, map_zero]

end SeparableFixedUniformizer

/-- Every discrete valuation ring has an unramified strictly Henselian discrete
valuation ring extension with separable residue extension, in the same universe. -/
theorem unramifiedStrictHenselianDvrExtension :
    UnramifiedStrictHenselianDvrExtensionStatement.{u} := by
  intro R _ _ _
  let Ω := AlgebraicClosure (FractionRing R)
  have : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).mpr (by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) Ω]
    exact (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R _))
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨S, hS⟩ := SeparableFixedUniformizer.exists_maximal (Ω := Ω) ht
  have : IsDiscreteValuationRing S := FixedUniformizer.isDiscreteValuationRing ht.ne_zero hS.1.1
  have : HenselianLocalRing S := SeparableFixedUniformizer.henselianLocalRing ht hS
  have : IsSepClosed (ResidueField S) := SeparableFixedUniformizer.isSepClosed_residueField ht hS
  have : IsLocalHom (algebraMap R S) := FixedUniformizer.isLocalHom ht hS.1.1
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, SeparableFixedUniformizer.isSeparable_residueField hS.1⟩
  rw [ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    (FixedUniformizer.irreducible hS.1.1).maximalIdeal_eq]

end Langlands.CommutativeAlgebra

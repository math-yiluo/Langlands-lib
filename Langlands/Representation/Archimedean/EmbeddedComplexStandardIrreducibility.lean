import Langlands.Representation.Archimedean.ComplexStandardScalarVector
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientUniqueProof
import Langlands.Representation.Archimedean.ComplexStandardPermutationProof
import Langlands.Representation.FreeMonoidGenerators
import Langlands.Representation.IsotypicRestriction
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # Complex standard modules embedded in an isotypic module -/

noncomputable section

set_option autoImplicit false

open scoped MonoidAlgebra TensorProduct

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean Langlands.FreeMonoidGenerators

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem nonempty_moduleEquiv_of_isotypic_scalar_vector
    {R M S : Type*} [Ring R] [Algebra ℂ R]
    [AddCommGroup M] [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
    [AddCommGroup S] [Module ℂ S] [Module R S] [IsScalarTower ℂ R S]
    [IsSimpleModule R S]
    (h : isotypicComponent R M S = ⊤) {x : M} (hx : x ≠ 0)
    (scalar : ∀ E : M →ₗ[R] M, ∃ c : ℂ, E x = c • x) :
    Nonempty (M ≃ₗ[R] S) := by
  classical
  let eC : M ≃ₗ[R] isotypicComponent R M S :=
    Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _ h.symm)
  have : IsSemisimpleModule R M := IsSemisimpleModule.of_injective eC.toLinearMap eC.injective
  obtain ⟨ι, ⟨e⟩⟩ := ((isotypicComponent_eq_top_iff (R := R) (M := M) (S := S)).mp h).linearEquiv_finsupp
  obtain ⟨i, hi⟩ : ∃ i : ι, e x i ≠ 0 := by
    by_contra! hz
    apply hx
    apply e.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using hz i
  have hj (j : ι) : j = i := by
    by_contra hji
    let E : M →ₗ[R] M :=
      e.symm.toLinearMap ∘ₗ Finsupp.lsingle j ∘ₗ Finsupp.lapply i ∘ₗ e.toLinearMap
    obtain ⟨c, hc⟩ := scalar E
    have he : Finsupp.single j (e x i) = c • e x := by
      simpa [E] using congrArg (e.restrictScalars ℂ) hc
    have hz : c • e x i = 0 := by
      have hsi := congrArg (fun f : ι →₀ S => f i) he
      simpa [Finsupp.single_apply, hji, Ne.symm hji] using hsi.symm
    have hc0 := (smul_eq_zero.mp hz).resolve_right hi
    have hsj := congrArg (fun f : ι →₀ S => f j) he
    exact hi (by simpa [hc0] using hsj)
  have : Subsingleton ι := ⟨fun j l => (hj j).trans (hj l).symm⟩
  exact ⟨e.trans (Finsupp.uniqueLinearEquiv R S i)⟩

private theorem isotypicComponent_eq_top_of_intertwiner_ranges
    {G V W : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G W) [ρ.IsIrreducible]
    (h : ⨆ f : ρ.IntertwiningMap τ, LinearMap.range f.toLinearMap = ⊤) :
    isotypicComponent ℂ[G] τ.asModule ρ.asModule = ⊤ := by
  let P := isotypicComponent ℂ[G] τ.asModule ρ.asModule
  have hmap : (P.restrictScalars ℂ).map τ.asModuleEquiv.toLinearMap = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← h]
    refine iSup_le fun f _ hx => ?_
    obtain ⟨x, rfl⟩ := hx
    let f' := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ f
    have hx' : f' (ρ.asModuleEquiv.symm x) ∈ P := by
      change _ ∈ isotypicComponent ℂ[G] τ.asModule ρ.asModule
      rw [CompactSplitting.isotypicComponent_eq_iSup_range]
      exact (le_iSup (fun g : ρ.asModule →ₗ[ℂ[G]] τ.asModule => LinearMap.range g) f')
        ⟨ρ.asModuleEquiv.symm x, rfl⟩
    exact ⟨_, hx', rfl⟩
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  have hx : τ.asModuleEquiv x ∈ (P.restrictScalars ℂ).map τ.asModuleEquiv.toLinearMap := by
    rw [hmap]
    trivial
  obtain ⟨y, hy, he⟩ := hx
  exact (τ.asModuleEquiv.injective he) ▸ hy

section Complex

variable {n : ℕ} {V W : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

local notation "K" => Matrix.unitaryGroup (Fin n) ℂ
local notation "L" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ
local notation "repGK" => gkRep (id : K ⊕ L → _)

set_option backward.isDefEq.respectTransparency false in
/-- A complex standard module embedded in an isotypic module is equivalent to
the irreducible type of the ambient module. The scalar vector of the standard
module forces its multiplicity to be one. -/
theorem nonempty_complexStandard_equiv_of_isotypic_embedding
    (ds : List ComplexCharacterData) (hlen : ds.length = n)
    (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (τ : Representation ℂ K W) (ξ : L →ₗ⁅ℂ⁆ Module.End ℂ W)
    (hirr : IsIrreducibleGKModule ρ π) (hiso : IsGKIsotypic ρ π τ ξ)
    (A : ComplexStandardScalarVector.KF n ds →ₗ[ℂ] W)
    (hA : IsComplexStandardIntertwining n τ ξ ds A) (hinj : Function.Injective A) :
    Nonempty ((repGK (complexStandardRep n ds) (complexStandardLie n ds)).Equiv (repGK ρ π)) := by
  let σ := repGK (complexStandardRep n ds) (complexStandardLie n ds)
  let υ := repGK ρ π
  let ζ := repGK τ ξ
  have : υ.IsIrreducible := isIrreducible_gk Function.surjective_id hirr
  have hW : isotypicComponent ℂ[FreeMonoid (K ⊕ L)] ζ.asModule υ.asModule = ⊤ :=
    isotypicComponent_eq_top_of_intertwiner_ranges υ ζ (iSup_range_gk_eq_top (dec := id) hiso)
  have hA' : A ∈ gkHoms (complexStandardRep n ds) (complexStandardLie n ds) τ ξ :=
    ⟨hA.map_rep, hA.map_lie⟩
  let f : σ.IntertwiningMap ζ := intertwiningMap A (gkGenerators_map hA')
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule σ ζ f
  have hf' : Function.Injective f' := hinj
  have hσ : isotypicComponent ℂ[FreeMonoid (K ⊕ L)] σ.asModule υ.asModule = ⊤ := by
    rw [← CompactSplitting.isotypicComponent_comap_of_injective
      ℂ[FreeMonoid (K ⊕ L)] υ.asModule f' hf', hW, Submodule.comap_top]
  obtain ⟨x, hx, hscalar⟩ := ComplexStandardScalarVector.exists_isScalarVector ds hlen
  obtain ⟨e⟩ := nonempty_moduleEquiv_of_isotypic_scalar_vector hσ
    (x := σ.asModuleEquiv.symm x) (by simpa using hx) fun E => by
      let E' := (Representation.IntertwiningMap.equivLinearMapAsModule σ σ).symm E
      obtain ⟨c, hc⟩ := hscalar E'.toLinearMap fun k y =>
        map_generator E' (Sum.inl k) y
      exact ⟨c, hc⟩
  let e' := (Representation.IntertwiningMap.equivLinearMapAsModule σ υ).symm e.toLinearMap
  exact ⟨e'.ofBijective e.bijective⟩

private theorem exists_ordered_complexStandard_intertwiner
    (ds : List ComplexCharacterData) (hlen : ds.length = n)
    (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (τ : Representation ℂ K W) (ξ : L →ₗ⁅ℂ⁆ Module.End ℂ W)
    (hirr : IsIrreducibleGKModule ρ π) (hiso : IsGKIsotypic ρ π τ ξ)
    (A : ComplexStandardScalarVector.KF n ds →ₗ[ℂ] W)
    (hA : IsComplexStandardIntertwining n τ ξ ds A) (hinj : Function.Injective A) :
    ∃ es, es.Perm ds ∧ IsComplexLanglandsOrdered es ∧
      ∃ C : ComplexStandardScalarVector.KF n es →ₗ[ℂ] V,
        C ≠ 0 ∧ IsComplexStandardIntertwining n ρ π es C := by
  obtain ⟨e⟩ := nonempty_complexStandard_equiv_of_isotypic_embedding ds hlen
    ρ π τ ξ hirr hiso A hA hinj
  have Hk (k : K) (a : ComplexStandardScalarVector.KF n ds) :
      e (complexStandardRep n ds k a) = ρ k (e a) :=
    map_generator e.toIntertwiningMap (Sum.inl k) a
  have Hl (X : L) (a : ComplexStandardScalarVector.KF n ds) :
      e (complexStandardLie n ds X a) = π X (e a) :=
    map_generator e.toIntertwiningMap (Sum.inr X) a
  have hE : IsComplexStandardIntertwining n ρ π ds e.toLinearMap :=
    (isComplexStandardIntertwining_id n ds).comp e.toLinearMap Hk (fun X => Hl (1 ⊗ₜ X))
  have : Nontrivial V := hirr.1
  have hirr' := isIrreducibleGKModule_of_injective hirr hE e.injective
    e.toLinearEquiv.toEquiv.nontrivial
  let es := ds.mergeSort complexLanglandsLE
  have hperm : es.Perm ds := List.mergeSort_perm ds complexLanglandsLE
  obtain ⟨B, hBbij, hB⟩ := complexStandardPermutation n ds es hlen hperm hirr'
  have hC := hB.comp e.toLinearMap Hk (fun X => Hl (1 ⊗ₜ X))
  refine ⟨es, hperm, isComplexLanglandsOrdered_mergeSort ds, _, ?_, hC⟩
  intro hz
  obtain ⟨y, hy⟩ := exists_ne (0 : V)
  obtain ⟨f, hf⟩ := (e.surjective.comp hBbij.2) y
  exact hy (hf.symm.trans (LinearMap.congr_fun hz f))

/-- Two complex standard modules embedded in the same isotypic module have
parameter lists that differ by a permutation. -/
theorem complexStandard_parameters_perm_of_isotypic_embeddings
    (ds es : List ComplexCharacterData) (hd : ds.length = n) (he : es.length = n)
    (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (τ : Representation ℂ K W) (ξ : L →ₗ⁅ℂ⁆ Module.End ℂ W)
    (hgk : IsComplexGKModule n ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (hadm : IsAdmissibleGKModule ρ) (hiso : IsGKIsotypic ρ π τ ξ)
    (A : ComplexStandardScalarVector.KF n ds →ₗ[ℂ] W)
    (B : ComplexStandardScalarVector.KF n es →ₗ[ℂ] W)
    (hA : IsComplexStandardIntertwining n τ ξ ds A) (hinjA : Function.Injective A)
    (hB : IsComplexStandardIntertwining n τ ξ es B) (hinjB : Function.Injective B) :
    ds.Perm es := by
  obtain ⟨d, hpermD, hordD, C, hC₀, hC⟩ :=
    exists_ordered_complexStandard_intertwiner ds hd ρ π τ ξ hirr hiso A hA hinjA
  obtain ⟨e, hpermE, hordE, D, hD₀, hD⟩ :=
    exists_ordered_complexStandard_intertwiner es he ρ π τ ξ hirr hiso B hB hinjB
  have h := complexLanglandsQuotientUnique n V ρ π d e C D hgk hirr hadm
    (hpermD.length_eq.trans hd) (hpermE.length_eq.trans he) hordD hordE hC₀ hC hD₀ hD
  exact hpermD.symm.trans (h.trans hpermE)

end Complex
end Langlands.Archimedean

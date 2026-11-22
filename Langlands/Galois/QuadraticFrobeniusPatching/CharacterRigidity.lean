import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.SimpleModule.Isotypic

/-! # Character rigidity for finite dimensional semisimple representations -/

noncomputable section

namespace Langlands.GaloisRepresentation.QuadraticFrobeniusPatching

open LinearMap Submodule
open scoped MonoidAlgebra

section Algebra

variable {k R J M N : Type*} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup J] [Module R J] [Module k J] [IsScalarTower k R J]
  [AddCommGroup M] [Module R M] [Module k M] [towerM : IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [towerN : IsScalarTower k R N]

/-- Jacobson density realizes the projection to an isotypic summand as the action
of an algebra element. -/
private theorem exists_isotypic_projection [FiniteDimensional k J] [IsSemisimpleModule R J]
    (c : isotypicComponents R J) :
    ∃ r : R, LinearMap.IsProj (c.val.restrictScalars k) (Module.toModuleEnd k J r) := by
  classical
  let rest := isotypicComponents R J \ {c.val}
  have hc : IsCompl c.val (sSup rest) := by
    refine ⟨sSupIndep_isotypicComponents R J c.prop, codisjoint_iff.mpr ?_⟩
    rw [← sSup_isotypicComponents R J]
    refine le_antisymm (sup_le (le_sSup c.prop) (sSup_le_sSup Set.sdiff_subset)) (sSup_le ?_)
    intro B hB
    by_cases h : B = c.val
    · exact h ▸ le_sup_left
    · exact (le_sSup (show B ∈ rest from ⟨hB, h⟩)).trans le_sup_right
  have hinv : (sSup rest).IsFullyInvariant :=
    (fullyInvariantSubmodule R J).sSupClosed fun _ h => .of_mem_isotypicComponents h.1
  let p := c.val.projection (sSup rest) hc
  have hcomm (T : Module.End R J) : Commute p T := by
    have hp : IsIdempotentElem p := isIdempotentElem_projection hc
    apply hp.commute_iff.mpr
    rw [range_projection hc, ker_projection hc]
    exact ⟨Submodule.IsFullyInvariant.of_mem_isotypicComponents c.prop T, hinv T⟩
  let P : Module.End (Module.End R J) J :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := fun T x => DFunLike.congr_fun (hcomm T).eq x }
  let : Module.Finite (Module.End R J) J := Module.Finite.of_restrictScalars_finite k _ _
  obtain ⟨r, hr⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective P
  have he (x : J) : r • x = p x := DFunLike.congr_fun hr x
  refine ⟨r, ⟨fun x => ?_, fun x hx => (he x).trans (projection_apply_of_mem_left hc hx)⟩⟩
  change r • x ∈ c.val
  rw [he]
  exact projection_apply_mem hc x

section SplitSummand

variable (s : M →ₗ[R] J) (p : J →ₗ[R] M) (hs : Function.LeftInverse p s)

include hs in
private theorem comap_isotypic_of_split {S : Type*} [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] :
    (isotypicComponent R J S).comap s = isotypicComponent R M S := by
  refine le_antisymm ?_ (s.le_comap_isotypicComponent S)
  intro x hx
  exact hs x ▸ p.le_comap_isotypicComponent S hx

include hs in
private theorem map_isotypic_of_split (c : isotypicComponents R J) :
    c.val.map p = c.val.comap s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.IsFullyInvariant.of_mem_isotypicComponents c.prop (s.comp p) hy
  · intro hx
    exact ⟨s x, hx, hs x⟩

/-- Restricting the isotypic decomposition to a split summand gives a direct sum
of its intersections with the ambient components. -/
private def splitIsotypicEquiv [IsSemisimpleModule R J] :
    M ≃ₗ[R] Π₀ c : isotypicComponents R J, c.val.comap s := by
  classical
  have hind := (sSupIndep_iff _).mp (sSupIndep_isotypicComponents R J)
  have hind' : iSupIndep (fun c : isotypicComponents R J => c.val.comap s) := by
    intro i
    have hdis : Disjoint (i.val.comap s) ((⨆ j, ⨆ (_ : j ≠ i), j.val).comap s) := by
      rw [disjoint_iff, ← Submodule.comap_inf, (hind i).eq_bot]
      exact LinearMap.ker_eq_bot.mpr hs.injective
    exact hdis.mono_right (iSup₂_le fun j hj =>
      Submodule.comap_mono ((le_iSup (fun _ : j ≠ i => j.val) hj).trans
        (le_iSup (fun j : isotypicComponents R J => ⨆ (_ : j ≠ i), j.val) j)))
  have htop : (⨆ c : isotypicComponents R J, c.val.comap s) = ⊤ := by
    simp_rw [← map_isotypic_of_split s p hs]
    rw [← Submodule.map_iSup, ← sSup_eq_iSup', sSup_isotypicComponents, Submodule.map_top,
      LinearMap.range_eq_top.mpr hs.surjective]
  exact (hind'.linearEquiv htop).symm

private theorem trace_eq_finrank_of_split_projection [FiniteDimensional k M]
    (hinj : Function.Injective s) {c : Submodule R J} {r : R}
    (hr : LinearMap.IsProj (c.restrictScalars k) (Module.toModuleEnd k J r)) :
    LinearMap.trace k M (Module.toModuleEnd k (S := R) M r) =
      (Module.finrank k ((c.comap s).restrictScalars k) : k) := by
  have hproj : LinearMap.IsProj ((c.comap s).restrictScalars k)
      (Module.toModuleEnd k (S := R) M r) := by
    constructor
    · intro x
      change s (r • x) ∈ c
      rw [map_smul]
      exact hr.map_mem _
    · intro x hx
      change r • x = x
      apply hinj
      rw [map_smul]
      exact hr.map_id _ hx
  exact hproj.trace

end SplitSummand

private theorem isotypic_equiv_of_finrank_eq {S : Type*} [AddCommGroup S]
    [Module R S] [Module k S] [towerS : IsScalarTower k R S] [FiniteDimensional k S]
    [simpleS : IsSimpleModule R S] [FiniteDimensional k M] [FiniteDimensional k N]
    [semisimpleM : IsSemisimpleModule R M] [semisimpleN : IsSemisimpleModule R N]
    (hM : IsIsotypicOfType R M S) (hN : IsIsotypicOfType R N S)
    (hd : Module.finrank k M = Module.finrank k N) : Nonempty (M ≃ₗ[R] N) := by
  let : Module.Finite R M := Module.Finite.of_restrictScalars_finite k R M
  let : Module.Finite R N := Module.Finite.of_restrictScalars_finite k R N
  obtain ⟨m, ⟨eM⟩⟩ := hM.linearEquiv_fun
  obtain ⟨n, ⟨eN⟩⟩ := hN.linearEquiv_fun
  have hm : Module.finrank k M = m * Module.finrank k S := by
    simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_id] using (eM.restrictScalars k).finrank_eq
  have hn : Module.finrank k N = n * Module.finrank k S := by
    simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_id] using (eN.restrictScalars k).finrank_eq
  let : Nontrivial S := IsSimpleModule.nontrivial R S
  have heq := Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := k) (M := S))
    (hm.symm.trans (hd.trans hn))
  subst n
  exact ⟨eM.trans eN.symm⟩

/-- Traces of algebra elements determine a finite dimensional semisimple module
in characteristic zero. -/
private theorem module_equiv_of_trace_eq [CharZero k] [FiniteDimensional k M] [FiniteDimensional k N]
    [IsSemisimpleModule R M] [IsSemisimpleModule R N]
    (htr : ∀ r : R, LinearMap.trace k M (Module.toModuleEnd k M r) =
      LinearMap.trace k N (Module.toModuleEnd k N r)) : Nonempty (M ≃ₗ[R] N) := by
  classical
  let inM := LinearMap.inl R M N
  let inN := LinearMap.inr R M N
  let outM := LinearMap.fst R M N
  let outN := LinearMap.snd R M N
  have hsM : Function.LeftInverse outM inM := fun _ => rfl
  have hsN : Function.LeftInverse outN inN := fun _ => rfl
  have : IsSemisimpleModule R (M × N) := by
    have h := IsSemisimpleModule.sup (IsSemisimpleModule.range inM) (IsSemisimpleModule.range inN)
    change IsSemisimpleModule R ↥((LinearMap.inl R M N).range ⊔ (LinearMap.inr R M N).range) at h
    rw [LinearMap.sup_range_inl_inr] at h
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  let eM := splitIsotypicEquiv inM outM hsM
  let eN := splitIsotypicEquiv inN outN hsN
  have hI (c : isotypicComponents R (M × N)) : Nonempty (c.val.comap inM ≃ₗ[R] c.val.comap inN) := by
    obtain ⟨r, hr⟩ := exists_isotypic_projection (k := k) c
    have hM := trace_eq_finrank_of_split_projection (k := k) inM hsM.injective hr
    have hN := trace_eq_finrank_of_split_projection (k := k) inN hsN.injective hr
    have hd : Module.finrank k ((c.val.comap inM).restrictScalars k) =
        Module.finrank k ((c.val.comap inN).restrictScalars k) :=
      Nat.cast_injective (R := k) (hM.symm.trans ((htr r).trans hN))
    obtain ⟨B, S, hS, rfl⟩ := c
    rw [comap_isotypic_of_split inM outM hsM, comap_isotypic_of_split inN outN hsN] at hd ⊢
    let pM := isotypicComponent R M S
    let pN := isotypicComponent R N S
    exact isotypic_equiv_of_finrank_eq (k := k) (S := S.restrictScalars k)
      (M := pM.restrictScalars k) (N := pN.restrictScalars k) (simpleS := hS)
      (towerS := Submodule.restrictScalars.isScalarTower k R (M × N) S)
      (towerM := Submodule.restrictScalars.isScalarTower k R M pM)
      (towerN := Submodule.restrictScalars.isScalarTower k R N pN)
      (semisimpleM := inferInstanceAs (IsSemisimpleModule R pM))
      (semisimpleN := inferInstanceAs (IsSemisimpleModule R pN))
      (IsIsotypicOfType.isotypicComponent R M S) (IsIsotypicOfType.isotypicComponent R N S) hd
  exact ⟨eM.trans ((DFinsupp.mapRange.linearEquiv fun c => (hI c).some).trans eN.symm)⟩

end Algebra

section Representation

variable {k G V W : Type*} [Field k] [CharZero k] [Group G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

omit [CharZero k] [FiniteDimensional k V] in
private theorem trace_asModule (ρ : Representation k G V) (r : k[G]) :
    LinearMap.trace k ρ.asModule (Module.toModuleEnd k ρ.asModule r) =
      LinearMap.trace k V (ρ.asAlgebraHom r) := by
  rw [← LinearMap.trace_conj' _ ρ.asModuleEquiv]
  congr 1

/-- Brauer–Nesbitt in characteristic zero for finite dimensional semisimple
representations of an arbitrary group. -/
theorem equiv_of_character_eq {ρ : Representation k G V} {σ : Representation k G W}
    (hρ : Representation.IsSemisimpleRepresentation ρ)
    (hσ : Representation.IsSemisimpleRepresentation σ) (h : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) := by
  let : IsSemisimpleModule k[G] ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hρ
  let : IsSemisimpleModule k[G] σ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp hσ
  have htr (r : k[G]) : LinearMap.trace k V (ρ.asAlgebraHom r) =
      LinearMap.trace k W (σ.asAlgebraHom r) := by
    induction r using MonoidAlgebra.induction_on with
    | of g => simpa only [Representation.asAlgebraHom_of, Representation.character] using congrFun h g
    | add x y hx hy => simp only [map_add, hx, hy]
    | smul c x hx => simp only [map_smul, hx]
  obtain ⟨e⟩ := module_equiv_of_trace_eq (k := k) (R := k[G]) (M := ρ.asModule) (N := σ.asModule)
    (fun r => (trace_asModule ρ r).trans ((htr r).trans (trace_asModule σ r).symm))
  let e' := ρ.asModuleEquiv.symm.trans ((e.restrictScalars k).trans σ.asModuleEquiv)
  refine ⟨Representation.Equiv.mk e' fun g => LinearMap.ext fun x => ?_⟩
  change σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g x))) =
    σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm x)))
  rw [ρ.asModuleEquiv_symm_map_rho, e.map_smul, σ.asModuleEquiv_map_smul, σ.asAlgebraHom_of]

end Representation

end Langlands.GaloisRepresentation.QuadraticFrobeniusPatching

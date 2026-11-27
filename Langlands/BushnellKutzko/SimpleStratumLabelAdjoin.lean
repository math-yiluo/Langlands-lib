import Langlands.BushnellKutzko.SimpleStratumLabelTower
import Langlands.BushnellKutzko.PureStratumApproximationChainImprovement

/-! # The field `F[γ, α]` of a refinement and its invariants

Let `E = F[γ]` act on `V` and let `α ∈ End_E(V)` generate a field `E[α]`. The `F`-subalgebra
`F[γ, α]` of `End_F(V)` is isomorphic to `E[α]` over `E`, so its ramification index and
residue degree over `F` are the products of those of `E/F` and `E[α]/E`. -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SimpleStratumLabel

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

/-- Restriction of scalars `End_E(V) → End_F(V)` as a ring homomorphism. -/
def restrictScalarsRingHom : Module.End E V →+* Module.End F V where
  toFun x := x.restrictScalars F
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem restrictScalarsRingHom_injective :
    Function.Injective (restrictScalarsRingHom (F := F) (E := E) (V := V)) := by
  intro x y h
  ext v
  exact LinearMap.congr_fun h v

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The image of `E[α]` under restriction of scalars is `F[γ, α]`. -/
theorem mem_adjoin_pair_iff {γE : E} (hgen : Algebra.adjoin F ({γE} : Set E) = ⊤)
    (α : Module.End E V) (x : Module.End F V) :
    x ∈ Algebra.adjoin F ({subfieldEmbedding F E V γE, α.restrictScalars F} :
        Set (Module.End F V)) ↔
      ∃ k ∈ elementAlgebra α, restrictScalarsRingHom k = x := by
  constructor
  · intro hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact ⟨algebraMap E (Module.End E V) γE, Subalgebra.algebraMap_mem _ _,
          PureApproximation.restrictScalars_algebraMap γE⟩
      · exact ⟨α, Algebra.self_mem_adjoin_singleton E α, rfl⟩
    | algebraMap c =>
      refine ⟨algebraMap E (Module.End E V) (algebraMap F E c), Subalgebra.algebraMap_mem _ _, ?_⟩
      change (algebraMap E (Module.End E V) (algebraMap F E c)).restrictScalars F = _
      rw [PureApproximation.restrictScalars_algebraMap, AlgHom.commutes]
    | add y z _ _ hy hz =>
      obtain ⟨k, hk, rfl⟩ := hy
      obtain ⟨l, hl, rfl⟩ := hz
      exact ⟨k + l, add_mem hk hl, map_add _ _ _⟩
    | mul y z _ _ hy hz =>
      obtain ⟨k, hk, rfl⟩ := hy
      obtain ⟨l, hl, rfl⟩ := hz
      exact ⟨k * l, mul_mem hk hl, map_mul _ _ _⟩
  · rintro ⟨k, hk, rfl⟩
    induction hk using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.mp hy]
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
    | algebraMap e =>
      change (algebraMap E (Module.End E V) e).restrictScalars F ∈ _
      rw [PureApproximation.restrictScalars_algebraMap]
      have h1 := PureApproximation.subfieldEmbedding_mem_elementAlgebra (V := V) rfl hgen e
      exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) h1
    | add y z _ _ hy hz =>
      rw [map_add]
      exact add_mem hy hz
    | mul y z _ _ hy hz =>
      rw [map_mul]
      exact mul_mem hy hz

set_option synthInstance.maxHeartbeats 400000 in
/-- The invariants of `F[γ, α]` over `F` are the products of those of `E = F[γ]` over `F` and of
`E[α]` over `E`, where `E` carries its spectral local-field structure. -/
theorem subalgebraInvariants_adjoin_pair [FiniteDimensional F V] [FiniteDimensional F E]
    {γE : E} (hgen : Algebra.adjoin F ({γE} : Set E) = ⊤)
    (α : Module.End E V) (hα : IsField (elementAlgebra α)) :
    letI := LocalField.FiniteExtension.valuativeRel F E
    subalgebraRamificationIndex F (Algebra.adjoin F
        ({subfieldEmbedding F E V γE, α.restrictScalars F} : Set (Module.End F V))) =
      subfieldRamificationIndex F E * elementRamificationIndex E α ∧
    subalgebraResidueDegree F (Algebra.adjoin F
        ({subfieldEmbedding F E V γE, α.restrictScalars F} : Set (Module.End F V))) =
      subfieldResidueDegree F E * elementResidueDegree E α := by
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  have : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  set E₁ := Algebra.adjoin F
    ({subfieldEmbedding F E V γE, α.restrictScalars F} : Set (Module.End F V)) with hE₁def
  set K := elementAlgebra α with hKdef
  let : Field K := hα.toField
  have hmemE : ∀ e : E, subfieldEmbedding F E V e ∈ E₁ := fun e =>
    (mem_adjoin_pair_iff hgen α _).2 ⟨algebraMap E _ e, Subalgebra.algebraMap_mem _ _,
      PureApproximation.restrictScalars_algebraMap e⟩
  let f : K →+* E₁ :=
    { toFun := fun k => ⟨restrictScalarsRingHom (k : Module.End E V),
        (mem_adjoin_pair_iff hgen α _).2 ⟨k, k.2, rfl⟩⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hbij : Function.Bijective f := by
    refine ⟨fun x y h => ?_, fun y => ?_⟩
    · apply Subtype.ext
      apply restrictScalarsRingHom_injective (F := F)
      exact congrArg (fun z : E₁ => (z : Module.End F V)) h
    · obtain ⟨k, hk, hky⟩ := (mem_adjoin_pair_iff hgen α _).1 y.2
      exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
  let φ₀ := RingEquiv.ofBijective f hbij
  have hE₁ : IsField E₁ := φ₀.symm.toMulEquiv.isField hα
  let : Field E₁ := hE₁.toField
  let ι : E →+* E₁ :=
    { toFun := fun e => ⟨subfieldEmbedding F E V e, hmemE e⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) }
  let : Algebra E E₁ := ι.toAlgebra' fun _ _ => hE₁.mul_comm _ _
  have : IsScalarTower F E E₁ := IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext ((subfieldEmbedding F E V).commutes c).symm
  let φ : K ≃ₐ[E] E₁ := AlgEquiv.ofRingEquiv (f := φ₀) fun e =>
    Subtype.ext (PureApproximation.restrictScalars_algebraMap e)
  have : FiniteDimensional E K := inferInstance
  have : FiniteDimensional E E₁ := LinearEquiv.finiteDimensional φ.toLinearEquiv
  have htowe := subfieldRamificationIndex_tower F E E₁
  have htowf := subfieldResidueDegree_tower F E E₁
  have hiso := PureApproximation.subfieldInvariants_of_algEquiv (F := E) φ
  unfold subalgebraRamificationIndex subalgebraResidueDegree elementRamificationIndex
    elementResidueDegree
  rw [dite_eq_left hE₁, dite_eq_left hE₁, dite_eq_left hα, dite_eq_left hα]
  exact ⟨htowe.trans (by rw [hiso.1]), htowf.trans (by rw [hiso.2])⟩

end Langlands.BushnellKutzko.SimpleStratumLabel

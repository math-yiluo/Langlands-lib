import Langlands.Representation.Jacquet.CanonicalLiftDefinitions
import Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof
import Langlands.Representation.Compact.SurjectivityProof
import Langlands.Representation.Category.SmoothCoproducts
import Langlands.LinearAlgebra.StableEndomorphismProofs

/-! # Fixed-exponent compact compression through sums and exact rows -/

noncomputable section

open scoped DirectSum

namespace Langlands

universe uG uA uB uC uI uV

section DirectSumFixedVectors

variable {G : Type uG} [Group G]
variable {ι : Type uI}
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The componentwise inclusion of fixed vectors into a direct sum. -/
def fixedVectorsDirectSumMap (ρ : ∀ i, Representation ℂ G (V i)) (H : Subgroup G) :
    (⨁ i, fixedVectors (ρ i) H) →ₗ[ℂ] fixedVectors (Representation.directSum ρ) H :=
  (DirectSum.lmap (fun i => (fixedVectors (ρ i) H).subtype)).codRestrict
    (fixedVectors (Representation.directSum ρ) H) (by
      intro x k
      ext i
      exact (x i).property k)

@[simp]
theorem fixedVectorsDirectSumMap_apply (ρ : ∀ i, Representation ℂ G (V i))
    (H : Subgroup G) (x : ⨁ i, fixedVectors (ρ i) H) (i : ι) :
    ((fixedVectorsDirectSumMap ρ H x).val i) = (x i).val := rfl

theorem fixedVectorsDirectSumMap_bijective (ρ : ∀ i, Representation ℂ G (V i))
    (H : Subgroup G) : Function.Bijective (fixedVectorsDirectSumMap ρ H) := by
  constructor
  · intro x y h
    apply (DirectSum.lmap_injective
      (fun i => (fixedVectors (ρ i) H).subtype)).mpr
        (fun _ => Subtype.val_injective)
    exact congrArg Subtype.val h
  · intro x
    have hx : x.val ∈ LinearMap.range
        (DirectSum.lmap (fun i => (fixedVectors (ρ i) H).subtype)) := by
      rw [DirectSum.range_lmap]
      intro i _
      refine ⟨⟨x.val i, ?_⟩, rfl⟩
      intro k
      exact congrArg (fun z => z i) (x.property k)
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩

/-- Fixed vectors commute with the actual algebraic direct sum. -/
def fixedVectorsDirectSumEquiv (ρ : ∀ i, Representation ℂ G (V i)) (H : Subgroup G) :
    (⨁ i, fixedVectors (ρ i) H) ≃ₗ[ℂ] fixedVectors (Representation.directSum ρ) H :=
  LinearEquiv.ofBijective (fixedVectorsDirectSumMap ρ H)
    (fixedVectorsDirectSumMap_bijective ρ H)

@[simp]
theorem fixedVectorsDirectSumEquiv_apply (ρ : ∀ i, Representation ℂ G (V i))
    (H : Subgroup G) (x : ⨁ i, fixedVectors (ρ i) H) (i : ι) :
    ((fixedVectorsDirectSumEquiv ρ H x).val i) = (x i).val := rfl

end DirectSumFixedVectors

namespace LinearAlgebra.StableEndomorphism

section Equivalence

variable {A : Type uA} {B : Type uB}
variable [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- Stability is preserved by an intertwining linear equivalence. -/
theorem stable_of_equiv (e : A ≃ₗ[ℂ] B) (t : Module.End ℂ A) (s : Module.End ℂ B)
    (he : e.toLinearMap.comp t = s.comp e.toLinearMap) (ht : Stable t) : Stable s := by
  apply stable_of_rightExact (0 : A →ₗ[ℂ] A) e.toLinearMap 0 t s
  · rw [LinearMap.range_zero, LinearMap.ker_eq_bot.mpr e.injective]
  · exact e.surjective
  · simp
  · exact he.symm
  · constructor <;> simp
  · exact ht

/-- Stability is invariant under an intertwining linear equivalence. -/
theorem stable_iff_of_equiv (e : A ≃ₗ[ℂ] B) (t : Module.End ℂ A) (s : Module.End ℂ B)
    (he : e.toLinearMap.comp t = s.comp e.toLinearMap) : Stable t ↔ Stable s := by
  refine ⟨stable_of_equiv e t s he, ?_⟩
  apply stable_of_equiv e.symm s t
  ext y
  apply e.injective
  have h := LinearMap.congr_fun he (e.symm y)
  simpa using h.symm

end Equivalence

section DirectSum

variable {ι : Type uI} {V : ι → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Componentwise stable endomorphisms give a stable direct-sum endomorphism. -/
theorem stable_directSum (t : ∀ i, Module.End ℂ (V i)) (ht : ∀ i, Stable (t i)) :
    Stable (DirectSum.lmap t) := by
  have hsq : DirectSum.lmap t ^ 2 = DirectSum.lmap (fun i => t i ^ 2) := by
    ext x i
    rfl
  constructor
  · have hk : (fun i => LinearMap.ker (t i)) =
        (fun i => LinearMap.ker (t i ^ 2)) := funext fun i => (ht i).1
    rw [hsq, DirectSum.ker_lmap, DirectSum.ker_lmap, hk]
  · have hr : (fun i => LinearMap.range (t i)) =
        (fun i => LinearMap.range (t i ^ 2)) := funext fun i => (ht i).2
    rw [hsq, DirectSum.range_lmap, DirectSum.range_lmap, hr]

/-- Stability of a direct-sum endomorphism is equivalent to componentwise stability. -/
theorem stable_directSum_iff (t : ∀ i, Module.End ℂ (V i)) :
    Stable (DirectSum.lmap t) ↔ ∀ i, Stable (t i) := by
  classical
  refine ⟨?_, stable_directSum t⟩
  intro ht i
  rw [stable_iff_le]
  constructor
  · intro v hv
    rw [LinearMap.mem_ker, pow_two, Module.End.mul_apply] at hv
    rw [LinearMap.mem_ker]
    have hx : DirectSum.lmap t
        (DirectSum.lmap t (DirectSum.lof ℂ ι V i v)) = 0 := by
      rw [DirectSum.lmap_lof, DirectSum.lmap_lof, hv, map_zero]
    have h := congrArg (fun z => z i) (ht.apply_eq_zero hx)
    simpa using h
  · rintro _ ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := ht.exists_apply_sq (DirectSum.lof ℂ ι V i v)
    refine ⟨w i, ?_⟩
    have h := congrArg (fun z => z i) hw
    simpa [pow_two, Module.End.mul_apply] using h

end DirectSum

end LinearAlgebra.StableEndomorphism

namespace Jacquet

open Langlands.LinearAlgebra.StableEndomorphism

section ExactRows

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
variable [AddCommGroup C] [Module ℂ C]
variable {ρ : Representation ℂ G A} {σ : Representation ℂ G B}
variable {τ : Representation ℂ G C}

/-- The published pointwise power-naturality law as an equality of linear maps. -/
theorem compressedAction_pow_natural_map (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (g : G) (f : ρ.IntertwiningMap σ) (b : ℕ) :
    (fixedVectorsMap f K.toSubgroup).comp (compressedAction ρ hρ K hK g ^ b) =
      (compressedAction σ hσ K hK g ^ b).comp (fixedVectorsMap f K.toSubgroup) := by
  apply LinearMap.ext
  intro v
  exact compressedAction_pow_natural ρ σ hρ hσ K hK g f b v

/-- Compact averaging preserves an algebraically exact row of smooth representations. -/
theorem fixedVectorsMap_range_eq_ker (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ)
    (hexact : LinearMap.range f.toLinearMap = LinearMap.ker q.toLinearMap) :
    LinearMap.range (fixedVectorsMap f K.toSubgroup) =
      LinearMap.ker (fixedVectorsMap q K.toSubgroup) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    apply Subtype.ext
    change q.toLinearMap (f.toLinearMap v.val) = 0
    rw [← LinearMap.mem_ker, ← hexact]
    exact LinearMap.mem_range_self f.toLinearMap v.val
  · intro w hw
    have hw' : w.val ∈ LinearMap.range f.toLinearMap := by
      rw [hexact, LinearMap.mem_ker]
      exact congrArg Subtype.val hw
    obtain ⟨v, hv⟩ := hw'
    change f v = w.val at hv
    refine ⟨⟨Compact.averageMap ρ hρ K hK v,
      Compact.averageMap_mem_fixedVectors ρ hρ K hK v⟩, Subtype.ext ?_⟩
    change f (Compact.averageMap ρ hρ K hK v) = w.val
    have hcomm := LinearMap.congr_fun (Compact.averageMap_commute ρ σ hρ hσ K hK f) v
    change f (Compact.averageMap ρ hρ K hK v) =
      Compact.averageMap σ hσ K hK (f v) at hcomm
    rw [hcomm, hv]
    exact Compact.averageMap_id σ hσ K hK w.val w.property

/-- A common stable compression power descends along a right exact presentation. -/
theorem compressedAction_stablePower_of_rightExact
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (hτ : IsSmooth τ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (f : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ)
    (hexact : LinearMap.range f.toLinearMap = LinearMap.ker q.toLinearMap)
    (hsurj : Function.Surjective q) (b : ℕ)
    (hA : Stable (compressedAction ρ hρ K hK g ^ b))
    (hB : Stable (compressedAction σ hσ K hK g ^ b)) :
    Stable (compressedAction τ hτ K hK g ^ b) := by
  apply stable_of_rightExact
    (fixedVectorsMap f K.toSubgroup) (fixedVectorsMap q K.toSubgroup)
    (compressedAction ρ hρ K hK g ^ b) (compressedAction σ hσ K hK g ^ b)
    (compressedAction τ hτ K hK g ^ b)
    (fixedVectorsMap_range_eq_ker hρ hσ K hK f q hexact)
  · exact Compact.fixedVectorSurjectivity G B C σ τ hσ hτ K hK q hsurj
  · exact (compressedAction_pow_natural_map hρ hσ K hK g f b).symm
  · exact (compressedAction_pow_natural_map hσ hτ K hK g q b).symm
  · exact hA
  · exact hB

/-- A common stable compression power passes to the kernel of an exact row. -/
theorem compressedAction_stablePower_of_leftExact
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (hτ : IsSmooth τ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (f : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ)
    (hinj : Function.Injective f)
    (hexact : LinearMap.range f.toLinearMap = LinearMap.ker q.toLinearMap)
    (b : ℕ) (hB : Stable (compressedAction σ hσ K hK g ^ b))
    (hC : Stable (compressedAction τ hτ K hK g ^ b)) :
    Stable (compressedAction ρ hρ K hK g ^ b) := by
  exact stable_of_leftExact
    (fixedVectorsMap f K.toSubgroup) (fixedVectorsMap q K.toSubgroup)
    (compressedAction ρ hρ K hK g ^ b) (compressedAction σ hσ K hK g ^ b)
    (compressedAction τ hτ K hK g ^ b)
    (fixedVectorsMap_injective f hinj K.toSubgroup)
    (fixedVectorsMap_range_eq_ker hρ hσ K hK f q hexact)
    (compressedAction_pow_natural_map hρ hσ K hK g f b).symm
    (compressedAction_pow_natural_map hσ hτ K hK g q b).symm hB hC

end ExactRows

section DirectSums

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {ι : Type uI} {V : ι → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Powers of compression correspond to componentwise powers under the actual
fixed-vector direct-sum equivalence. -/
theorem compressedAction_pow_directSum
    (ρ : ∀ i, Representation ℂ G (V i)) (hρ : ∀ i, IsSmooth (ρ i))
    (hsum : IsSmooth (Representation.directSum ρ))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) (b : ℕ) :
    (fixedVectorsDirectSumEquiv ρ K.toSubgroup).toLinearMap.comp
        (DirectSum.lmap (fun i => compressedAction (ρ i) (hρ i) K hK g ^ b)) =
      (compressedAction (Representation.directSum ρ) hsum K hK g ^ b).comp
        (fixedVectorsDirectSumEquiv ρ K.toSubgroup).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  ext i
  let p : (Representation.directSum ρ).IntertwiningMap (ρ i) :=
    { toLinearMap := DirectSum.component ℂ ι V i
      isIntertwining' g := by ext x; rfl }
  have h := congrArg Subtype.val (LinearMap.congr_fun
    (compressedAction_pow_natural_map hsum (hρ i) K hK g p b)
      (fixedVectorsDirectSumEquiv ρ K.toSubgroup x))
  change ((compressedAction (Representation.directSum ρ) hsum K hK g ^ b)
      (fixedVectorsDirectSumEquiv ρ K.toSubgroup x)).val i =
    ((compressedAction (ρ i) (hρ i) K hK g ^ b) (x i)).val at h
  exact h.symm

/-- A fixed exponent is stable on an actual smooth direct sum exactly when it
is stable on each summand. No finiteness condition is put on the index type. -/
theorem compressedAction_stablePower_directSum_iff
    (ρ : ∀ i, Representation ℂ G (V i)) (hρ : ∀ i, IsSmooth (ρ i))
    (hsum : IsSmooth (Representation.directSum ρ))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) (b : ℕ) :
    Stable (compressedAction (Representation.directSum ρ) hsum K hK g ^ b) ↔
      ∀ i, Stable (compressedAction (ρ i) (hρ i) K hK g ^ b) := by
  rw [← stable_iff_of_equiv (fixedVectorsDirectSumEquiv ρ K.toSubgroup)
    (DirectSum.lmap (fun i => compressedAction (ρ i) (hρ i) K hK g ^ b))
    (compressedAction (Representation.directSum ρ) hsum K hK g ^ b)
    (compressedAction_pow_directSum ρ hρ hsum K hK g b)]
  exact stable_directSum_iff _

end DirectSums

end Jacquet

end Langlands

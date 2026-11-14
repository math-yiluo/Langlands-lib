import Langlands.Automorphic.PlaceComponentDetection
import Langlands.Representation.CompactMaschke

/-!
# Post-composition actions on spaces of linear maps

Let `κ` be a representation of a group `K` and `π` a Lie action on a complex vector space `V`.
On the space `(Fin m → ℂ) →ₗ[ℂ] V` of linear maps, `K` and the Lie algebra act by
post-composition (`postRep`, `postLie`), and evaluation at a vector is equivariant. This
module shows that post-composition keeps local finiteness and weak continuity, and that a
matrix representation detecting the nonzero stable subspaces of `V` also detects the nonzero
stable subspaces of the space of linear maps.
-/

noncomputable section

open scoped Matrix

set_option autoImplicit false

namespace Langlands.Automorphic.PlaceComponent

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Group K] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (m : ℕ)

/-- Post-composition with endomorphisms of `V`. -/
def postComp : Module.End ℂ V →ₐ[ℂ] Module.End ℂ ((Fin m → ℂ) →ₗ[ℂ] V) where
  toFun A := LinearMap.llcomp ℂ (Fin m → ℂ) V V A
  map_one' := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  map_zero' := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  map_add' _ _ := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  commutes' _ := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/-- `K` acts on linear maps by post-composition. -/
def postRep (κ : Representation ℂ K V) : Representation ℂ K ((Fin m → ℂ) →ₗ[ℂ] V) :=
  (postComp m).toMonoidHom.comp κ

/-- The Lie algebra acts on linear maps by post-composition. -/
def postLie (π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ V) :
    𝔤 →ₗ⁅ℂ⁆ Module.End ℂ ((Fin m → ℂ) →ₗ[ℂ] V) :=
  (postComp m).toLieHom.comp π

theorem postRep_apply (κ : Representation ℂ K V) (k : K) (φ : (Fin m → ℂ) →ₗ[ℂ] V)
    (x : Fin m → ℂ) : postRep m κ k φ x = κ k (φ x) := rfl

theorem postLie_apply (π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ V) (X : 𝔤) (φ : (Fin m → ℂ) →ₗ[ℂ] V)
    (x : Fin m → ℂ) : postLie m π X φ x = π X (φ x) := rfl

/-- Evaluation at a vector. -/
def evalAt (x : Fin m → ℂ) : ((Fin m → ℂ) →ₗ[ℂ] V) →ₗ[ℂ] V := LinearMap.applyₗ x

theorem evalAt_apply (x : Fin m → ℂ) (φ : (Fin m → ℂ) →ₗ[ℂ] V) : evalAt m x φ = φ x := rfl

/-- A linear map vanishing on the standard basis vanishes. -/
theorem eq_zero_of_single (φ : (Fin m → ℂ) →ₗ[ℂ] V)
    (h : ∀ j : Fin m, φ (Pi.single j 1) = 0) : φ = 0 := by
  classical
  exact LinearMap.pi_ext' fun j => LinearMap.ext_ring (h j)

/-- A linear map from `Fin m → ℂ` in terms of its values on the standard basis. -/
theorem apply_eq_sum (φ : (Fin m → ℂ) →ₗ[ℂ] V) (x : Fin m → ℂ) :
    φ x = ∑ j : Fin m, x j • φ (Pi.single j 1) := by
  classical
  rw [LinearMap.pi_apply_eq_sum_univ]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  funext i
  rw [Pi.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- A linear map from `Fin m → ℂ` as a sum of rank-one maps. -/
theorem eq_sum_smulRight (φ : (Fin m → ℂ) →ₗ[ℂ] V) :
    φ = ∑ j : Fin m,
      (LinearMap.proj j : (Fin m → ℂ) →ₗ[ℂ] ℂ).smulRight (φ (Pi.single j 1)) := by
  refine LinearMap.ext fun x => ?_
  rw [apply_eq_sum m φ x, LinearMap.sum_apply]
  rfl

variable [TopologicalSpace K]

/-- Post-composition keeps weak continuity. -/
theorem isWeaklyContinuous_postRep {κ : Representation ℂ K V} (hweak : IsWeaklyContinuous κ) :
    IsWeaklyContinuous (postRep m κ) := by
  classical
  intro μ φ
  let μj : Fin m → V →ₗ[ℂ] ℂ := fun j =>
    { toFun := fun v => μ ((LinearMap.proj j : (Fin m → ℂ) →ₗ[ℂ] ℂ).smulRight v)
      map_add' := fun v w => by
        rw [← map_add]
        congr 1
        exact LinearMap.ext fun x => smul_add (x j) v w
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        exact LinearMap.ext fun x => smul_comm (x j) c v }
  have hdec : ∀ ψ : (Fin m → ℂ) →ₗ[ℂ] V,
      μ ψ = ∑ j : Fin m, μj j (ψ (Pi.single j 1)) := by
    intro ψ
    conv_lhs => rw [eq_sum_smulRight m ψ]
    rw [map_sum]
    rfl
  simp_rw [hdec]
  exact continuous_finsetSum _ fun j _ => hweak (μj j) (φ (Pi.single j 1))

omit [TopologicalSpace K] in
/-- Post-composition keeps local finiteness. -/
theorem isLocallyFinite_postRep {κ : Representation ℂ K V} (hfin : IsLocallyFinite κ) :
    IsLocallyFinite (postRep m κ) := by
  classical
  intro φ
  choose E hEf hE hEs using fun j : Fin m => hfin (φ (Pi.single j 1))
  let E' : Submodule ℂ V := ⨆ j, E j
  have : FiniteDimensional ℂ E' := Submodule.finiteDimensional_iSup _
  have hE's : ∀ (k : K), ∀ y ∈ E', κ k y ∈ E' := by
    intro k y hy
    refine Submodule.iSup_induction E (motive := fun y => κ k y ∈ E') hy
      (fun i y hy => Submodule.mem_iSup_of_mem i (hEs i k y hy)) ?_ ?_
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  let C : ((Fin m → ℂ) →ₗ[ℂ] E') →ₗ[ℂ] ((Fin m → ℂ) →ₗ[ℂ] V) :=
    LinearMap.llcomp ℂ (Fin m → ℂ) E' V E'.subtype
  let F : Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] V) := LinearMap.range C
  have hφE : ∀ x, φ x ∈ E' := fun x => by
    rw [apply_eq_sum m φ x]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem j (hE j))
  refine ⟨F, LinearMap.finiteDimensional_range _, ⟨φ.codRestrict E' hφE, rfl⟩, ?_⟩
  rintro k _ ⟨ψ, rfl⟩
  refine ⟨(postRep m κ k (E'.subtype.comp ψ : (Fin m → ℂ) →ₗ[ℂ] V)).codRestrict E'
    fun x => hE's k _ (ψ x).2, ?_⟩
  rfl

variable [IsTopologicalGroup K] [CompactSpace K]

/-- **Detection passes to post-composition.** If a matrix representation `τ` has a nonzero
intertwiner into every nonzero stable subspace of `V`, it has one into every nonzero stable
subspace of `(Fin m → ℂ) →ₗ V`. -/
theorem intertwiners_ne_bot_postRep {κ : Representation ℂ K V} {π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ V}
    (hfin : IsLocallyFinite κ) (hweak : IsWeaklyContinuous κ) {d : ℕ}
    {τ : K →* Matrix (Fin d) (Fin d) ℂ}
    (hdet : ∀ W : Submodule ℂ V, IsStable κ π W → W ≠ ⊥ → intertwiners κ W d τ ≠ ⊥)
    {N : Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] V)} (hNs : IsStable (postRep m κ) (postLie m π) N)
    (hN : N ≠ ⊥) : intertwiners (postRep m κ) N d τ ≠ ⊥ := by
  classical
  obtain ⟨φ, hφN, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  have hex : ∃ j, φ (Pi.single j 1) ≠ 0 := by
    by_contra h
    exact hφ0 (eq_zero_of_single m φ fun j => not_not.mp fun hj => h ⟨j, hj⟩)
  obtain ⟨j, hj⟩ := hex
  let W : Submodule ℂ V := N.map (evalAt m (Pi.single j 1))
  have hWs : IsStable κ π W := by
    refine ⟨?_, ?_⟩
    · rintro k _ ⟨ψ, hψ, rfl⟩
      exact ⟨postRep m κ k ψ, hNs.1 k ψ hψ, rfl⟩
    · rintro X _ ⟨ψ, hψ, rfl⟩
      exact ⟨postLie m π X ψ, hNs.2 X ψ hψ, rfl⟩
  have hW0 : W ≠ ⊥ := by
    intro h
    have hmem : φ (Pi.single j 1) ∈ W := ⟨φ, hφN, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hj hmem
  obtain ⟨ψ, hψ, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hdet W hWs hW0)
  rw [mem_intertwiners] at hψ
  obtain ⟨ψ', hψ'eq, hψ'q⟩ := CompactMaschke.exists_lift_intertwiner
    (restrictRep (postRep m κ) N hNs.1) κ
    (isLocallyFinite_restrict (isLocallyFinite_postRep m hfin) hNs.1)
    (isWeaklyContinuous_restrict (isWeaklyContinuous_postRep m hweak) hNs.1)
    (evalAt m (Pi.single j 1) ∘ₗ N.subtype) (fun k x => rfl) τ ψ hψ.2 (fun x => by
      obtain ⟨y, hy, hxy⟩ := hψ.1 x
      exact ⟨⟨y, hy⟩, hxy⟩)
  intro hbot
  have hzero := eq_zero_of_free (postRep m κ) hNs.1 τ hbot ψ' hψ'eq
  apply hψ0
  rw [← hψ'q, hzero, LinearMap.comp_zero]

end Langlands.Automorphic.PlaceComponent

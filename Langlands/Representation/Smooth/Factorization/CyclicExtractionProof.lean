import Langlands.Representation.Smooth.Factorization.CyclicExtractionStatement
import Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof
import Langlands.Representation.Hecke.CommutativeCornerFixedLine
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.Representation.TensorProduct.MultiplicityCancellation

/-! # Prescribed-vector cyclic extraction in a product representation -/

noncomputable section

namespace Langlands.CyclicExtraction

open Representation TwoFactorExistence
open scoped TensorProduct

universe uG uG₁ uG₂ uV uW uX

section Refinement

variable {G₁ : Type uG₁} {G₂ : Type uG₂} [Group G₁] [Group G₂]
variable [TopologicalSpace G₁] [TopologicalSpace G₂]
variable [IsTopologicalGroup G₁]
variable [T2Space G₁] [LocallyCompactSpace G₁] [TotallyDisconnectedSpace G₁]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ (G₁ × G₂) V}

/-- Localizing the minimal-fixed-space construction to the orbit span of a
prescribed nonzero vector retains membership in that span. -/
theorem exists_cyclic_in_span [ρ.IsIrreducible] (ha : IsAdmissible ρ)
    (x : V) (hx : x ≠ 0) :
    ∃ (K₂ : OpenSubgroup G₂) (y : V), y ∈ spanOrbit ρ x ∧ y ≠ 0 ∧
      y ∈ fixedVectors (second ρ) K₂.toSubgroup ∧
      ∀ u ∈ spanOrbit ρ y, u ≠ 0 → y ∈ spanOrbit ρ u := by
  classical
  obtain ⟨W, hW⟩ := ha.1 x
  obtain ⟨K₁, hK₁W, hK₁, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G₁ ∅
    (W.comap (MonoidHom.inl G₁ G₂) continuous_inl')
  let K₂ := W.comap (MonoidHom.inr G₁ G₂) continuous_inr'
  let M : Submodule ℂ V :=
    fixedVectors (first ρ) K₁.toSubgroup ⊓ fixedVectors (second ρ) K₂.toSubgroup
  have hMle : M ≤ fixedVectors ρ (K₁.prod K₂).toSubgroup := by
    intro v hv
    obtain ⟨h₁, h₂⟩ := Submodule.mem_inf.mp hv
    refine TwoFactorExistence.mem_fixedVectors_iff.mpr fun g hg => ?_
    rw [OpenSubgroup.toSubgroup_prod, Subgroup.mem_prod] at hg
    rw [← first_second_apply ρ g, (TwoFactorExistence.mem_fixedVectors_iff.mp h₂) g.2 hg.2,
      (TwoFactorExistence.mem_fixedVectors_iff.mp h₁) g.1 hg.1]
  have : FiniteDimensional ℂ (fixedVectors ρ (K₁.prod K₂).toSubgroup) := ha.2 (K₁.prod K₂)
  have : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le hMle
  have hxM : x ∈ M := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact TwoFactorExistence.mem_fixedVectors_iff.mpr fun k hk =>
        (TwoFactorExistence.mem_fixedVectors_iff.mp hW) (MonoidHom.inl G₁ G₂ k) (hK₁W hk)
    · exact TwoFactorExistence.mem_fixedVectors_iff.mpr fun k hk =>
        (TwoFactorExistence.mem_fixedVectors_iff.mp hW) (MonoidHom.inr G₁ G₂ k) hk
  let S : V → Submodule ℂ V := fun z => (spanOrbit ρ z).toSubmodule ⊓ M
  have hSfin : ∀ z, FiniteDimensional ℂ (S z) := fun z =>
    Submodule.finiteDimensional_of_le inf_le_right
  have hex : ∃ d, ∃ z ∈ M, z ∈ spanOrbit ρ x ∧ z ≠ 0 ∧ Module.finrank ℂ (S z) = d :=
    ⟨_, x, hxM, mem_spanOrbit_self ρ x, hx, rfl⟩
  obtain ⟨y, hyM, hyx, hy0, hyd⟩ := Nat.find_spec hex
  have hmin : ∀ z ∈ M, z ∈ spanOrbit ρ x → z ≠ 0 →
      Module.finrank ℂ (S y) ≤ Module.finrank ℂ (S z) := by
    intro z hz hzx hz0
    rw [hyd]
    exact Nat.find_min' hex ⟨z, hz, hzx, hz0, rfl⟩
  obtain ⟨hy₁, hy₂⟩ := Submodule.mem_inf.mp hyM
  refine ⟨K₂, y, hyx, hy0, hy₂, fun u hu hu0 => ?_⟩
  have hN : spanOrbit ρ u ≠ ⊥ := by
    intro h
    have h1 := mem_spanOrbit_self ρ u
    rw [h] at h1
    exact hu0 (mem_bot_iff.mp h1)
  obtain ⟨n, hn, hn0, hn₁⟩ := exists_fixed_of_ne_bot ha.1 K₁ hK₁ hy0 hy₁ hN
  have hny : n ∈ spanOrbit ρ y := spanOrbit_le ρ hu hn
  have hnx : n ∈ spanOrbit ρ x := spanOrbit_le ρ hyx hny
  have hn₂ : n ∈ fixedVectors (second ρ) K₂.toSubgroup :=
    spanOrbit_le ρ (P := secondFixed ρ K₂.toSubgroup) hy₂ hny
  have hle : S n ≤ S y := inf_le_inf_right M fun v hv => spanOrbit_le ρ hny hv
  have := hSfin y
  have heq : S n = S y :=
    Submodule.eq_of_le_of_finrank_le hle
      (hmin n (Submodule.mem_inf.mpr ⟨hn₁, hn₂⟩) hnx hn0)
  have hyS : y ∈ S y := Submodule.mem_inf.mpr ⟨mem_spanOrbit_self ρ y, hyM⟩
  rw [← heq] at hyS
  exact spanOrbit_le ρ hn (Submodule.mem_inf.mp hyS).1

/-- The prescribed-vector refinement, with the standard cyclic-span carrier. -/
theorem refinement [ρ.IsIrreducible] (ha : IsAdmissible ρ) (x : V) (hx : x ≠ 0) :
    ∃ y : V, y ∈ Cyclic.orbitSpan (first ρ) x ∧ y ≠ 0 ∧
      IsAdmissible (Cyclic.orbitSpan (first ρ) y).toRepresentation ∧
      (Cyclic.orbitSpan (first ρ) y).toRepresentation.IsIrreducible := by
  obtain ⟨K₂, y, hyx, hy0, hy₂, hcyc⟩ := exists_cyclic_in_span ha x hx
  have ha' : IsAdmissible (spanOrbit ρ y).toRepresentation :=
    isAdmissible_of_le_secondFixed ha K₂ _
      (spanOrbit_le ρ (P := secondFixed ρ K₂.toSubgroup) hy₂)
  exact ⟨y, hyx, hy0, ha', isIrreducible_spanOrbit hy0 hcyc⟩

end Refinement

section CyclicImages

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {σ : Representation ℂ G V} {τ : Representation ℂ G W}

/-- A nonzero vector generates an irreducible representation. -/
theorem orbitSpan_eq_top [σ.IsIrreducible] {u : V} (hu : u ≠ 0) :
    Cyclic.orbitSpan σ u = ⊤ := by
  refine (IsSimpleOrder.eq_bot_or_eq_top (Cyclic.orbitSpan σ u)).resolve_left ?_
  intro h
  have hmem := Cyclic.mem_orbitSpan σ u
  rw [h] at hmem
  exact hu (mem_bot_iff.mp hmem)

/-- An injective image of an irreducible representation is the cyclic space
of the image of each of its nonzero vectors. -/
theorem cyclicImageEquiv [σ.IsIrreducible] (f : σ.IntertwiningMap τ)
    (hf : Function.Injective f) {u : V} (hu : u ≠ 0) :
    Nonempty (σ.Equiv (Cyclic.orbitSpan τ (f u)).toRepresentation) := by
  have htop : FiniteVectors.orbitSpan σ u = ⊤ :=
    congrArg Subrepresentation.toSubmodule (orbitSpan_eq_top hu)
  have hmem : ∀ v : V, f v ∈ Cyclic.orbitSpan τ (f u) := by
    intro v
    change f v ∈ FiniteVectors.orbitSpan τ (f u)
    rw [← FiniteVectors.map_orbitSpan f u]
    exact ⟨v, htop.symm ▸ Submodule.mem_top, rfl⟩
  let F : σ.IntertwiningMap (Cyclic.orbitSpan τ (f u)).toRepresentation :=
    { toLinearMap := f.toLinearMap.codRestrict _ hmem
      isIntertwining' g := LinearMap.ext fun v =>
        Subtype.ext (Representation.IntertwiningMap.isIntertwining σ τ f g v) }
  refine ⟨F.ofBijective ⟨fun a b hab => hf (congrArg Subtype.val hab), ?_⟩⟩
  intro w
  have hw : (w : W) ∈ FiniteVectors.orbitSpan τ (f u) := w.2
  rw [← FiniteVectors.map_orbitSpan f u] at hw
  obtain ⟨v, -, hv⟩ := Submodule.mem_map.mp hw
  exact ⟨v, Subtype.ext hv⟩

/-- Irreducibility transports along an actual intertwining equivalence. -/
theorem irreducible_of_equiv (e : σ.Equiv τ) (hi : σ.IsIrreducible) :
    τ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at hi ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule σ τ e.toIntertwiningMap)
    e.bijective).mp hi

end CyclicImages

section FixedTensor

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (σ : Representation ℂ G V) (H : Subgroup G)

/-- If the fixed space of the acting factor is a line, every fixed tensor
is a simple tensor with any prescribed nonzero vector on that line. -/
theorem exists_tmul_of_fixed_line
    (hline : Module.finrank ℂ (fixedVectors σ H) = 1)
    (u : fixedVectors σ H) (hu : u ≠ 0) {t : V ⊗[ℂ] W}
    (ht : t ∈ fixedVectors (σ.tprod (Representation.trivial ℂ G W)) H) :
    ∃ w : W, t = (u : V) ⊗ₜ[ℂ] w := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let a := TensorProduct.equivFinsuppOfBasisRight b t
  have hfixed : ∀ j, a j ∈ fixedVectors σ H := fun j =>
    (fixedVectorsMap (TensorMultiplicity.coefficient σ b j) H ⟨t, ht⟩).property
  have hc : ∀ j, ∃ c : ℂ, c • (u : V) = a j := by
    intro j
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' u hu).mp hline ⟨a j, hfixed j⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose c hc using hc
  refine ⟨∑ j ∈ a.support, c j • b j, ?_⟩
  calc
    t = a.sum (fun j v => v ⊗ₜ[ℂ] b j) := by
      exact ((TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply t).symm.trans
        (TensorProduct.equivFinsuppOfBasisRight_symm_apply b a)
    _ = (u : V) ⊗ₜ[ℂ] (∑ j ∈ a.support, c j • b j) := by
      simp only [Finsupp.sum, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', hc]

end FixedTensor

section TensorRestriction

variable {G₁ : Type uG₁} {G₂ : Type uG₂} [Group G₁] [Group G₂]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {X : Type uX} [AddCommGroup X] [Module ℂ X]
variable {ρ : Representation ℂ (G₁ × G₂) V}
variable {σ : Representation ℂ G₁ W} {τ : Representation ℂ G₂ X}

/-- Restricting an external tensor equivalence to the first factor leaves
a trivial action on the second tensor coordinate. -/
def firstTensorEquiv (e : ρ.Equiv
    (Representation.tprod (σ.comp (MonoidHom.fst G₁ G₂))
      (τ.comp (MonoidHom.snd G₁ G₂)))) :
    (first ρ).Equiv (σ.tprod (Representation.trivial ℂ G₁ X)) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' g := by
    change e.toLinearMap ∘ₗ ρ (g, 1) =
      TensorProduct.map (σ g) LinearMap.id ∘ₗ e.toLinearMap
    simpa [Representation.tprod_apply, Module.End.one_eq_id] using e.isIntertwining' (g, 1)

end TensorRestriction

section Spherical

variable {G₁ : Type uG₁} {G₂ : Type uG₂} [Group G₁] [Group G₂]
variable [TopologicalSpace G₁] [TopologicalSpace G₂]
variable [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
variable [T2Space G₁] [T2Space G₂]
variable [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
variable [TotallyDisconnectedSpace G₁] [TotallyDisconnectedSpace G₂]
variable [MeasurableSpace G₁] [BorelSpace G₁]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ (G₁ × G₂) V}

/-- A spherical prescribed vector is a simple tensor after factorization,
so its own first-factor cyclic representation is admissible irreducible. -/
theorem spherical [ρ.IsIrreducible] (ha : IsAdmissible ρ)
    (μ : MeasureTheory.Measure G₁) [MeasureTheory.Measure.IsHaarMeasure μ]
    [MeasureTheory.Measure.Regular μ]
    (H : OpenSubgroup G₁) (hH : IsCompact (H : Set G₁))
    (hcomm : SphericalHeckeCommutative μ H.toSubgroup)
    (x : V) (hx : x ≠ 0) (hxH : x ∈ fixedVectors (first ρ) H.toSubgroup) :
    IsAdmissible (Cyclic.orbitSpan (first ρ) x).toRepresentation ∧
      (Cyclic.orbitSpan (first ρ) x).toRepresentation.IsIrreducible ∧
      Module.finrank ℂ
        (fixedVectors (Cyclic.orbitSpan (first ρ) x).toRepresentation H.toSubgroup) = 1 := by
  classical
  obtain ⟨W, X, σ, τ, haσ, hiσ, -, -, ⟨e⟩⟩ :=
    admissibleProductFactorization G₁ G₂ V ρ ha inferInstance
  have := hiσ
  let e₁ := firstTensorEquiv e
  have ht0 : e₁ x ≠ 0 := fun h => hx (e₁.injective (h.trans e₁.toLinearEquiv.map_zero.symm))
  have htH : e₁ x ∈ fixedVectors (σ.tprod (Representation.trivial ℂ G₁ X)) H.toSubgroup :=
    (fixedVectorsMap e₁.toIntertwiningMap H.toSubgroup ⟨x, hxH⟩).property
  let b := Module.Free.chooseBasis ℂ X
  obtain ⟨j, hj⟩ := TensorMultiplicity.exists_coefficient_ne_zero σ ht0
  let u : fixedVectors σ H.toSubgroup :=
    fixedVectorsMap (TensorMultiplicity.coefficient σ b j) H.toSubgroup ⟨e₁ x, htH⟩
  have hu0 : u ≠ 0 := fun h => hj (congrArg Subtype.val h)
  have h0 : fixedVectors σ H.toSubgroup ≠ ⊥ := by
    intro h
    have hu : (u : W) ∈ (⊥ : Submodule ℂ W) := h.le u.property
    exact hu0 (Subtype.ext ((Submodule.mem_bot ℂ).mp hu))
  have hc : ∀ f g : Hecke.HeckeAlgebra.Corner μ H hH, f * g = g * f := by
    intro f g
    apply Hecke.HeckeAlgebra.Corner.toHeckeAlgebra_injective μ H hH
    rw [map_mul, map_mul]
    exact hcomm _ _ f.property g.property
  have hline := Hecke.finrank_fixedVectors_eq_one_of_corner_comm μ σ haσ.1 H hH
    hc hiσ (haσ.2 H) h0
  obtain ⟨w, hw⟩ := exists_tmul_of_fixed_line σ H.toSubgroup hline u hu0 htH
  let f : σ.IntertwiningMap (first ρ) :=
    e₁.symm.toIntertwiningMap.comp (TensorMultiplicity.slice σ w)
  have hfu : f (u : W) = x := by
    change e₁.symm ((u : W) ⊗ₜ[ℂ] w) = x
    rw [← hw]
    exact e₁.symm_apply_apply x
  have hf0 : f ≠ 0 := by
    intro h
    apply hx
    rw [← hfu, h]
    rfl
  have hf := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf0
  obtain ⟨q⟩ := cyclicImageEquiv f hf (show (u : W) ≠ 0 from fun h => hu0 (Subtype.ext h))
  rw [hfu] at q
  refine ⟨isAdmissible_of_equiv q haσ, irreducible_of_equiv q hiσ, ?_⟩
  rw [← (fixedVectorsEquiv q H.toSubgroup).finrank_eq]
  exact hline

end Spherical

end Langlands.CyclicExtraction

namespace Langlands

universe uG₁ uG₂ uV

/-- The prescribed-vector refinement and spherical cyclic extraction inputs
for restricted-product factorization, over independent universes. -/
theorem twoFactorCyclicExtraction :
    TwoFactorCyclicExtractionStatement.{uG₁, uG₂, uV} := by
  constructor
  · intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ V _ _ ρ ha hi x hx
    have := hi
    exact CyclicExtraction.refinement ha x hx
  · intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ _ H hH V _ _ ρ hc ha hi x hx hxH
    have := hi
    exact CyclicExtraction.spherical ha μ H hH hc x hx hxH

end Langlands

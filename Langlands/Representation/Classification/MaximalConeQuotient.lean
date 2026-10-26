import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof

/-!
# Irreducible quotients detected by a dual eigenfunctional

A finitely generated admissible representation with a nonzero functional that is
an eigenvector of a central subgroup has an irreducible admissible quotient on
which that subgroup acts by the same character. The maximal-cone assembly applies
this to the whole normalized opposite Jacquet module along a dual exponent.
-/

noncomputable section

namespace Langlands

universe uV uG uC

namespace MaximalConeQuotient

section Generic

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The vectors whose whole orbit is annihilated by a functional. -/
def orbitKernel (ρ : Representation ℂ G V) (φ : Module.Dual ℂ V) : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | ∀ g, φ (ρ g v) = 0}
      add_mem' := fun {v w} hv hw g => by
        have hv' : ∀ g, φ (ρ g v) = 0 := hv
        have hw' : ∀ g, φ (ρ g w) = 0 := hw
        change φ (ρ g (v + w)) = 0
        rw [map_add, map_add, hv' g, hw' g, add_zero]
      zero_mem' := fun g => by simp
      smul_mem' := fun c v hv g => by
        have hv' : ∀ g, φ (ρ g v) = 0 := hv
        change φ (ρ g (c • v)) = 0
        rw [map_smul, map_smul, hv' g, smul_zero] }
  apply_mem_toSubmodule g v hv h := by
    have hv' : ∀ g, φ (ρ g v) = 0 := hv
    change φ (ρ h (ρ g v)) = 0
    rw [← Module.End.mul_apply, ← map_mul]
    exact hv' (h * g)

theorem mem_orbitKernel {ρ : Representation ℂ G V} {φ : Module.Dual ℂ V} (v : V) :
    v ∈ orbitKernel ρ φ ↔ ∀ g, φ (ρ g v) = 0 := Iff.rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- A finitely generated admissible representation with a nonzero eigenfunctional
for a central homomorphism has an irreducible admissible quotient with that scalar
character. -/
theorem exists_irreducible_quotient
    (hG : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ H)
    {C : Type uC} [Group C] (z : C →* G) (hz : ∀ c g, z c * g = g * z c) (χ : C →* ℂˣ)
    (ρ : Representation ℂ G V) (hfin : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule)
    (hadm : IsAdmissible ρ) (φ : Module.Dual ℂ V) (hφ : φ ≠ 0)
    (heig : ∀ c v, φ (ρ (z c) v) = (χ c : ℂ) * φ v) :
    ∃ S : Rep.{uV} ℂ G, Representation.IsIrreducible S.ρ ∧ IsAdmissible S.ρ ∧
      Classification.HasScalarCharacter S.ρ z χ ∧
      ∃ f : ρ.IntertwiningMap S.ρ, Function.Surjective f := by
  have hco : IsCoatomic (Subrepresentation ρ) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).isCoatomic_iff.mpr
      inferInstance
  obtain ⟨v₀, hv₀⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  rcases hco.eq_top_or_exists_le_coatom (orbitKernel ρ φ) with htop | ⟨M, hM, hWM⟩
  · exfalso
    have hmem : v₀ ∈ orbitKernel ρ φ := by
      rw [htop]
      exact Submodule.mem_top
    apply hv₀
    simpa using hmem 1
  let σ : Representation ℂ G (V ⧸ M.toSubmodule) :=
    ρ.quotient M.toSubmodule (fun g _ hv => M.apply_mem_toSubmodule g hv)
  let f : ρ.IntertwiningMap σ :=
    { toLinearMap := M.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
  have hf : Function.Surjective f := Submodule.mkQ_surjective _
  refine ⟨Rep.of σ, ?_, ?_, ?_, f, hf⟩
  · exact CuspidalSupport.QuasicuspidalEmbedding.isIrreducible_of_isCoatom f hf M hM
      fun v => Submodule.Quotient.mk_eq_zero M.toSubmodule
  · exact Unramified.SphericalExistence.isAdmissible_of_surjective hG f hf hadm
  · intro c w
    obtain ⟨v, rfl⟩ := hf w
    change Submodule.Quotient.mk (ρ (z c) v) = (χ c : ℂ) • Submodule.Quotient.mk v
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    apply hWM
    intro g
    have hcomm : ρ g (ρ (z c) v) = ρ (z c) (ρ g v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← hz c g, map_mul, Module.End.mul_apply]
    rw [map_sub, map_sub, map_smul, hcomm, heig, map_smul, smul_eq_mul, sub_self]

end Generic

end MaximalConeQuotient

end Langlands

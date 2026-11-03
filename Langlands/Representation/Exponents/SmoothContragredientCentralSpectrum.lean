import Langlands.Representation.Compact.OrbitMeanTranslation
import Langlands.Representation.Exponents.DualEigenfunctionalExistence
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Exponents.Central

/-! # Central-spectrum inversion for the actual smooth contragredient -/

noncomputable section

namespace Langlands

universe uG uA uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type uA} [Group A]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A nonzero central transpose eigenfunctional can be smoothed without losing
its eigencharacter. In the contragredient action the character is inverted. -/
theorem exists_smoothEigenfunctional_of_centralEigenfunctional
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (hG : CompactOpenCofinal G)
    (z : A →* G) (hz : ∀ a, z a ∈ Subgroup.center G) (χ : A →* ℂˣ)
    (φ : Module.Dual ℂ V) (hφ : φ ≠ 0)
    (heig : ∀ a v, φ (ρ (z a) v) = (χ a : ℂ) * φ v) :
    ∃ ℓ : SmoothDual ρ, ℓ ≠ 0 ∧
      ∀ a, smoothContragredient ρ (z a) ℓ = (χ⁻¹ a : ℂ) • ℓ := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : V, φ v ≠ 0 := by
    by_contra! h
    exact hφ (LinearMap.ext h)
  obtain ⟨H, hH⟩ := hρ v
  obtain ⟨K, hK, hKH⟩ := hG H
  let P := Compact.averageMap ρ hρ K hK
  have hPv : P v = v := Compact.averageMap_id ρ hρ K hK v
    (fun k => hH ⟨k, hKH k.property⟩)
  have hPk (k : K) (x : V) : P (ρ k.val x) = P x :=
    Compact.orbitMean_apply (ρ.comp K.toSubgroup.subtype) k x
  let f : Module.Dual ℂ V := φ.comp P
  have hfix (k : K) : ρ.dual k.val f = f := by
    ext x
    change φ (P (ρ k.val⁻¹ x)) = φ (P x)
    exact congrArg φ (hPk k⁻¹ x)
  let ℓ : SmoothDual ρ := ⟨f, K, hfix⟩
  have hPz (a : A) (x : V) : P (ρ (z a) x) = ρ (z a) (P x) := by
    let T : ρ.IntertwiningMap ρ :=
      { toLinearMap := ρ (z a)
        isIntertwining' := fun g => by
          rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul,
            ← map_mul, Subgroup.mem_center_iff.mp (hz a) g] }
    exact (congrArg (fun F : V →ₗ[ℂ] V => F x)
      (Compact.averageMap_commute ρ ρ hρ hρ K hK T)).symm
  refine ⟨ℓ, ?_, fun a => ?_⟩
  · intro h
    have h0 := congrArg (fun ψ : SmoothDual ρ => ψ.val v) h
    change φ (P v) = 0 at h0
    exact hv (hPv ▸ h0)
  · apply Subtype.ext
    ext x
    change φ (P (ρ (z a)⁻¹ x)) = (χ⁻¹ a : ℂ) * φ (P x)
    rw [← map_inv, hPz, heig]
    simp

/-- A chosen nonzero smooth eigenfunctional obtained from a nonzero central
transpose eigenfunctional by compact averaging. -/
def smoothCentralEigenfunctional
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (hG : CompactOpenCofinal G)
    (z : A →* G) (hz : ∀ a, z a ∈ Subgroup.center G) (χ : A →* ℂˣ)
    (φ : Module.Dual ℂ V) (hφ : φ ≠ 0)
    (heig : ∀ a v, φ (ρ (z a) v) = (χ a : ℂ) * φ v) : SmoothDual ρ :=
  Classical.choose
    (exists_smoothEigenfunctional_of_centralEigenfunctional ρ hρ hG z hz χ φ hφ heig)

theorem smoothCentralEigenfunctional_ne_zero
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (hG : CompactOpenCofinal G)
    (z : A →* G) (hz : ∀ a, z a ∈ Subgroup.center G) (χ : A →* ℂˣ)
    (φ : Module.Dual ℂ V) (hφ : φ ≠ 0)
    (heig : ∀ a v, φ (ρ (z a) v) = (χ a : ℂ) * φ v) :
    smoothCentralEigenfunctional ρ hρ hG z hz χ φ hφ heig ≠ 0 :=
  (Classical.choose_spec
    (exists_smoothEigenfunctional_of_centralEigenfunctional ρ hρ hG z hz χ φ hφ heig)).1

theorem smoothCentralEigenfunctional_action
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (hG : CompactOpenCofinal G)
    (z : A →* G) (hz : ∀ a, z a ∈ Subgroup.center G) (χ : A →* ℂˣ)
    (φ : Module.Dual ℂ V) (hφ : φ ≠ 0)
    (heig : ∀ a v, φ (ρ (z a) v) = (χ a : ℂ) * φ v) (a : A) :
    smoothContragredient ρ (z a)
        (smoothCentralEigenfunctional ρ hρ hG z hz χ φ hφ heig) =
      (χ⁻¹ a : ℂ) • smoothCentralEigenfunctional ρ hρ hG z hz χ φ hφ heig :=
  (Classical.choose_spec
    (exists_smoothEigenfunctional_of_centralEigenfunctional ρ hρ hG z hz χ φ hφ heig)).2 a

/-- Every uniform generalized central eigencharacter gives a nonzero ordinary
eigenvector of the actual smooth contragredient for the inverse character. -/
theorem exists_smoothEigenfunctional_of_isGeneralizedEigencharacter
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (hG : CompactOpenCofinal G)
    (z : A →* G) (hz : ∀ a, z a ∈ Subgroup.center G) (χ : A →* ℂˣ)
    (h : IsGeneralizedEigencharacter (ρ.comp z) χ) :
    ∃ ℓ : SmoothDual ρ, ℓ ≠ 0 ∧
      ∀ a, smoothContragredient ρ (z a) ℓ = (χ⁻¹ a : ℂ) • ℓ := by
  obtain ⟨φ, hφ, heig⟩ :=
    DualEigenfunctional.exists_dualEigenfunctional_of_isGeneralizedEigencharacter
      ρ hρ hG z hz χ h
  exact exists_smoothEigenfunctional_of_centralEigenfunctional ρ hρ.1 hG z hz χ φ hφ heig

/-- Central generalized eigencharacters of an admissible representation and
its actual smooth contragredient correspond by inversion. -/
theorem isGeneralizedEigencharacter_smoothContragredient_inv_iff
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (hG : CompactOpenCofinal G)
    (z : A →* G) (hz : ∀ a, z a ∈ Subgroup.center G) (χ : A →* ℂˣ) :
    IsGeneralizedEigencharacter ((smoothContragredient ρ).comp z) χ⁻¹ ↔
      IsGeneralizedEigencharacter (ρ.comp z) χ := by
  constructor
  · intro h
    obtain ⟨ψ, hψ, heig⟩ :=
      exists_smoothEigenfunctional_of_isGeneralizedEigencharacter
        (smoothContragredient ρ)
        (isAdmissible_smoothContragredient_of_compact_cofinal hG ρ hρ) hG z hz χ⁻¹ h
    obtain ⟨v, rfl⟩ := smoothBidual_surjective_of_compact_cofinal hG ρ hρ ψ
    have hinj := smoothBidual_injective_of_compact_cofinal hG ρ hρ.1
    refine isGeneralizedEigencharacter_of_eigenvector (ρ.comp z) χ (v := v) ?_
      (fun a => ?_)
    · intro hv
      exact hψ (by rw [hv, map_zero])
    · apply hinj
      change smoothBidual hρ.1 (ρ (z a) v) = smoothBidual hρ.1 ((χ a : ℂ) • v)
      rw [(smoothBidual hρ.1).isIntertwining _ _ (z a) v, map_smul]
      simpa only [MonoidHom.inv_apply, inv_inv] using heig a
  · intro h
    obtain ⟨ℓ, hℓ, heig⟩ :=
      exists_smoothEigenfunctional_of_isGeneralizedEigencharacter ρ hρ hG z hz χ h
    exact isGeneralizedEigencharacter_of_eigenvector
      ((smoothContragredient ρ).comp z) χ⁻¹ hℓ heig

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The full-center generalized-space convention is the same uniform-power
condition as the central restricted-action convention. -/
theorem generalizedCentralCharacterSpace_ne_bot_iff_isGeneralizedEigencharacter
    (ρ : Representation ℂ G V) (χ : Subgroup.center G →* ℂˣ) :
    generalizedCentralCharacterSpace ρ χ ≠ ⊥ ↔
      IsGeneralizedEigencharacter (ρ.comp (Subgroup.center G).subtype) χ := by
  constructor
  · intro h
    have hne : (generalizedCentralCharacterSpace ρ χ).toSubmodule ≠ ⊥ := by
      intro h0
      exact h (Subrepresentation.toSubmodule_injective h0)
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
    obtain ⟨n, hn⟩ := (mem_generalizedCentralCharacterSpace ρ χ v).mp hv
    exact (isGeneralizedEigencharacter_iff _ _).mpr ⟨n, v, hv0, hn⟩
  · intro h h0
    obtain ⟨n, v, hv0, hv⟩ := (isGeneralizedEigencharacter_iff _ _).mp h
    have hm := (mem_generalizedCentralCharacterSpace ρ χ v).mpr ⟨n, hv⟩
    rw [h0] at hm
    exact hv0 hm

/-- Full-center exponents of an admissible smooth representation and its actual
smooth contragredient correspond by character inversion, including openness. -/
theorem isCentralExponent_smoothContragredient_inv_iff
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (hG : CompactOpenCofinal G)
    (χ : Subgroup.center G →* ℂˣ) :
    IsCentralExponent (smoothContragredient ρ) χ⁻¹ ↔ IsCentralExponent ρ χ := by
  have hker : (χ⁻¹).ker = χ.ker := by
    ext z
    simp
  simp only [IsCentralExponent, hker,
    generalizedCentralCharacterSpace_ne_bot_iff_isGeneralizedEigencharacter]
  exact and_congr Iff.rfl
    (isGeneralizedEigencharacter_smoothContragredient_inv_iff ρ hρ hG
      (Subgroup.center G).subtype (fun z => z.property) χ)

end Langlands

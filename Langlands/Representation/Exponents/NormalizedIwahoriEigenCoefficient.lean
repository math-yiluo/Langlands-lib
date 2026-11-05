import Langlands.Representation.Jacquet.IwahoriEigenCoefficient
import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof

/-! # Exact coefficients for generalized normalized Jacquet exponents

The algebraic comparison uses the actual normalized quotient. Cofinal
Iwahori contractions for the specified element are supplied explicitly.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Iwahori contraction data for one specified element, with arbitrarily small
Levi intersections. This strengthens the existential-element basis predicate. -/
def HasIwahoriContractionBasisAt (N M Nbar : Subgroup G) (g : G) : Prop :=
  ∀ L : OpenSubgroup M, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
    K.toSubgroup.comap M.subtype ≤ L.toSubgroup ∧
      IsIwahoriContraction K N M Nbar g

omit [IsTopologicalGroup G] in
theorem HasIwahoriContractionBasisAt.hasIwahoriContractionBasis
    {N M Nbar : Subgroup G} {g : G}
    (h : HasIwahoriContractionBasisAt N M Nbar g) :
    HasIwahoriContractionBasis N M Nbar := by
  intro L
  obtain ⟨K, hK, hKL, hg⟩ := h L
  exact ⟨K, hK, hKL, g, hg⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A scalar twist of a central Levi action preserves the vectors fixed by
every subgroup of the ordinary Jacquet action. -/
theorem characterTwistedAction_mem_fixedVectors_of_mem_center
    (ρ : Representation ℂ G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (η : M →* ℂˣ)
    (H : Subgroup M) (z : Subgroup.center M)
    {w : Coinvariants ρ N} (hw : w ∈ fixedVectors (action ρ N M hMN) H) :
    characterTwistedAction ρ N M hMN η (z : M) w ∈
      fixedVectors (action ρ N M hMN) H := by
  change (η (z : M) : ℂ) • action ρ N M hMN (z : M) w ∈ _
  apply Submodule.smul_mem
  intro m
  have hm := hw m
  change action ρ N M hMN (m : M) w = w at hm
  change action ρ N M hMN (m : M) (action ρ N M hMN (z : M) w) =
    action ρ N M hMN (z : M) w
  rw [← Module.End.mul_apply, ← map_mul,
    Subgroup.mem_center_iff.mp z.property (m : M),
    map_mul, Module.End.mul_apply, hm]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The scalar-twisted central action restricted to the fixed vectors of the
ordinary Jacquet quotient. -/
def centralTwistedFixedAction
    (ρ : Representation ℂ G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (η : M →* ℂˣ)
    (H : Subgroup M) (z : Subgroup.center M) :
    Module.End ℂ (fixedVectors (action ρ N M hMN) H) :=
  (characterTwistedAction ρ N M hMN η (z : M)).restrict
    (fun _ hw => characterTwistedAction_mem_fixedVectors_of_mem_center
      ρ N M hMN η H z hw)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A nonzero generalized eigenvector in ordinary fixed coinvariants yields
an ordinary eigenvector there after removing the scalar normalization. -/
theorem exists_jacquet_eigenvector_of_twisted_genEigenvector
    (ρ : Representation ℂ G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (η : M →* ℂˣ)
    (H : Subgroup M) (z : Subgroup.center M)
    (μ : ℂ) (d : ℕ) (v : Coinvariants ρ N) (hv0 : v ≠ 0)
    (hvH : v ∈ fixedVectors (action ρ N M hMN) H)
    (hvd : ((characterTwistedAction ρ N M hMN η (z : M) - μ • 1) ^ d) v = 0) :
    ∃ w : Coinvariants ρ N,
      w ≠ 0 ∧ w ∈ fixedVectors (action ρ N M hMN) H ∧
      action ρ N M hMN (z : M) w = ((η (z : M) : ℂ)⁻¹ * μ) • w := by
  let F : Module.End ℂ (Coinvariants ρ N) :=
    characterTwistedAction ρ N M hMN η (z : M)
  let Y := fixedVectors (action ρ N M hMN) H
  let f := centralTwistedFixedAction ρ N M hMN η H z
  have hvgen : v ∈ F.genEigenspace μ d := by
    rw [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker]
    exact hvd
  have hgen : f.HasGenEigenvalue μ d := by
    apply (Module.End.hasGenEigenvalue_iff).mpr
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨⟨v, hvH⟩, ?_, fun h => hv0 (congrArg Subtype.val h)⟩
    change (⟨v, hvH⟩ : Y) ∈ Module.End.genEigenspace (F.restrict _) μ d
    rw [Module.End.genEigenspace_restrict]
    exact hvgen
  obtain ⟨w, hw⟩ := (Module.End.hasEigenvalue_of_hasGenEigenvalue hgen).exists_hasEigenvector
  have heq := congrArg Subtype.val hw.apply_eq_smul
  change (η (z : M) : ℂ) • action ρ N M hMN (z : M) (w : Coinvariants ρ N) =
    μ • (w : Coinvariants ρ N) at heq
  have heq' := congrArg (fun y : Coinvariants ρ N => (η (z : M) : ℂ)⁻¹ • y) heq
  refine ⟨w, fun h => hw.2 (Subtype.ext h), w.property, ?_⟩
  simpa only [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] using heq'

/-- A generalized scalar-twisted Jacquet eigenvector supplies an exact smooth
coefficient under the supplied central Iwahori contraction. -/
theorem exists_eigen_coefficient_of_twisted_genEigenvector
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (η : M →* ℂˣ) (z : Subgroup.center M)
    (h : IsIwahoriContraction K N M Nbar ((z : M) : G))
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (μ : ℂ) (d : ℕ) (v : Coinvariants ρ N) (hv0 : v ≠ 0)
    (hvK : v ∈ fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype))
    (hvd : ((characterTwistedAction ρ N M hMN η (z : M) - μ • 1) ^ d) v = 0) :
    ∃ (x : fixedVectors ρ K.toSubgroup) (ℓ : SmoothDual ρ),
      (ℓ : Module.Dual ℂ V) x ≠ 0 ∧
      (∀ k ∈ K, ∀ y, (ℓ : Module.Dual ℂ V) (ρ k y) = (ℓ : Module.Dual ℂ V) y) ∧
      ∀ n : ℕ, (ℓ : Module.Dual ℂ V) (ρ (((z : M) : G) ^ n) x) =
        ((η (z : M) : ℂ)⁻¹ * μ) ^ n * (ℓ : Module.Dual ℂ V) x := by
  obtain ⟨w, hw0, hwK, hw⟩ :=
    exists_jacquet_eigenvector_of_twisted_genEigenvector
      ρ N M hMN η (K.toSubgroup.comap M.subtype) z μ d v hv0 hvK hvd
  obtain ⟨x, ℓ, _, hℓx, hℓK, hℓn⟩ :=
    exists_eigen_coefficient_of_jacquet_eigenvector
      ρ hρ K hK N M Nbar hMN ((z : M) : G) h hfin
      ((η (z : M) : ℂ)⁻¹ * μ) w hw0 hwK hw
  exact ⟨x, ℓ, hℓx, hℓK, hℓn⟩

end Langlands.Jacquet

namespace Langlands.Aubert.General

universe uG uV uB

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- The actual normalized localized coinvariant module identified with the
inverse-half-character twist of ordinary coinvariants. -/
def normalizedJacquetOrdinaryEquiv
    (N M : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N) (π : SmoothRep.{0, uG, uV} ℂ G) :
    ((normalizedJacquetFunctor N M hN hMN).obj π).representation.Equiv
      (Jacquet.characterTwistedAction π.representation N M hMN
        (HaarModulus.closedInverseHalfCharacter N hN M hMN)) :=
  twistEquiv (HaarModulus.closedInverseHalfCharacter N hN M hMN)
    (Jacquet.Localization.trivialEquiv π.representation N M hMN)

@[simp]
theorem normalizedJacquetOrdinaryEquiv_mk
    (N M : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N) (π : SmoothRep.{0, uG, uV} ℂ G) (v : π) :
    normalizedJacquetOrdinaryEquiv N M hN hMN π
        (Jacquet.Localization.mk π.representation N 1 v) =
      Jacquet.mk π.representation N v := rfl

/-- An actual generalized normalized Jacquet character yields an exact smooth
matrix coefficient at a specified central point when cofinal Iwahori
contractions for that point are supplied. -/
theorem exists_eigen_coefficient_of_normalizedJacquet_generalizedEigencharacter
    {B : Type uB} [Group B]
    (N M Nbar : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N)
    (π : SmoothRep.{0, uG, uV} ℂ G) (hπ : π.IsAdmissible)
    (ι : B →* M) (χ : B →* ℂˣ)
    (hχ : IsGeneralizedEigencharacter
      (((normalizedJacquetFunctor N M hN hMN).obj π).representation.comp ι) χ)
    (b : B) (hb : ι b ∈ Subgroup.center M)
    (hbasis : Jacquet.HasIwahoriContractionBasisAt N M Nbar ((ι b : M) : G)) :
    ∃ (K : OpenSubgroup G), IsCompact (K : Set G) ∧
      ∃ (x : fixedVectors π.representation K.toSubgroup)
        (ℓ : SmoothDual π.representation),
        (ℓ : Module.Dual ℂ π) x ≠ 0 ∧
        (∀ k ∈ K, ∀ y,
          (ℓ : Module.Dual ℂ π) (π.representation k y) = (ℓ : Module.Dual ℂ π) y) ∧
        ∀ n : ℕ, (ℓ : Module.Dual ℂ π) (π.representation (((ι b : M) : G) ^ n) x) =
          ((HaarModulus.closedInverseHalfCharacter N hN M hMN (ι b) : ℂ)⁻¹ *
            (χ b : ℂ)) ^ n * (ℓ : Module.Dual ℂ π) x := by
  let η := HaarModulus.closedInverseHalfCharacter N hN M hMN
  let e := normalizedJacquetOrdinaryEquiv N M hN hMN π
  let eι : Representation.Equiv
      (((normalizedJacquetFunctor N M hN hMN).obj π).representation.comp ι)
        ((Jacquet.characterTwistedAction π.representation N M hMN η).comp ι) :=
    Representation.Equiv.mk e.toLinearEquiv (by
      intro t
      exact e.isIntertwining' (ι t))
  have hχ' := (isGeneralizedEigencharacter_iff_of_equiv eι χ).mp hχ
  obtain ⟨d, v, hv0, hvd⟩ := (isGeneralizedEigencharacter_iff _ χ).mp hχ'
  obtain ⟨L, hvL⟩ :=
    Jacquet.isSmooth_action π.representation N M hMN hπ.1 v
  obtain ⟨K, hK, hKL, hg⟩ := hbasis L
  have hvK : v ∈ fixedVectors (Jacquet.action π.representation N M hMN)
      (K.toSubgroup.comap M.subtype) := by
    intro m
    exact hvL ⟨m.val, hKL m.property⟩
  obtain ⟨x, ℓ, hℓx, hℓK, hℓn⟩ :=
    Jacquet.exists_eigen_coefficient_of_twisted_genEigenvector
      π.representation hπ.1 K hK N M Nbar hMN η ⟨ι b, hb⟩ hg (hπ.2 K)
      (χ b : ℂ) d v hv0 hvK (hvd b)
  exact ⟨K, hK, x, ℓ, hℓx, hℓK, hℓn⟩

end Langlands.Aubert.General

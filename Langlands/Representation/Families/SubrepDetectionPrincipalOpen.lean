import Langlands.Representation.Families.GlobalCompressionPrincipalOpen
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof
import Langlands.Representation.Smooth.FixedVectors.NormalizedJacquetBridgeProof
import Langlands.Representation.Category.Contragredient

/-! # Irreducibility neighborhoods from fixed-vector detection of subrepresentations

The compact-compression neighborhoods of `CompactCompressionPrincipalOpen` use
detection of every irreducible subquotient by one compact open subgroup. The
matrix argument only needs two consequences of that hypothesis for each fiber:
every nonzero subrepresentation contains a nonzero fixed vector, and every
subrepresentation containing all fixed vectors is the whole representation.
This module records that weaker hypothesis and the corresponding neighborhoods,
together with two facts about fixed smooth functionals.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily.SubrepDetectionPrincipalOpen

open Plancherel CompactCompressionMatrices CompactCompressionPrincipalOpen
  LocalizedMatrixPrincipalOpen MatrixGenerationWitness UnramifiedPolynomialWitness

universe uB uS uG uV uW un u uX

section Detection

variable {G : Type uG} [Group G]

/-- A subgroup `K` detects the representation `ρ` through subrepresentations:
every nonzero invariant subspace contains a nonzero `K`-fixed vector, and every
invariant subspace containing all `K`-fixed vectors is the whole space. -/
def IsSubrepDetected {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) : Prop :=
  (∀ S : Subrepresentation ρ, S ≠ ⊥ →
      ∃ v ∈ S.toSubmodule, v ∈ fixedVectors ρ K ∧ v ≠ 0) ∧
    ∀ S : Subrepresentation ρ, fixedVectors ρ K ≤ S.toSubmodule → S = ⊤

/-- Detection through subrepresentations is transported by an equivariant
linear equivalence. -/
theorem IsSubrepDetected.of_equiv {V W : Type uV} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) {K : Subgroup G} (h : IsSubrepDetected ρ K) :
    IsSubrepDetected σ K := by
  refine ⟨fun S hS => ?_, NormalizedJacquetBridge.generation_of_equiv e K h.2⟩
  let C : Subrepresentation ρ :=
    { toSubmodule := S.toSubmodule.comap e.toLinearEquiv.toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        change e.toIntertwiningMap (ρ g v) ∈ S
        rw [Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v]
        exact S.apply_mem_toSubmodule g hv }
  have hC : C ≠ ⊥ := by
    intro hC
    apply hS
    apply Subrepresentation.toSubmodule_injective
    apply (Submodule.eq_bot_iff _).mpr
    intro w hw
    obtain ⟨v, rfl⟩ := e.surjective w
    have hv : v ∈ C.toSubmodule := hw
    rw [hC] at hv
    have hv0 : v = 0 := (Submodule.mem_bot ℂ).mp hv
    rw [hv0, map_zero]
  obtain ⟨v, hvC, hvK, hv0⟩ := h.1 C hC
  refine ⟨e v, hvC, map_mem_fixedVectors e.toIntertwiningMap hvK, fun hz => hv0 ?_⟩
  exact e.injective (hz.trans (map_zero e).symm)

/-- An irreducible representation detected through subrepresentations has a
nonzero fixed vector. -/
theorem IsSubrepDetected.exists_fixed_ne_zero {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {K : Subgroup G} (h : IsSubrepDetected ρ K)
    (hirr : ρ.IsIrreducible) : ∃ v : V, v ∈ fixedVectors ρ K ∧ v ≠ 0 := by
  obtain ⟨v, -, hv, hv0⟩ := h.1 ⊤ top_ne_bot
  exact ⟨v, hv, hv0⟩

end Detection

section Contragredient

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A nonzero vector fixed by a compact open subgroup `L` gives a nonzero
`L`-fixed smooth functional. -/
theorem exists_contragredient_fixed_ne_zero (A : SmoothRep.{0, uG, uV} ℂ G)
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) {v : A}
    (hv : v ∈ fixedVectors A.representation L.toSubgroup) (hv0 : v ≠ 0) :
    ∃ ℓ : A.contragredient,
      ℓ ∈ fixedVectors A.contragredient.representation L.toSubgroup ∧ ℓ ≠ 0 := by
  let u : fixedVectors A.representation L.toSubgroup := ⟨v, hv⟩
  have hu : u ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (fixedVectors A.representation L.toSubgroup),
      φ u ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hu ((Module.forall_dual_apply_eq_zero_iff ℂ u).mp hno)
  obtain ⟨ℓ, hℓ⟩ :=
    (smoothDualFixedRestriction_bijective A.representation A.isSmooth L hL).2 φ
  refine ⟨ℓ.val, ℓ.property, fun h0 => hφ ?_⟩
  rw [← hℓ]
  have h0' : (ℓ.val : SmoothDual A.representation) = 0 := h0
  change smoothDualPairing A.representation (ℓ.val : SmoothDual A.representation) v = 0
  rw [h0', map_zero, LinearMap.zero_apply]

/-- If a compact open subgroup `L` fixes no nonzero vector, it fixes no nonzero
smooth functional. -/
theorem contragredient_fixed_eq_zero (A : SmoothRep.{0, uG, uV} ℂ G)
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G))
    (hA : ∀ v ∈ fixedVectors A.representation L.toSubgroup, v = 0) :
    ∀ ℓ ∈ fixedVectors A.contragredient.representation L.toSubgroup, ℓ = 0 := by
  intro ℓ hℓ
  have hinj := (smoothDualFixedRestriction_bijective A.representation A.isSmooth L hL).1
  have h0 : (⟨ℓ, hℓ⟩ : fixedVectors (smoothContragredient A.representation) L.toSubgroup) =
      0 := by
    apply hinj
    rw [map_zero]
    apply LinearMap.ext
    intro u
    have hu0 : u = 0 := Subtype.ext (hA u.val u.property)
    rw [hu0, map_zero, map_zero]
  exact congrArg Subtype.val h0

end Contragredient

section Matrices

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : SmoothRep.{0, uG, uV} ℂ G)
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
variable {n : Type un} [Fintype n]
variable (e : Module.Basis n ℂ (fixedVectors A.representation K.toSubgroup))

/-- Under detection through subrepresentations, matrix irreducibility of the
compact compression family forces irreducibility of the representation. -/
theorem isIrreducible_of_fixedMatrix_of_subrepDetected [Nontrivial A]
    (hdet : IsSubrepDetected A.representation K.toSubgroup)
    (hirr : UnitarizabilityContinuation.IsIrreducibleFamily (fixedMatrix A K hK e)) :
    A.IsIrreducible := by
  classical
  refine { exists_pair_ne := ⟨⊥, ⊤, fun he => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · obtain ⟨v, hv⟩ := exists_ne (0 : A)
    apply hv
    have hmem : v ∈ (⊤ : Subrepresentation A.representation) := trivial
    rw [← he] at hmem
    exact hmem
  · by_cases hS : S = ⊥
    · exact Or.inl hS
    right
    let U : Submodule ℂ (n → ℂ) := S.toSubmodule.comap
      ((fixedVectors A.representation K.toSubgroup).subtype ∘ₗ e.equivFun.symm.toLinearMap)
    have hU : ∀ g v, v ∈ U → (fixedMatrix A K hK e g).mulVec v ∈ U := by
      intro g v hv
      change (e.equivFun.symm ((fixedMatrix A K hK e g).mulVec v) : A) ∈ S
      rw [← fixedMatrix_mulVec, LinearEquiv.symm_apply_apply]
      exact averageMap_mem A K hK S (S.apply_mem_toSubmodule g hv)
    rcases hirr U hU with h | h
    · exfalso
      obtain ⟨w, hwS, hwK, hw0⟩ := hdet.1 S hS
      let v : fixedVectors A.representation K.toSubgroup := ⟨w, hwK⟩
      have hv : e.equivFun v ∈ U := by
        change (e.equivFun.symm (e.equivFun v) : A) ∈ S
        rw [LinearEquiv.symm_apply_apply]
        exact hwS
      have hv0 : e.equivFun v = 0 := by simpa only [h, Submodule.mem_bot] using hv
      have hv0' : v = 0 := e.equivFun.injective (hv0.trans (map_zero e.equivFun).symm)
      exact hw0 (congrArg Subtype.val hv0')
    · apply hdet.2 S
      intro v hv
      have hvU : e.equivFun ⟨v, hv⟩ ∈ U := h ▸ Submodule.mem_top
      change (e.equivFun.symm (e.equivFun ⟨v, hv⟩) : A) ∈ S at hvU
      change v ∈ S
      rw [LinearEquiv.symm_apply_apply] at hvU
      exact hvU

end Matrices

section PrincipalOpen

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
variable {S : Type uS} [CommRing S] [Algebra B S] [Algebra ℂ S]
variable [IsScalarTower ℂ B S] (g : B) [IsLocalization.Away g S]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : SmoothRep.{0, uG, uV} ℂ G)
variable [Module S A] [SMulCommClass ℂ S A]
variable [HasCompatibleCoefficients S A.representation]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
variable {n : Type un} [Fintype n] [DecidableEq n]
variable (b : Module.Basis n S (fixedVectors A.representation K.toSubgroup))

include hK b in
/-- A coefficient basis, actual full specialization, and detection of every
fiber through subrepresentations give a principal regular irreducibility
neighborhood of an irreducible fiber. -/
theorem exists_regular_principal_neighborhood_of_subrepDetected
    {X : Type uX} (χ : X → B →ₐ[ℂ] ℂ)
    (D : X → SmoothRep.{0, uG, uW} ℂ G)
    (hsp : ∀ x (hx : χ x g ≠ 0),
      IsFullSpecialization S A (awayEvaluation g (χ x) hx) (D x))
    (hdet : ∀ x, IsSubrepDetected (D x).representation K.toSubgroup)
    (x₀ : X) (hg₀ : χ x₀ g ≠ 0) (hirr₀ : (D x₀).IsIrreducible) :
    ∃ f : B, χ x₀ f ≠ 0 ∧ ∀ x, χ x f ≠ 0 → (D x).IsIrreducible := by
  obtain ⟨e₀, he₀⟩ := exists_fixedBasis S A K hK b
    (awayEvaluation g (χ x₀) hg₀) (D x₀) (hsp x₀ hg₀)
  obtain ⟨v₀, hv₀, hv₀ne⟩ := (hdet x₀).exists_fixed_ne_zero hirr₀
  have : Nontrivial (fixedVectors (D x₀).representation K.toSubgroup) :=
    ⟨⟨⟨v₀, hv₀⟩, 0, fun he => hv₀ne (congrArg Subtype.val he)⟩⟩
  have : Nonempty n := e₀.index_nonempty
  have hm₀ : UnitarizabilityContinuation.IsIrreducibleFamily
      (specialize (coefficientMatrix S A K hK b) (awayEvaluation g (χ x₀) hg₀)) := by
    rw [← he₀]
    exact fixedMatrix_isIrreducible (D x₀) K hK e₀ hirr₀
  obtain ⟨f, hf₀, hf⟩ :=
    LocalizedMatrixPrincipalOpen.exists_regular_principal_neighborhood g
      (coefficientMatrix S A K hK b) (χ x₀) hg₀ hm₀
  refine ⟨f, hf₀, ?_⟩
  intro x hx
  obtain ⟨hg, hm⟩ := hf (χ x) hx
  obtain ⟨e, he⟩ := exists_fixedBasis S A K hK b
    (awayEvaluation g (χ x) hg) (D x) (hsp x hg)
  have : Nontrivial (D x) := by
    let j : n := Classical.choice inferInstance
    exact ⟨⟨(e j : D x), 0, fun hz => e.ne_zero j (Subtype.ext hz)⟩⟩
  apply isIrreducible_of_fixedMatrix_of_subrepDetected (D x) K hK e (hdet x)
  rwa [he]

end PrincipalOpen

section ActualCharacters

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : SmoothRep.{0, uG, uV} ℂ G)
variable [Module B A] [SMulCommClass ℂ B A]
variable [HasCompatibleCoefficients B A.representation]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (M : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (hM : GroupScheme.IsConnectedReductive M)

local instance subrepDetectionActualTopology :
    TopologicalSpace (GroupScheme.rationalPoints M) :=
  rationalPointTopology F M.X

include hK in
/-- A global coefficient family and detection of every fiber through
subrepresentations by one compact open subgroup give a polynomial principal
irreducibility neighborhood of an irreducible fiber. -/
theorem exists_polynomial_principal_neighborhood_of_family_of_subrepDetected
    (e : B ≃ₐ[ℂ]
      unramifiedRegularFunctions (fun ψ => (rationalNormCharacters M ψ).toMul))
    (D : unramifiedCharacters (fun ψ => (rationalNormCharacters M ψ).toMul) →
      SmoothRep.{0, uG, uW} ℂ G)
    (hA : IsGlobalCoefficientFamily A M e D)
    (hdet : ∀ χ, IsSubrepDetected (D χ).representation K.toSubgroup)
    (χ₀ : unramifiedCharacters (fun ψ => (rationalNormCharacters M ψ).toMul))
    (hirr₀ : (D χ₀).IsIrreducible) :
    ∃ p : MvPolynomial (Fin (rationalImageRank M)) ℂ,
      χ₀ ∈ rationalUnramifiedPrincipalOpen M hM p ∧
      ∀ χ ∈ rationalUnramifiedPrincipalOpen M hM p, (D χ).IsIrreducible := by
  classical
  obtain ⟨_, _⟩ := hA.1 K hK
  let b := Module.Free.chooseBasis B (fixedVectors A.representation K.toSubgroup)
  let := isLocalization_away_one (B := B)
  obtain ⟨f, hf₀, hf⟩ := exists_regular_principal_neighborhood_of_subrepDetected
    (S := B) (1 : B) A K hK b (coefficientCharacter M e) D
    (fun χ hχ => by rw [awayEvaluation_one]; exact hA.2 χ) hdet χ₀ (by simp) hirr₀
  refine ⟨rationalRegularPolynomial M hM (e f), ?_, ?_⟩
  · rw [principalOpen_rationalRegularPolynomial]
    exact hf₀
  · intro χ hχ
    rw [principalOpen_rationalRegularPolynomial] at hχ
    exact hf χ hχ

end ActualCharacters

end Langlands.Renard.AlgebraicFamily.SubrepDetectionPrincipalOpen

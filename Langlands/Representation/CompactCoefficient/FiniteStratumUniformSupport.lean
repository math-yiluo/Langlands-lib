import Langlands.Representation.CompactCoefficient.UniformSupportStatement
import Langlands.Representation.Hecke.UniformFixedLevelBounds

/-! # Common coefficient support from finitely many fixed-level classes -/

noncomputable section

namespace Langlands.CompactCoefficientClass

open MeasureTheory Hecke CategoryTheory

universe uG uV uW uI

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

section OneRepresentation

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
  {ι : Type uI} (b : Module.Basis ι ℂ (fixedVectors ρ K.toSubgroup))

/-- The union of the topological supports of the inverse coefficients of the
fixed basis vectors against the averaged coordinate functionals. -/
def basisInverseCoefficientSupport : Set G :=
  ⋃ i, ⋃ j, tsupport (fun g : G =>
    fixedExtension μ ρ hρ K hK (b.coord j) (ρ g⁻¹ (b i)))

/-- A finite fixed basis and compact smooth-dual coefficients make this
explicit support envelope compact. -/
theorem isCompact_basisInverseCoefficientSupport [Finite ι]
    (hc : HasCompactSmoothDualCoefficients ρ) :
    IsCompact (basisInverseCoefficientSupport μ K hK ρ hρ b) := by
  apply isCompact_iUnion
  intro i
  apply isCompact_iUnion
  intro j
  exact (inverseCoefficient_hasCompactSupport hc
    (fixedExtension_isSmoothVector μ ρ hρ K hK (b.coord j)) (b i)).isCompact

/-- Vanishing of the finitely many coordinate coefficients forces every
coefficient with both inputs fixed at the same level to vanish. -/
theorem support_subset_basisInverseCoefficientSupport
    {v : V} (hv : v ∈ fixedVectors ρ K.toSubgroup)
    (ℓ : Module.Dual ℂ V)
    (hℓ : ∀ k ∈ K, ∀ w, ℓ (ρ k w) = ℓ w) :
    Function.support (fun g : G => ℓ (ρ g⁻¹ v)) ⊆
      basisInverseCoefficientSupport μ K hK ρ hρ b := by
  classical
  intro g hg
  by_contra houtside
  let P := fixedProjection μ ρ hρ K hK
  let A : Module.End ℂ (fixedVectors ρ K.toSubgroup) :=
    P ∘ₗ ρ g⁻¹ ∘ₗ (fixedVectors ρ K.toSubgroup).subtype
  have hA : A = 0 := by
    apply b.ext
    intro i
    apply b.ext_elem
    intro j
    have hzero : fixedExtension μ ρ hρ K hK (b.coord j)
        (ρ g⁻¹ (b i)) = 0 := by
      by_contra hnonzero
      exact houtside (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨j, subset_tsupport _ hnonzero⟩⟩)
    rw [fixedExtension_apply] at hzero
    change b.coord j (P (ρ g⁻¹ (b i))) = b.coord j 0
    rw [map_zero]
    exact hzero
  have hP : P (ρ g⁻¹ v) = 0 :=
    LinearMap.congr_fun hA ⟨v, hv⟩
  apply hg
  calc
    ℓ (ρ g⁻¹ v) = ℓ (P (ρ g⁻¹ v)) :=
      (apply_heckeAction_normalizedIndicator μ ρ hρ K hK hℓ _).symm
    _ = 0 := by rw [hP]; exact map_zero ℓ

end OneRepresentation

include μ hK in
/-- One compact irreducible representation has a common support envelope
for all coefficients whose two inputs are fixed at the given level. -/
theorem exists_compact_fixedLevel_support
    (D : IrreducibleCompactCoefficientRep.{uG, uV} G) :
    ∃ C : Set G, IsCompact C ∧
      ∀ (v : D.obj), v ∈ fixedVectors D.obj.representation K.toSubgroup →
        ∀ ℓ : Module.Dual ℂ D.obj,
          (∀ k ∈ K, ∀ w, ℓ (D.obj.representation k w) = ℓ w) →
          Function.support (fun g : G => ℓ (D.obj.representation g⁻¹ v)) ⊆ C := by
  let := finiteDimensional_fixedVectors μ D.obj.representation D.obj.isSmooth
    K hK D.property.1 D.property.2
  let b := Module.finBasis ℂ (fixedVectors D.obj.representation K.toSubgroup)
  exact ⟨basisInverseCoefficientSupport μ K hK D.obj.representation D.obj.isSmooth b,
    isCompact_basisInverseCoefficientSupport μ K hK D.obj.representation
      D.obj.isSmooth b D.property.2,
    fun v hv ℓ hℓ => support_subset_basisInverseCoefficientSupport
      μ K hK D.obj.representation D.obj.isSmooth b hv ℓ hℓ⟩

section Transport

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- The same compact support bound transfers along a representation
equivalence, even between independent carrier universes. -/
theorem fixedLevel_support_of_equiv (e : ρ.Equiv σ) {C : Set G}
    (hC : ∀ (v : V), v ∈ fixedVectors ρ K.toSubgroup →
      ∀ ℓ : Module.Dual ℂ V,
        (∀ k ∈ K, ∀ w, ℓ (ρ k w) = ℓ w) →
        Function.support (fun g : G => ℓ (ρ g⁻¹ v)) ⊆ C) :
    ∀ (w : W), w ∈ fixedVectors σ K.toSubgroup →
      ∀ ℓ : Module.Dual ℂ W,
        (∀ k ∈ K, ∀ y, ℓ (σ k y) = ℓ y) →
        Function.support (fun g : G => ℓ (σ g⁻¹ w)) ⊆ C := by
  intro w hw ℓ hℓ g hg
  let v : fixedVectors ρ K.toSubgroup :=
    (fixedVectorsEquiv e K.toSubgroup).symm ⟨w, hw⟩
  have he : e (v : V) = w := e.apply_symm_apply w
  let Λ : Module.Dual ℂ V := ℓ ∘ₗ e.toLinearMap
  have heρ : ∀ g y, e (ρ g y) = σ g (e y) :=
    fun g y => congrArg (fun f : V →ₗ[ℂ] W => f y) (e.isIntertwining' g)
  have hΛ : ∀ k ∈ K, ∀ y, Λ (ρ k y) = Λ y := by
    intro k hk y
    change ℓ (e (ρ k y)) = ℓ (e y)
    rw [heρ]
    exact hℓ k hk (e y)
  apply hC v v.property Λ hΛ
  change ℓ (e (ρ g⁻¹ v)) ≠ 0
  rwa [heρ, he]

end Transport

include μ hK in
/-- Finitely many actual compact irreducible classes at a compact open level
give one compact support for all coefficients tested at that level. -/
theorem hasUniformFixedLevelCoefficientSupport_of_finite_fixedStratum
    (hfin : (fixedStratum.{uG, uV} K.toSubgroup).Finite) :
    HasUniformFixedLevelCoefficientSupport.{uG, uV} K.toSubgroup := by
  classical
  let S := fixedStratum.{uG, uV} (G := G) K.toSubgroup
  let ι := {c // c ∈ S}
  let : Finite ι := hfin.to_subtype
  have hex := fun c : ι => exists_compact_fixedLevel_support μ K hK c.1.out
  choose C hcompact hsupport using hex
  refine ⟨⋃ c : ι, C c, isCompact_iUnion hcompact, ?_⟩
  intro D v hv ℓ hℓ g hg
  have hv0 : v ≠ 0 := by
    intro hz
    apply hg
    simp [hz]
  have hc : ofRep D ∈ S :=
    (hasFixedVector_ofRep_iff_exists K.toSubgroup D).mpr ⟨v, hv, hv0⟩
  let c : ι := ⟨ofRep D, hc⟩
  have heq : ofRep c.1.out = ofRep D := Quotient.out_eq _
  obtain ⟨e⟩ := (ofRep_eq_iff c.1.out D).mp heq
  let E := SmoothRep.equivOfIso
    ((irreducibleCompactCoefficientProperty G).ι.mapIso e)
  exact Set.mem_iUnion.mpr ⟨c,
    fixedLevel_support_of_equiv K E (hsupport c) v hv ℓ hℓ hg⟩

/-- The actual Haar Hecke sandwich already supplies the common coefficient
support, using its algebraic finite-class bound and finite fixed bases. -/
theorem hasUniformFixedLevelCoefficientSupport_of_sandwich
    (D : FixedLevelSandwich μ K hK) :
    HasUniformFixedLevelCoefficientSupport.{uG, uV} K.toSubgroup :=
  hasUniformFixedLevelCoefficientSupport_of_finite_fixedStratum μ K hK
    (fixedStratum_finite_of_sandwich μ K hK sandwichSimpleModuleDimensionBound
      D.edge D.middle D.commute D.span)

end Langlands.CompactCoefficientClass

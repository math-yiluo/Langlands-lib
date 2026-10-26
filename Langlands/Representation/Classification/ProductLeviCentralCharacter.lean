import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Exponents.Jacquet
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Full central characters from block-scalar characters

The block-scalar torus is identified with the entire center of a product Levi.
This gives the actual unitary central-character datum used by analytic
temperedness, without any assertion about integrability.
-/

noncomputable section

namespace Langlands

universe uR uF uV uG uH

namespace GeneralLinear.BlockShape

variable {n : ℕ} (B : BlockShape n) (R : Type uR) [CommRing R]

/-- Block scalars with their membership certificate in the full Levi center. -/
def blockScalarToCenter :
    (Fin B.length → Rˣ) →* Subgroup.center (B.Levi R) :=
  (B.blockScalarLevi R).codRestrict _ (B.blockScalarLevi_mem_center R)

@[simp]
theorem blockScalarToCenter_val (a : Fin B.length → Rˣ) :
    (B.blockScalarToCenter R a).val = B.blockScalarLevi R a := rfl

theorem blockScalarToCenter_bijective :
    Function.Bijective (B.blockScalarToCenter R) := by
  constructor
  · intro a b hab
    funext i
    apply (GeneralLinear.scalarEmbedding (R := R) (B.positive i)).injective
    exact congrArg (fun z : Subgroup.center (B.Levi R) => z.val i) hab
  · intro z
    have hz := z.property
    simp only [Subgroup.center_pi, Subgroup.mem_pi, Set.mem_univ, true_implies,
      Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at hz
    choose a ha using hz
    exact ⟨a, Subtype.ext (funext ha)⟩

/-- The block-scalar torus is the full center of the actual product Levi. -/
def blockScalarCenterEquiv :
    (Fin B.length → Rˣ) ≃* Subgroup.center (B.Levi R) :=
  MulEquiv.ofBijective (B.blockScalarToCenter R) (B.blockScalarToCenter_bijective R)

@[simp]
theorem blockScalarCenterEquiv_val (a : Fin B.length → Rˣ) :
    (B.blockScalarCenterEquiv R a).val = B.blockScalarLevi R a := rfl

end GeneralLinear.BlockShape

namespace Classification

/-- A scalar character of a smooth nonzero representation has open kernel.
The stabilizer argument is adapted from Worker 349's
`TemperedExponentEdgeProof.scalarCharacter_open_kernel`. -/
theorem HasScalarCharacter.isOpen_ker
    {G : Type uG} [Group G] [TopologicalSpace G]
    {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    {ρ : Representation ℂ G V} {f : H →* G} {χ : H →* ℂˣ}
    (hact : HasScalarCharacter ρ f χ) (hf : Continuous f) (hρ : IsSmooth ρ) :
    IsOpen (χ.ker : Set H) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨K, hK⟩ := hρ v
  apply Subgroup.isOpen_mono (H₁ := K.toSubgroup.comap f) ?_ (K.isOpen.preimage hf)
  intro a ha
  change χ a = 1
  apply Units.ext
  apply smul_left_injective ℂ hv
  change (χ a : ℂ) • v = (1 : ℂ) • v
  rw [← hact, one_smul]
  exact hK ⟨f a, ha⟩

/-- A prescribed scalar character along a central homomorphism agrees with
the restriction of an actual unitary central character. -/
theorem HasScalarCharacter.eq_unitaryCentralCharacter
    {G : Type uG} [Group G] [TopologicalSpace G]
    {H : Type uH} [Group H]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    {ρ : Representation ℂ G V} (f : H →* Subgroup.center G)
    (χ : H →* ℂˣ)
    (hact : HasScalarCharacter ρ ((Subgroup.center G).subtype.comp f) χ)
    (c : UnitaryCentralCharacter ρ) (a : H) :
    χ a = c.character (f a) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply Units.ext
  apply smul_left_injective ℂ hv
  exact (hact a v).symm.trans (c.acts (f a) v)

end Classification

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  (ρ : Representation ℂ (B.Levi F.Carrier) V)
  (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)

/-- Transport an exact unitary block-scalar character to the full center.
Smoothness supplies the open kernel of the transported character. -/
def unitaryCentralCharacterOfBlockScalar
    (hρ : letI := T.topology; IsSmooth ρ)
    (hact : Classification.HasScalarCharacter ρ (B.blockScalarLevi F.Carrier) χ)
    (hnorm : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    letI := T.topology
    UnitaryCentralCharacter ρ := by
  let := T.topology
  have := T.leviTopologicalGroup B
  let e := B.blockScalarCenterEquiv F.Carrier
  let ω : Subgroup.center (B.Levi F.Carrier) →* ℂˣ :=
    χ.comp e.symm.toMonoidHom
  have hω : Classification.HasScalarCharacter ρ
      (Subgroup.center (B.Levi F.Carrier)).subtype ω := by
    intro z v
    obtain ⟨a, rfl⟩ := e.surjective z
    change ρ (B.blockScalarLevi F.Carrier a) v =
      (χ (e.symm (e a)) : ℂ) • v
    rw [e.symm_apply_apply]
    exact hact a v
  exact {
    character := ω
    isOpen_ker := hω.isOpen_ker continuous_subtype_val hρ
    norm_eq_one := fun z => hnorm (e.symm z)
    acts := hω }

/-- The constructed full-center character restricts to the prescribed one. -/
@[simp]
theorem unitaryCentralCharacterOfBlockScalar_character
    (hρ : letI := T.topology; IsSmooth ρ)
    (hact : Classification.HasScalarCharacter ρ (B.blockScalarLevi F.Carrier) χ)
    (hnorm : ∀ a, ‖(χ a : ℂ)‖ = 1) (a : Fin B.length → F.Carrierˣ) :
    letI := T.topology
    (T.unitaryCentralCharacterOfBlockScalar B ρ χ hρ hact hnorm).character
      (B.blockScalarToCenter F.Carrier a) = χ a := by
  let := T.topology
  change χ ((B.blockScalarCenterEquiv F.Carrier).symm
    (B.blockScalarCenterEquiv F.Carrier a)) = χ a
  rw [MulEquiv.symm_apply_apply]

/-- Analytic temperedness forces any prescribed block-scalar character
of a nonzero representation to be unitary. -/
theorem norm_blockScalarCharacter_eq_one_of_isTemperedModCenter
    (hact : Classification.HasScalarCharacter ρ (B.blockScalarLevi F.Carrier) χ) :
    letI := T.topology
    ∀ [MeasurableSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      (μ : MeasureTheory.Measure
        (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))) [μ.IsHaarMeasure],
      IsTemperedModCenter ρ μ → ∀ a, ‖(χ a : ℂ)‖ = 1 := by
  let := T.topology
  intro _ μ _ h a
  obtain ⟨c, _⟩ := h.2
  have heq := hact.eq_unitaryCentralCharacter
    (B.blockScalarToCenter F.Carrier) χ c a
  rw [heq]
  exact c.norm_eq_one _

end PadicField.TopologicalData

end Langlands

import Langlands.Shimura.PEL.PolynomialDescent
import Langlands.Shimura.PEL.HodgeDeterminantReflexProof

/-! # The regular Hodge determinant over the actual cocharacter reflex field -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    (hΦ : IsCMSection E K Φ)
    {ι : Type} [Fintype ι]

/-- The constructed determinant with coefficients in the existing reflex field. -/
def kottwitzReflexDeterminant (a : ι → A) :
    MvPolynomial ι (D.kottwitzCocharacterReflexField C) :=
  PolynomialDescent.descend (D.kottwitzCocharacterReflexField C).val.toRingHom
    (D.kottwitzHodgeDeterminant C a)
    (fun d => ⟨⟨_, D.kottwitzHodgeDeterminantReflexDescent C hΦ ι a d⟩, rfl⟩)

@[simp] theorem map_kottwitzReflexDeterminant (a : ι → A) :
    MvPolynomial.map (D.kottwitzCocharacterReflexField C).val.toRingHom
      (D.kottwitzReflexDeterminant C hΦ a) =
        D.kottwitzHodgeDeterminant C a :=
  PolynomialDescent.map_descend _ _ _

@[simp] theorem coe_coeff_kottwitzReflexDeterminant
    (a : ι → A) (d : ι →₀ ℕ) :
    ((D.kottwitzReflexDeterminant C hΦ a).coeff d : ℂ) =
      (D.kottwitzHodgeDeterminant C a).coeff d := by
  change (D.kottwitzCocharacterReflexField C).val.toRingHom
    ((D.kottwitzReflexDeterminant C hΦ a).coeff d) = _
  exact PolynomialDescent.map_coeff_descend _ _ _ d

theorem kottwitzReflexDeterminant_unique (a : ι → A)
    (q : MvPolynomial ι (D.kottwitzCocharacterReflexField C))
    (hq : MvPolynomial.map (D.kottwitzCocharacterReflexField C).val.toRingHom q =
      D.kottwitzHodgeDeterminant C a) :
    q = D.kottwitzReflexDeterminant C hΦ a :=
  PolynomialDescent.unique _ Subtype.val_injective _ _ q hq

theorem kottwitzReflexDeterminant_isHomogeneous (a : ι → A) :
    (D.kottwitzReflexDeterminant C hΦ a).IsHomogeneous
      (Module.finrank ℂ (D.kottwitzHodgeModule C)) :=
  PolynomialDescent.descend_isHomogeneous _ Subtype.val_injective _ _
    (D.kottwitzHodgeDeterminant_isHomogeneous C a)

/-- Complex evaluation recovers the determinant on the actual Hodge module. -/
theorem eval₂_kottwitzReflexDeterminant (a : ι → A) (x : ι → ℂ) :
    MvPolynomial.eval₂ (D.kottwitzCocharacterReflexField C).val.toRingHom x
      (D.kottwitzReflexDeterminant C hΦ a) =
        LinearMap.det (D.kottwitzHodgeAction C
          (∑ i, x i • ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] a i)))) := by
  rw [← MvPolynomial.eval_map, map_kottwitzReflexDeterminant]
  exact D.eval_kottwitzHodgeDeterminant C a x

variable {R : Type*} [CommRing R]

/-- Change the coefficient ring along an arbitrary reflex-field ring map. -/
def kottwitzReflexDeterminantBaseChange (a : ι → A)
    (f : D.kottwitzCocharacterReflexField C →+* R) : MvPolynomial ι R :=
  MvPolynomial.map f (D.kottwitzReflexDeterminant C hΦ a)

@[simp] theorem coeff_kottwitzReflexDeterminantBaseChange (a : ι → A)
    (f : D.kottwitzCocharacterReflexField C →+* R) (d : ι →₀ ℕ) :
    (D.kottwitzReflexDeterminantBaseChange C hΦ a f).coeff d =
      f ((D.kottwitzReflexDeterminant C hΦ a).coeff d) :=
  MvPolynomial.coeff_map _ _ _

@[simp] theorem kottwitzReflexDeterminantBaseChange_id (a : ι → A) :
    D.kottwitzReflexDeterminantBaseChange C hΦ a (RingHom.id _) =
      D.kottwitzReflexDeterminant C hΦ a :=
  MvPolynomial.map_id _

@[simp] theorem kottwitzReflexDeterminantBaseChange_inclusion (a : ι → A) :
    D.kottwitzReflexDeterminantBaseChange C hΦ a
      (D.kottwitzCocharacterReflexField C).val.toRingHom =
        D.kottwitzHodgeDeterminant C a :=
  D.map_kottwitzReflexDeterminant C hΦ a

theorem kottwitzReflexDeterminantBaseChange_isHomogeneous (a : ι → A)
    (f : D.kottwitzCocharacterReflexField C →+* R) :
    (D.kottwitzReflexDeterminantBaseChange C hΦ a f).IsHomogeneous
      (Module.finrank ℂ (D.kottwitzHodgeModule C)) :=
  (D.kottwitzReflexDeterminant_isHomogeneous C hΦ a).map f

@[simp] theorem eval_kottwitzReflexDeterminantBaseChange (a : ι → A)
    (f : D.kottwitzCocharacterReflexField C →+* R) (x : ι → R) :
    MvPolynomial.eval x
      (D.kottwitzReflexDeterminantBaseChange C hΦ a f) =
        MvPolynomial.eval₂ f x (D.kottwitzReflexDeterminant C hΦ a) :=
  MvPolynomial.eval_map _ _ _

variable {S : Type*} [CommRing S]

@[simp] theorem map_kottwitzReflexDeterminantBaseChange (a : ι → A)
    (f : D.kottwitzCocharacterReflexField C →+* R) (g : R →+* S) :
    MvPolynomial.map g (D.kottwitzReflexDeterminantBaseChange C hΦ a f) =
      D.kottwitzReflexDeterminantBaseChange C hΦ a (g.comp f) :=
  MvPolynomial.map_map _ _ _

theorem map_eval_kottwitzReflexDeterminantBaseChange (a : ι → A)
    (f : D.kottwitzCocharacterReflexField C →+* R)
    (g : R →+* S) (x : ι → R) :
    g (MvPolynomial.eval x
      (D.kottwitzReflexDeterminantBaseChange C hΦ a f)) =
        MvPolynomial.eval (fun i => g (x i))
          (D.kottwitzReflexDeterminantBaseChange C hΦ a (g.comp f)) := by
  simp only [eval_kottwitzReflexDeterminantBaseChange]
  exact MvPolynomial.hom_eval₂ _ _ _ _

end Langlands.Shimura.CentralSimpleUnitaryData

import Langlands.Shimura.PEL.HarrisTaylorCMLieDeterminant

/-! # Extending the normalized Harris determinant from the order to the full algebra -/

noncomputable section

open CategoryTheory _root_.AlgebraicGeometry MvPolynomial
open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w t

namespace Langlands.Shimura.HodgeDeterminant

variable {R : Type u} [CommRing R] {ι : Type v}

/-- Substitute `r k * X k` for every variable, keeping all coefficients fixed. -/
def rescaleVariables (r : ι → R) : MvPolynomial ι R →+* MvPolynomial ι R :=
  eval₂Hom C (fun k => C (r k) * X k)

theorem map_rescaleVariables {T : Type w} [CommRing T] (f : R →+* T)
    (r : ι → R) (q : MvPolynomial ι R) :
    MvPolynomial.map f (rescaleVariables r q) =
      rescaleVariables (fun k => f (r k)) (MvPolynomial.map f q) := by
  change MvPolynomial.map f (eval₂ C (fun k => C (r k) * X k) q) =
    eval₂ C (fun k => C (f (r k)) * X k) (MvPolynomial.map f q)
  rw [MvPolynomial.map_eval₂]
  congr 1
  funext k
  change MvPolynomial.map f (C (r k) * X k) = C (f (r k)) * X k
  rw [(MvPolynomial.map f).map_mul, map_C, map_X]

/-- Unit diagonal substitutions can be cancelled over arbitrary commutative rings. -/
theorem rescaleVariables_injective (r : ι → R) (hr : ∀ k, IsUnit (r k)) :
    Function.Injective (rescaleVariables r) := by
  classical
  choose c hc using hr
  have hcomp :
      (rescaleVariables (fun k => ↑((c k)⁻¹))).comp (rescaleVariables r) =
        RingHom.id (MvPolynomial ι R) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rescaleVariables]
    · intro k
      simp only [RingHom.comp_apply, RingHom.id_apply, rescaleVariables,
        eval₂Hom_X', RingHom.map_mul, eval₂Hom_C, ← hc k]
      rw [← mul_assoc, ← C.map_mul, Units.mul_inv, C.map_one, one_mul]
  intro q q' h
  have := congrArg (rescaleVariables (fun k => ↑((c k)⁻¹))) h
  simpa only [← RingHom.comp_apply, hcomp, RingHom.id_apply] using this

variable {M : Type w} [AddCommGroup M] [Module R M]
    [Fintype ι] {κ : Type t} [Fintype κ] [DecidableEq κ]

/-- Scaling the actual family is exactly diagonal substitution in its determinant. -/
theorem polynomial_smul_family (b : Module.Basis κ R M)
    (f : ι → Module.End R M) (r : ι → R) :
    polynomial b (fun k => r k • f k) =
      rescaleVariables r (polynomial b f) := by
  unfold polynomial rescaleVariables
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro j k
  simp only [matrix, Matrix.map_apply, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X',
    map_smul, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem polynomial_zsmul_family (b : Module.Basis κ R M)
    (f : ι → Module.End R M) (m : ι → ℤ) :
    polynomial b (fun k => m k • f k) =
      rescaleVariables (fun k => (m k : R)) (polynomial b f) := by
  simpa only [Int.cast_smul_eq_zsmul] using
    polynomial_smul_family b f (fun k => (m k : R))

end Langlands.Shimura.HodgeDeterminant

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}} {R : CommRingCat.{u}} [Algebra ℚ R]
    (p : S ⟶ Spec R) (B : AbelianScheme S)
    {O : Type v} [Ring O] (α : O →+* End0 B)
    {ι : Type w} [Fintype ι] {U : S.Opens} {I : Type u} [Fintype I]

/-- Integer scaling of the actual rational Lie family rescales the same polynomial. -/
theorem lieRationalSectionDeterminant_zsmul_family
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → O) (m : ι → ℤ) (V : Over U) :
    lieRationalSectionDeterminant p B α e (fun k => m k • a k) V =
      Langlands.Shimura.HodgeDeterminant.rescaleVariables
        (fun k => (m k : Γ(S, V.left))) (lieRationalSectionDeterminant p B α e a V) := by
  classical
  rw [lieRationalSectionDeterminant_eq_basis p B α e _ V (localSectionBasis e V),
    lieRationalSectionDeterminant_eq_basis p B α e a V (localSectionBasis e V)]
  simp only [map_zsmul]
  exact Langlands.Shimura.HodgeDeterminant.polynomial_zsmul_family _ _ m

end Langlands.AbelianScheme

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra Langlands.AbelianScheme

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    {ι : Type} [Fintype ι]

/-- The actual regular Hodge determinant obeys the same integer rescaling law. -/
theorem kottwitzHodgeDeterminant_zsmul_family (a : ι → A) (m : ι → ℤ) :
    D.kottwitzHodgeDeterminant C (fun k => m k • a k) =
      HodgeDeterminant.rescaleVariables (fun k => (m k : ℂ))
        (D.kottwitzHodgeDeterminant C a) := by
  let : FiniteDimensional K A := D.finite
  let : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ K A
  let h := (D.realPositiveKottwitzHom C).val.hom
  let φ : A →+* ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A) :=
    (TensorProduct.includeRight :
      (ℝ ⊗[ℚ] A) →ₐ[ℝ] ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)).toRingHom.comp
      (TensorProduct.includeRight : A →ₐ[ℚ] ℝ ⊗[ℚ] A).toRingHom
  change HodgeDeterminant.polynomial (Module.finBasis ℂ (RegularHodge.submodule h))
      (fun k => RegularHodge.leftAction h (φ (m k • a k))) = _
  simp only [map_zsmul]
  exact HodgeDeterminant.polynomial_zsmul_family _ _ m

variable (hΦ : IsCMSection E K Φ)

/-- The rescaling identity descends to the actual reflex field. -/
theorem kottwitzReflexDeterminant_zsmul_family (a : ι → A) (m : ι → ℤ) :
    D.kottwitzReflexDeterminant C hΦ (fun k => m k • a k) =
      HodgeDeterminant.rescaleVariables
        (fun k => (m k : D.kottwitzCocharacterReflexField C))
        (D.kottwitzReflexDeterminant C hΦ a) := by
  apply MvPolynomial.map_injective
    (D.kottwitzCocharacterReflexField C).val.toRingHom Subtype.val_injective
  rw [D.map_kottwitzReflexDeterminant,
    HodgeDeterminant.map_rescaleVariables, D.map_kottwitzReflexDeterminant]
  simpa only [map_intCast] using D.kottwitzHodgeDeterminant_zsmul_family C a m

/-- Integer rescaling survives every coefficient map out of the reflex field. -/
theorem kottwitzReflexDeterminantBaseChange_zsmul_family
    {T : Type*} [CommRing T] (a : ι → A) (m : ι → ℤ)
    (f : D.kottwitzCocharacterReflexField C →+* T) :
    D.kottwitzReflexDeterminantBaseChange C hΦ (fun k => m k • a k) f =
      HodgeDeterminant.rescaleVariables (fun k => (m k : T))
        (D.kottwitzReflexDeterminantBaseChange C hΦ a f) := by
  unfold kottwitzReflexDeterminantBaseChange
  rw [D.kottwitzReflexDeterminant_zsmul_family C hΦ,
    HodgeDeterminant.map_rescaleVariables]
  simp only [map_intCast]

end Langlands.Shimura.CentralSimpleUnitaryData

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra Langlands.AbelianScheme

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)
    {ι : Type} [Fintype ι] {U : S.Opens} {I : Type} [Fintype I]

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

/-- The normalized determinant test for a family in the full rational algebra. -/
def HarrisTaylorCMFullAlgebraLieDeterminantConditionAt
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → A) (V : Over U) : Prop :=
  lieRationalSectionDeterminant p B i.toRingHom e a V =
    MvPolynomial.map (secHom p V.left).hom
      (D.kottwitzReflexDeterminantBaseChange C hΦ a
        (D.harrisTaylorReflexToCM C).toRingHom)

/-- Restricting the full-algebra test recovers the exact existing order-family test. -/
theorem harrisTaylorCMFullAlgebraLieDeterminantConditionAt_order
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → D.harrisHodgePELIntegralOrder C) (V : Over U) :
    D.HarrisTaylorCMFullAlgebraLieDeterminantConditionAt C p B i e
        (fun k => (a k : A)) V ↔
      D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e a V := Iff.rfl

/-- At the same chart and smaller open, testing every order family is equivalent to
testing every family in the full rational algebra. -/
theorem harrisTaylorCMFullAlgebraLieDeterminantConditionAt_iff_order_families
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (V : Over U) :
    (∀ a : ι → A,
      D.HarrisTaylorCMFullAlgebraLieDeterminantConditionAt C p B i e a V) ↔
    (∀ a : ι → D.harrisHodgePELIntegralOrder C,
      D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e a V) := by
  constructor
  · intro h a
    exact (D.harrisTaylorCMFullAlgebraLieDeterminantConditionAt_order C p B i e a V).mp
      (h (fun k => (a k : A)))
  · intro h a
    classical
    choose m hm ha using fun k => D.exists_int_multiple_mem_harrisHodgePELIntegralOrder C (a k)
    let c : ι → D.harrisHodgePELIntegralOrder C := fun k => ⟨m k • a k, ha k⟩
    have hscaled := h c
    change lieRationalSectionDeterminant p B i.toRingHom e (fun k => m k • a k) V =
      MvPolynomial.map (secHom p V.left).hom
        (D.kottwitzReflexDeterminantBaseChange C hΦ (fun k => m k • a k)
          (D.harrisTaylorReflexToCM C).toRingHom) at hscaled
    rw [lieRationalSectionDeterminant_zsmul_family,
      D.kottwitzReflexDeterminantBaseChange_zsmul_family,
      HodgeDeterminant.map_rescaleVariables] at hscaled
    simp only [map_intCast] at hscaled
    apply HodgeDeterminant.rescaleVariables_injective (fun k => (m k : Γ(S, V.left))) _ hscaled
    intro k
    have hmF : (m k : F) ≠ 0 := by exact_mod_cast hm k
    simpa only [map_intCast] using
      (isUnit_iff_ne_zero.mpr hmF).map (secHom p V.left).hom

/-- The full-algebra condition is equality of every coefficient in the actual section ring. -/
theorem harrisTaylorCMFullAlgebraLieDeterminantConditionAt_iff_coeff
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → A) (V : Over U) :
    D.HarrisTaylorCMFullAlgebraLieDeterminantConditionAt C p B i e a V ↔
      ∀ d : ι →₀ ℕ,
        (lieRationalSectionDeterminant p B i.toRingHom e a V).coeff d =
          (secHom p V.left).hom
            ((D.kottwitzReflexDeterminantBaseChange C hΦ a
              (D.harrisTaylorReflexToCM C).toRingHom).coeff d) := by
  simp only [HarrisTaylorCMFullAlgebraLieDeterminantConditionAt, MvPolynomial.ext_iff,
    MvPolynomial.coeff_map]

/-- The full-algebra test restricts along every actual inclusion of smaller opens. -/
theorem harrisTaylorCMFullAlgebraLieDeterminantConditionAt_restrict
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : ι → A) {V W : Over U} (j : V ⟶ W)
    (h : D.HarrisTaylorCMFullAlgebraLieDeterminantConditionAt C p B i e a W) :
    D.HarrisTaylorCMFullAlgebraLieDeterminantConditionAt C p B i e a V := by
  unfold HarrisTaylorCMFullAlgebraLieDeterminantConditionAt at h ⊢
  rw [← lieRationalSectionDeterminant_restrict p B i.toRingHom e a j, h,
    MvPolynomial.map_map]
  have hsec : (S.presheaf.map j.left.op).hom.comp (secHom p W.left).hom =
      (secHom p V.left).hom := by
    change (secHom p W.left ≫ S.presheaf.map j.left.op).hom = (secHom p V.left).hom
    have hj : j.left = homOfLE (leOfHom j.left) := Subsingleton.elim _ _
    rw [hj, secHom_map]
  rw [hsec]

/-- The same normalized test on every finite full-algebra family and finite Lie chart. -/
def HarrisTaylorCMFullAlgebraLieDeterminantCondition : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → A)
    (U : S.Opens) (I : Type) [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (V : Over U), D.HarrisTaylorCMFullAlgebraLieDeterminantConditionAt C p B i e a V

/-- Extending the families changes no global normalized determinant condition. -/
theorem harrisTaylorCMFullAlgebraLieDeterminantCondition_iff :
    D.HarrisTaylorCMFullAlgebraLieDeterminantCondition C p B i ↔
      D.HarrisTaylorCMRationalLieDeterminantCondition C p B i := by
  constructor
  · intro h ι _ a U I _ e V
    exact (D.harrisTaylorCMFullAlgebraLieDeterminantConditionAt_order C p B i e a V).mp
      (h ι (fun k => (a k : A)) U I e V)
  · intro h ι _ a U I _ e V
    exact (D.harrisTaylorCMFullAlgebraLieDeterminantConditionAt_iff_order_families
      C p B i e V).mpr (fun c => h ι c U I e V) a

/-- The full-algebra version is also equivalent to the original normalized reflex-base test. -/
theorem harrisTaylorCMFullAlgebraLieDeterminantCondition_iff_reflex :
    D.HarrisTaylorCMFullAlgebraLieDeterminantCondition C p B i ↔
      D.HarrisRationalLieDeterminantCondition C hΦ (D.harrisTaylorReflexStructure C p) B i :=
  (D.harrisTaylorCMFullAlgebraLieDeterminantCondition_iff C p B i).trans
    (D.harrisTaylorCMRationalLieDeterminantCondition_iff C p B i)

variable {B}

/-- Actual equivariant rational isomorphisms preserve the full-algebra condition. -/
theorem harrisTaylorCMFullAlgebraLieDeterminantCondition_iso
    {B' : AbelianScheme S} (i' : A →ₐ[ℚ] End0 B')
    (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
    (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a)) :
    D.HarrisTaylorCMFullAlgebraLieDeterminantCondition C p B i ↔
      D.HarrisTaylorCMFullAlgebraLieDeterminantCondition C p B' i' :=
  (D.harrisTaylorCMFullAlgebraLieDeterminantCondition_iff C p B i).trans
    ((D.harrisTaylorCMRationalLieDeterminantCondition_iso C p i i' e he).trans
      (D.harrisTaylorCMFullAlgebraLieDeterminantCondition_iff C p B' i').symm)

variable (B) [IsCMField F]

/-- The full-algebra condition yields the normalized central trace for every central
element, without a choice of an order element representing it. -/
theorem harrisTaylorCMFullAlgebraLieDeterminantConditionAt_centralCoefficient
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : F) (V : Over U)
    (h : D.HarrisTaylorCMFullAlgebraLieDeterminantConditionAt C p B i e
      ![1, algebraMap F A a] V) :
    HodgeDeterminant.traceCoefficient
      (lieRationalSectionDeterminant p B i.toRingHom e ![1, algebraMap F A a] V) =
      HarrisTaylor.lieTraceSection L p n a V.left := by
  change lieRationalSectionDeterminant p B i.toRingHom e
    ![1, algebraMap F A a] V = _ at h
  rw [h]
  exact D.traceCoefficient_harrisTaylorCentralDeterminant_section C p a V.left

end Langlands.Shimura.CentralSimpleUnitaryData

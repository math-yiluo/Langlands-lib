import Langlands.Shimura.PEL.HarrisTaylorCMArtinianMatrixDeterminant
import Langlands.Shimura.PEL.HarrisTaylorCMFullAlgebraDeterminant
import Langlands.Shimura.PEL.HarrisTaylorCMDeterminantLocality
import Mathlib.RingTheory.Smooth.Field

/-! # Reflection of the normalized determinant over local Artinian bases -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AbelianScheme Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

variable {A : Type} [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] [IsSimpleRing A]
  {F : Type} [Field F] [CharZero F]
  {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
  (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)
  {ι I : Type} [Fintype ι] [Fintype I] {U : S.Opens}
  (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
  (a : ι → A) (V : Over U)

/-- The entire Lie determinant polynomial is fixed by coefficient reduction followed
by a coefficient field section. -/
private theorem lieDeterminant_eq_section
    [IsLocalRing Γ(S, V.left)] {k : Type} [Field k] [CharZero k]
    (q : Γ(S, V.left) →+* k) (σ : k →+* Γ(S, V.left))
    (hσ : q.comp σ = RingHom.id k) :
    lieRationalSectionDeterminant p B i.toRingHom e a V =
      MvPolynomial.map (σ.comp q) (lieRationalSectionDeterminant p B i.toRingHom e a V) := by
  classical
  let : Algebra ℚ ↥Γ(S, V.left) :=
    ((secHom p V.left).hom.comp (algebraMap ℚ F)).toAlgebra
  let b := localSectionBasis e V
  let mat : Module.End Γ(S, V.left) Γ(B.Lie, V.left) →+* Matrix I I Γ(S, V.left) :=
    { toFun := LinearMap.toMatrix b b
      map_zero' := map_zero _
      map_one' := LinearMap.toMatrix_one b
      map_add' := map_add _
      map_mul' := LinearMap.toMatrix_mul b }
  let ρ : A →ₐ[ℚ] Matrix I I Γ(S, V.left) :=
    (mat.comp (lieRationalSectionOrderAction p B i.toRingHom V)).toRatAlgHom
  have hqσ : q.toRatAlgHom.comp σ.toRatAlgHom = AlgHom.id ℚ k := by
    ext x
    exact RingHom.congr_fun hσ x
  rw [lieRationalSectionDeterminant_eq_basis p B i.toRingHom e a V b,
    hodgeDeterminant_polynomial_eq_pencil]
  change (matrixPencil (fun l => ρ (a l))).det =
    MvPolynomial.map (σ.comp q) (matrixPencil (fun l => ρ (a l))).det
  exact matrixPencil_det_eq_section q.toRatAlgHom σ.toRatAlgHom hqσ ρ a

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra
open Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

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

private theorem secHom_spec_map_top {R S : CommRingCat.{0}} (f : R ⟶ S) :
    secHom (Spec.map f) ⊤ = f ≫ (Scheme.ΓSpecIso S).inv := by
  calc
    _ = (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop :=
      congrArg ((Scheme.ΓSpecIso R).inv ≫ ·) ((Spec.map f).appLE_eq_app (U := ⊤))
    _ = _ := (Scheme.ΓSpecIso_inv_naturality f).symm

variable {R k : Type} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    [Field k] [CharZero k]

/-- A compatible coefficient field detects the normalized Lie determinant on the
whole local Artinian base, including its nilpotent coefficients. -/
theorem harrisTaylorCMRationalLieDeterminantCondition_of_coefficientField
    (β : F →+* R) (q : R →+* k) (σ : k →+* R)
    (hσ : q.comp σ = RingHom.id k) (hβ : σ.comp (q.comp β) = β)
    (B : AbelianScheme (Spec (.of R))) (i : A →ₐ[ℚ] End0 B)
    (h : D.HarrisTaylorCMRationalLieDeterminantCondition C
      (Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom β))
      ((baseChange (Spec.map (CommRingCat.ofHom q))).obj B)
      ((rationalBaseChangeEnd (Spec.map (CommRingCat.ofHom q)) B).comp i)) :
    D.HarrisTaylorCMRationalLieDeterminantCondition C (Spec.map (CommRingCat.ofHom β)) B i := by
  let S := Spec (CommRingCat.of R)
  let T := Spec (CommRingCat.of k)
  let p : S ⟶ Spec (.of F) := Spec.map (CommRingCat.ofHom β)
  let b : T ⟶ S := Spec.map (CommRingCat.ofHom q)
  let : Subsingleton S := inferInstanceAs (Subsingleton (PrimeSpectrum R))
  let : FiniteDimensional F A := D.finite
  let : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ F A
  let : IsSimpleRing A := D.simple
  intro ι _ a U I _ e V
  obtain ⟨W, j, rfl⟩ := Over.mk_surjective V
  rcases TopologicalSpace.Opens.eq_bot_or_top W with hW | hW
  · subst W
    apply MvPolynomial.ext
    intro d
    let : Subsingleton ↥Γ(S, (Over.mk j).left) :=
      inferInstanceAs (Subsingleton ↥Γ(S, ⊥))
    exact Subsingleton.elim _ _
  · subst W
    let v : Over U := Over.mk j
    let qₛ : Γ(S, ⊤) ⟶ CommRingCat.of k := b.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom
    let σₛ : CommRingCat.of k ⟶ Γ(S, ⊤) :=
      CommRingCat.ofHom σ ≫ (Scheme.ΓSpecIso (.of R)).inv
    let : IsLocalRing ↥Γ(S, v.left) :=
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.isLocalRing
    have hqₛ : qₛ = (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom q :=
      Scheme.ΓSpecIso_naturality (CommRingCat.ofHom q)
    have hσₛ : qₛ.hom.comp σₛ.hom = RingHom.id k := by
      change (σₛ ≫ qₛ).hom = _
      rw [hqₛ]
      simp only [σₛ, Category.assoc, Iso.inv_hom_id_assoc, ← CommRingCat.ofHom_comp, hσ,
        CommRingCat.ofHom_id, CommRingCat.hom_id]
    have hp : (σₛ.hom.comp qₛ.hom).comp (secHom p ⊤).hom = (secHom p ⊤).hom := by
      change (secHom p ⊤ ≫ qₛ ≫ σₛ).hom = _
      rw [hqₛ, show secHom p ⊤ = _ from secHom_spec_map_top (CommRingCat.ofHom β)]
      have hβ' : (CommRingCat.ofHom β ≫ CommRingCat.ofHom q) ≫ CommRingCat.ofHom σ =
          CommRingCat.ofHom β := congrArg CommRingCat.ofHom hβ
      have key := congrArg (· ≫ (Scheme.ΓSpecIso (.of R)).inv) hβ'
      simpa only [σₛ, Category.assoc, Iso.inv_hom_id_assoc] using
        congrArg CommRingCat.Hom.hom key
    let a' : ι → A := fun l => (a l : A)
    let P := lieRationalSectionDeterminant p B i.toRingHom e a' v
    let Q := D.kottwitzReflexDeterminantBaseChange C
      (isCMSection_harrisCMSection E (algebraMap L F) τ₀) a'
      (D.harrisTaylorReflexToCM C).toRingHom
    let Qₛ := MvPolynomial.map (secHom p ⊤).hom Q
    have hmap : MvPolynomial.map b.appTop.hom P = MvPolynomial.map b.appTop.hom Qₛ := by
      have hb := h ι a (b ⁻¹ᵁ U) I (lieBaseChangeChart b B e)
        (Over.mk ((TopologicalSpace.Opens.map b.base).map j))
      unfold HarrisTaylorCMRationalLieDeterminantConditionAt at hb
      have hpull := lieRationalSectionDeterminant_baseChange_of_naturality p b B i.toRingHom
        (lieBaseChangeNaturalityStatements S).1 e a' v
      change MvPolynomial.map b.appTop.hom P = _ at hpull
      dsimp only [Qₛ]
      rw [hpull, MvPolynomial.map_map]
      have hsec := congrArg CommRingCat.Hom.hom (secHom_comp_app p b (⊤ : S.Opens))
      rw [CommRingCat.hom_comp] at hsec
      change b.appTop.hom.comp (secHom p ⊤).hom = _ at hsec
      rw [hsec]
      exact hb
    change P = Qₛ
    calc
      P = MvPolynomial.map (σₛ.hom.comp qₛ.hom) P :=
        lieDeterminant_eq_section p B i e a' v qₛ.hom σₛ.hom hσₛ
      _ = MvPolynomial.map (σₛ.hom.comp qₛ.hom) Qₛ := by
        simp only [qₛ, CommRingCat.hom_comp, ← MvPolynomial.map_map]
        rw [hmap]
      _ = Qₛ := by
        dsimp only [Qₛ]
        rw [MvPolynomial.map_map, hp]

open IsLocalRing

/-- The normalized Lie determinant on an Artinian lift is detected by its
actual restriction to any surjective local Artinian test. -/
def HarrisTaylorCMArtinianDeterminantReflectionStatement : Prop :=
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] [IsLocalRing R] [IsLocalRing R₀]
    [IsArtinianRing R] [IsArtinianRing R₀] (φ : R →+* R₀), Function.Surjective φ →
    ∀ (β : Spec (.of R) ⟶ Spec (.of F)) (B : AbelianScheme (Spec (.of R)))
      (i : A →ₐ[ℚ] End0 B),
      D.HarrisTaylorCMDeterminantPullbackCondition C β B i (Spec.map (CommRingCat.ofHom φ)) →
      D.HarrisTaylorCMRationalLieDeterminantCondition C β B i

/-- Reduce further to a field and split its residue map over the CM test base `F`. -/
theorem harrisTaylorCMArtinianDeterminantReflection :
    D.HarrisTaylorCMArtinianDeterminantReflectionStatement C := by
  intro R R₀ _ _ _ _ _ _ φ hφ β B i h
  let q : R →+* ResidueField R₀ := (residue R₀).comp φ
  let hq : Function.Surjective q := residue_surjective.comp hφ
  let β' : F →+* R := (Spec.preimage β).hom
  have hβ' : Spec.map (CommRingCat.ofHom β') = β := Spec.map_preimage β
  let : Algebra F R := β'.toAlgebra
  let : Algebra F (ResidueField R₀) := (q.comp β').toAlgebra
  let : Algebra ℚ (ResidueField R₀) := ((q.comp β').comp (algebraMap ℚ F)).toAlgebra
  let : CharZero (ResidueField R₀) := algebraRat.charZero _
  let qₐ : R →ₐ[F] ResidueField R₀ := ⟨q, fun _ => rfl⟩
  have hnil : IsNilpotent (RingHom.ker q) := by
    rw [ker_eq_maximalIdeal q hq]
    exact (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance
  have hsmooth : _root_.Algebra.FormallySmooth F (ResidueField R₀) := by
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (ResidueField R₀)
    let := hs.isAlgebraic_field
    exact _root_.Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
  let σ := _root_.Algebra.FormallySmooth.liftOfSurjective
    (AlgHom.id F (ResidueField R₀)) qₐ hq hnil
  have hσ : q.comp σ.toRingHom = RingHom.id (ResidueField R₀) := by
    ext x
    exact _root_.Algebra.FormallySmooth.liftOfSurjective_apply
      (AlgHom.id F (ResidueField R₀)) qₐ hq hnil x
  have hσβ : σ.toRingHom.comp (q.comp β') = β' := by
    ext x
    exact σ.commutes x
  have hqMap : Spec.map (CommRingCat.ofHom q) =
      Spec.map (CommRingCat.ofHom (residue R₀)) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hres := D.harrisTaylorCMDeterminantPullbackCondition_comp C β B i
    (Spec.map (CommRingCat.ofHom (residue R₀))) (Spec.map (CommRingCat.ofHom φ)) h
  rw [← hqMap, ← hβ'] at hres
  rw [← hβ']
  exact D.harrisTaylorCMRationalLieDeterminantCondition_of_coefficientField C β' q
    σ.toRingHom hσ hσβ B i ((D.harrisTaylorCMDeterminantPullbackCondition_iff
      C _ B i (Spec.map (CommRingCat.ofHom q))).mp hres)

end Langlands.Shimura.CentralSimpleUnitaryData

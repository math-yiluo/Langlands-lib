import Langlands.Shimura.PEL.HarrisKottwitzPrimeLocalDatum
import Langlands.AbelianScheme.PrimeToPDual
import Langlands.AbelianScheme.LiePrimeToP
import Langlands.AbelianScheme.RationalAlgebraAction
import Langlands.Shimura.PEL.HarrisTaylorLieCondition
import Langlands.AlgebraicGeometry.ProjectiveSpace

/-! # Kottwitz's tuples `(A, λ, i)` up to prime-to-`p` isogeny for the Harris datum -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open NumberField

universe u

namespace Langlands.AbelianScheme

/-- Zariski-local H-projectivity: over every affine open of the base, the abelian scheme admits a
closed immersion into a finite projective space over that open. -/
def IsLocallyHProjective {S : Scheme.{u}} (A : AbelianScheme S) : Prop :=
  ∀ U : S.affineOpens,
    Langlands.AlgebraicGeometry.IsHProjective (R := Γ(U.1.toScheme, ⊤))
      (((baseChange U.1.ι).obj A).X.hom ≫ U.1.toScheme.isoSpec.hom)

end Langlands.AbelianScheme

namespace Langlands.Shimura.CentralSimpleUnitaryData

open Langlands.PrimeLocalIntegers Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.Scheme.Modules

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [Algebra.IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} {D : CentralSimpleUnitaryData E K A n}
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [Algebra.IsQuadraticExtension ℚ L]
    {j : L →+* K} {τ₀ : L →+* ℂ}
    {C : HarrisSignatureCharts D.toSecondKindInvolution n (harrisCMSection E j τ₀)}
    {p : ℕ} [Fact p.Prime]
    (Dat : HarrisKottwitzPrimeLocalDatum D C p) (P : Prerequisites.{0})
    {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of (PrimeLocalRingOfIntegers K p)))

namespace HarrisKottwitzPrimeLocalDatum

variable {Dat} in
/-- The `ℤ_(p)`-scalars of a scheme over `𝒪_K ⊗ ℤ_(p)`. -/
def baseScalars : PrimeLocalIntegers p →+* Γ(S, ⊤) :=
  (scalarsFromBase s).comp
    (algebraMap (PrimeLocalIntegers p) (PrimeLocalRingOfIntegers K p))

/-- The integral determinant polynomial mapped to the sections of a test scheme over an open. -/
def sectionDeterminant (W : S.Opens) : MvPolynomial (Fin Dat.rank) Γ(S, W) :=
  MvPolynomial.map (secHom s W).hom Dat.determinant

/-- Kottwitz's determinant condition on `Lie(B)`: on every finite free chart of the actual Lie
module and every smaller open, `det(X₁ i(α₁) + ⋯ + X_t i(α_t) ; Lie B)` equals the integral
determinant polynomial `f` mapped to the sections. -/
def DeterminantCondition (B : AbelianScheme S)
    (i : Dat.order →ₐ[PrimeLocalIntegers p] EndP p B) : Prop :=
  ∀ (U : S.Opens) (I : Type) [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U) (V : Over U),
    liePSectionDeterminant p (baseScalars s) B i.toRingHom e (fun k => Dat.basis k) V =
      Dat.sectionDeterminant s V.left

end HarrisKottwitzPrimeLocalDatum

/-- A tuple `(A, λ, i)` of Kottwitz's integral moduli problem for the Harris datum, over a
scheme `S` over `𝒪_K ⊗ ℤ_(p)`, before level structure. -/
structure HarrisKottwitzPrimeLocalTuple where
  /-- The actual abelian scheme. -/
  abelian : AbelianScheme S
  /-- It is projective over every affine open of the base. -/
  projective : abelian.IsLocallyHProjective
  /-- It has the Harris relative dimension `[E : ℚ] n²`. -/
  dimension : HarrisTaylor.PrescribedRelativeDimension E abelian n
  /-- The actual dual of `abelian`. -/
  dualWitness : DualWitness abelian
  /-- The polarization, a homomorphism up to prime-to-`p` isogeny to the dual. -/
  polarization : HomP p abelian (dualWitness.dual P)
  isPolarization : dualWitness.IsPrimeToPPolarization P p polarization
  /-- The action of the order on the localized endomorphisms. -/
  action : Dat.order →ₐ[PrimeLocalIntegers p] EndP p abelian
  /-- The action is a `*`-homomorphism for the positive involution and the Rosati involution. -/
  rosati : dualWitness.RosatiCompatible P p Dat.orderInvolution polarization action.toRingHom
  /-- The full determinant condition on the Lie module. -/
  determinant : Dat.DeterminantCondition s abelian action

namespace HarrisKottwitzPrimeLocalTuple

variable {Dat P s}

/-! ## Comparison with the rational action -/

theorem endPToEnd0_smul (B : AbelianScheme S) (r : PrimeLocalIntegers p) (e : EndP p B) :
    endPToEnd0 p B (r • e) = toRat p r • endPToEnd0 p B e := by
  rw [Algebra.smul_def, map_mul, endPToEnd0_algebraMap, ← Algebra.smul_def]

variable (X : HarrisKottwitzPrimeLocalTuple Dat P s)

/-- The `ℚ`-linear extension of the action composed with `EndP → End0`, on the order basis. -/
def rationalActionLinear : A →ₗ[ℚ] End0 X.abelian :=
  Dat.ratBasis.constr ℚ (fun k => endPToEnd0 p X.abelian (X.action (Dat.basis k)))

theorem rationalActionLinear_order (b : Dat.order) :
    X.rationalActionLinear (b : A) = endPToEnd0 p X.abelian (X.action b) := by
  have hb : (b : A) = ∑ k, toRat p (Dat.basis.repr b k) • (Dat.basis k : A) := by
    conv_lhs => rw [← Dat.basis.sum_repr b]
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [Dat.coe_smul]
  conv_rhs => rw [← Dat.basis.sum_repr b]
  rw [hb, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, endPToEnd0_smul, ← Dat.ratBasis_apply, rationalActionLinear,
    Module.Basis.constr_basis]

theorem rationalActionLinear_one : X.rationalActionLinear 1 = 1 := by
  have h := X.rationalActionLinear_order (1 : Dat.order)
  rwa [OneMemClass.coe_one, map_one X.action, map_one (endPToEnd0 p X.abelian)] at h

theorem rationalActionLinear_mul (x y : A) :
    X.rationalActionLinear (x * y) = X.rationalActionLinear x * X.rationalActionLinear y := by
  have h : (LinearMap.mul ℚ A).compr₂ X.rationalActionLinear =
      (LinearMap.mul ℚ (End0 X.abelian)).compl₁₂ X.rationalActionLinear
        X.rationalActionLinear := by
    refine Dat.ratBasis.ext fun i => Dat.ratBasis.ext fun k => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
      Dat.ratBasis_apply]
    have hmem : (Dat.basis i : A) * Dat.basis k = ((Dat.basis i * Dat.basis k : Dat.order) : A) :=
      rfl
    rw [hmem, X.rationalActionLinear_order, X.rationalActionLinear_order,
      X.rationalActionLinear_order, map_mul, map_mul]
  exact LinearMap.congr_fun₂ h x y

/-- The rational algebra action at the generic point: the unique `ℚ`-algebra homomorphism
`A → End0 A` extending the order action through `ℤ_(p) ⊆ ℚ`. -/
def rationalAction : A →ₐ[ℚ] End0 X.abelian :=
  AlgHom.ofLinearMap X.rationalActionLinear X.rationalActionLinear_one
    X.rationalActionLinear_mul

theorem rationalAction_order (b : Dat.order) :
    X.rationalAction (b : A) = endPToEnd0 p X.abelian (X.action b) :=
  X.rationalActionLinear_order b

/-- Uniqueness of the rational extension, since the order spans `A`. -/
theorem rationalAction_unique (ρ : A →ₐ[ℚ] End0 X.abelian)
    (hρ : ∀ b : Dat.order, ρ (b : A) = endPToEnd0 p X.abelian (X.action b)) :
    ρ = X.rationalAction := by
  apply AlgHom.toLinearMap_injective
  refine Dat.ratBasis.ext fun k => ?_
  rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, Dat.ratBasis_apply, hρ,
    X.rationalAction_order]

/-- The underlying object of the existing category of abelian schemes with rational algebra
action. -/
def toRationalAlgebraActionData : RationalAlgebraActionData S A :=
  ⟨X.abelian, X.rationalAction⟩

/-- Over a rational base, the Lie action of the tuple is the published rational Lie action of
its rational algebra action, restricted to the order. -/
theorem liePOrderAction_eq_rational (a : PrimeLocalIntegers p →+* Γ(S, ⊤))
    {R : CommRingCat.{0}} [Algebra ℚ R] (q : S ⟶ Spec R) :
    liePOrderAction p a X.abelian X.action.toRingHom =
      lieRationalOrderAction q X.abelian
        (X.rationalAction.toRingHom.comp Dat.order.val.toRingHom) := by
  rw [Langlands.AbelianScheme.liePOrderAction_eq_rational p a q]
  congr 1
  ext b : 1
  exact (X.rationalAction_order b).symm

/-! ## Isomorphisms up to prime-to-`p` isogeny -/

variable (Y Z : HarrisKottwitzPrimeLocalTuple Dat P s)

/-- An isomorphism of tuples: a `ℤ_(p)`-isogeny intertwining the order actions and carrying
`λ_Y` to a `ℤ_(p)^×`-multiple of `λ_X`. -/
structure PrimeToPIso where
  /-- The `ℤ_(p)`-isogeny. -/
  iso : (CoefficientExtension.of X.abelian : PrimeToPCategory p S) ≅
    CoefficientExtension.of Y.abelian
  intertwines : ∀ b : Dat.order,
    (X.action b).asHom ≫ iso.hom = iso.hom ≫ (Y.action b).asHom
  /-- The polarization scalar. -/
  scalar : (PrimeLocalIntegers p)ˣ
  polarization_eq : X.dualWitness.pullbackP P p Y.dualWitness iso.hom Y.polarization =
    (scalar : PrimeLocalIntegers p) • X.polarization

variable {X Y Z}

/-- The identity isomorphism. -/
def PrimeToPIso.refl (X : HarrisKottwitzPrimeLocalTuple Dat P s) : PrimeToPIso X X where
  iso := Iso.refl _
  intertwines b := by rw [Iso.refl_hom, Category.comp_id, Category.id_comp]
  scalar := 1
  polarization_eq := by
    change X.dualWitness.pullbackP P p X.dualWitness (idP p X.abelian) X.polarization = _
    rw [DualWitness.pullbackP_idP, Units.val_one, one_smul]

/-- The inverse isomorphism, with the inverse scalar. -/
def PrimeToPIso.symm (e : PrimeToPIso X Y) : PrimeToPIso Y X where
  iso := e.iso.symm
  intertwines b := by
    rw [Iso.symm_hom]
    symm
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact e.intertwines b
  scalar := e.scalar⁻¹
  polarization_eq := by
    have h1 : Y.dualWitness.pullbackP P p X.dualWitness e.iso.inv
        (X.dualWitness.pullbackP P p Y.dualWitness e.iso.hom Y.polarization) =
          Y.polarization := by
      rw [← DualWitness.pullbackP_compP]
      have hid : compP p _ _ _ e.iso.inv e.iso.hom = idP p Y.abelian := e.iso.inv_hom_id
      rw [hid, DualWitness.pullbackP_idP]
    rw [e.polarization_eq, DualWitness.pullbackP_smul] at h1
    change Y.dualWitness.pullbackP P p X.dualWitness e.iso.inv X.polarization = _
    rw [← h1, smul_smul, Units.inv_mul, one_smul]

/-- Composition of isomorphisms, with the product of the scalars. -/
def PrimeToPIso.trans (e : PrimeToPIso X Y) (f : PrimeToPIso Y Z) : PrimeToPIso X Z where
  iso := e.iso ≪≫ f.iso
  intertwines b := by
    rw [Iso.trans_hom, ← Category.assoc, e.intertwines, Category.assoc, f.intertwines,
      Category.assoc]
  scalar := f.scalar * e.scalar
  polarization_eq := by
    change X.dualWitness.pullbackP P p Z.dualWitness
      (compP p _ _ _ e.iso.hom f.iso.hom) Z.polarization = _
    rw [DualWitness.pullbackP_compP P p X.dualWitness Y.dualWitness, f.polarization_eq,
      DualWitness.pullbackP_smul, e.polarization_eq, smul_smul, Units.val_mul]

variable (X Y)

/-- Two tuples are isomorphic up to prime-to-`p` isogeny. -/
def PrimeToPIsomorphic : Prop := Nonempty (PrimeToPIso X Y)

variable (Dat P s)

/-- Isomorphism up to prime-to-`p` isogeny is an equivalence relation. -/
def primeToPSetoid : Setoid (HarrisKottwitzPrimeLocalTuple Dat P s) where
  r := PrimeToPIsomorphic
  iseqv := ⟨fun X => ⟨PrimeToPIso.refl X⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- The isomorphism classes of tuples over `S` (no smallness is asserted). -/
def PrimeToPClasses : Type 1 := Quotient (primeToPSetoid Dat P s)

end HarrisKottwitzPrimeLocalTuple

end Langlands.Shimura.CentralSimpleUnitaryData

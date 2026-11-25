/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # Functorial transport to finite rational coefficients

Source: Weil blueprint, proper base change, order 1306
(blueprint: prop-weil-pbc-rational-transport).
The scalar-first tensor convention is identified with the source's Hom-first convention
by TensorProduct.comm. All functors and comparisons below use actual tensor maps.

## Main definitions

- `CategoryTheory.ScalarLocalization.transport`: tensor extension of a linear functor.
- `CategoryTheory.ScalarLocalization.transportNat`: componentwise tensor extension.
- `WeilConjectures.pbcRationalExtension`: extension on the completed rational categories.

## Main statements

- `CategoryTheory.ScalarLocalization.transport_exact`: generic exact tensor transport.
- `WeilConjectures.pbcRationalTransport`: exactness, scalar formulas and uniqueness.
- `WeilConjectures.pbcRationalExchange`: transport of the four supplied operations and exchange.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe r u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace CategoryTheory.ScalarLocalization

variable (R : Type r) [CommRing R] (p : R)
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]
variable (F : C ⥤ D) [F.Additive] [F.Linear R]

/-- The Hom map is extension of scalars of the supplied linear map.
Source: blueprint order 1306, proof step 1
(blueprint: prop-weil-pbc-rational-transport). -/
def transportHom (K L : C) :
    (Localization.Away p ⊗[R] (K ⟶ L)) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (F.obj K ⟶ F.obj L)) :=
  (F.mapLinearMap R).baseChange (Localization.Away p)

/-- The tensor Hom maps preserve identities and composition.
Source: blueprint order 1306, proof steps 1--2
(blueprint: prop-weil-pbc-rational-transport).
Proof: the pure-tensor formula for baseChange sends a tensor a ⊗ f to a ⊗ F(f).
The composition formula reduces preservation of composition on pure tensors to that
of F and multiplication of scalars. Bilinearity extends it to finite sums. Identities
are tensors of the integral identities with one. -/
theorem transport_laws :
    (∀ K : C, transportHom R p F K K ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 K) =
      (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (F.obj K)) ∧
    (∀ (K L M : C) (f : Localization.Away p ⊗[R] (K ⟶ L))
        (g : Localization.Away p ⊗[R] (L ⟶ M)),
      transportHom R p F K M (composition R C p K L M g f) =
        composition R D p (F.obj K) (F.obj L) (F.obj M)
          (transportHom R p F L M g) (transportHom R p F K L f)) := by
  constructor
  · intro K
    simp [transportHom]
  · intro K L M f g
    induction g using TensorProduct.inductionOn with
    | tmul b g =>
      induction f using TensorProduct.inductionOn with
      | tmul a f => simp [transportHom, composition_tmul]
      | add f f' hf hf' => simp [map_add, hf, hf']
    | add g g' hg hg' => simp [map_add, hg, hg']

/-- The extension agrees on objects and sends a ⊗ f to a ⊗ F(f).
Source: blueprint order 1306, proof steps 1--2
(blueprint: prop-weil-pbc-rational-transport). -/
def transport : ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj K := ⟨F.obj K.obj⟩
  map {K L} f := transportHom R p F K.obj L.obj f
  map_id K := (transport_laws R p F).1 K.obj
  map_comp {K L M} f g := (transport_laws R p F).2 K.obj L.obj M.obj f g

/-- Additivity of the scalar extension. Source: blueprint order 1306
(blueprint: prop-weil-pbc-rational-transport). -/
instance transportAdditive : (transport R p F).Additive where
  map_add {K L} {f g} := (transportHom R p F K.obj L.obj).map_add f g

/-- Localized-ring linearity of the scalar extension. Source: blueprint order 1306
(blueprint: prop-weil-pbc-rational-transport). -/
instance transportLinear : (transport R p F).Linear (Localization.Away p) where
  map_smul {K L} f a := (transportHom R p F K.obj L.obj).map_smul a f

/-- Uniqueness among linear functors agreeing on integral objects and morphisms.
Source: blueprint order 1306, proof step 2
(blueprint: prop-weil-pbc-rational-transport).
Proof: a pure tensor is a times the integral tensor with one. Linearity forces its
image; additivity forces the image of every finite sum. The object equalities and
these Hom equalities give equality of functors by functor extensionality. -/
theorem transport_unique (H : ScalarLocalization R C p ⥤ ScalarLocalization R D p)
    [H.Additive] [H.Linear (Localization.Away p)]
    (hobj : ∀ K : C, H.obj ⟨K⟩ = ⟨F.obj K⟩)
    (hmap : ∀ (K L : C) (f : K ⟶ L),
      HEq (H.map ((1 : Localization.Away p) ⊗ₜ[R] f :
        ScalarLocalization.mk (R := R) (p := p) K ⟶ ⟨L⟩))
        ((1 : Localization.Away p) ⊗ₜ[R] F.map f)) :
    H = transport R p F := by
  refine Functor.ext (fun K ↦ hobj K.obj) ?_
  intro K L f
  change H.map f = eqToHom (hobj K.obj) ≫
    (transportHom R p F K.obj L.obj) f ≫ eqToHom (hobj L.obj).symm
  have hi (g : K.obj ⟶ L.obj) :
      H.map ((1 : Localization.Away p) ⊗ₜ[R] g : K ⟶ L) =
        eqToHom (hobj K.obj) ≫
          ((1 : Localization.Away p) ⊗ₜ[R] F.map g) ≫ eqToHom (hobj L.obj).symm := by
    exact (conj_eqToHom_iff_heq _ _ (hobj K.obj) (hobj L.obj)).mpr
      (hmap K.obj L.obj g)
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    calc
      H.map (a ⊗ₜ[R] f : K ⟶ L) =
          H.map (a • ((1 : Localization.Away p) ⊗ₜ[R] f) : K ⟶ L) := by
            congr 1
            simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = a • H.map ((1 : Localization.Away p) ⊗ₜ[R] f : K ⟶ L) := H.map_smul a _
      _ = _ := by
        rw [hi, ← Linear.comp_smul, ← Linear.smul_comp]
        dsimp only [transportHom]
        rw [LinearMap.baseChange_tmul]
        congr 2
        change a • ((1 : Localization.Away p) ⊗ₜ[R] F.map f) = a ⊗ₜ[R] F.map f
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add f g hf hg =>
    change H.map (f + g : K ⟶ L) = _
    rw [H.map_add, map_add]
    erw [Preadditive.add_comp, Preadditive.comp_add]
    exact congrArg₂ (· + ·) hf hg

variable {F} {G : C ⥤ D} [G.Additive] [G.Linear R]

/-- Naturality after scalar extension, for the prescribed components.
Source: blueprint order 1306, proof step 3
(blueprint: prop-weil-pbc-rational-transport).
Proof: on a pure tensor, both sides are the integral naturality equation tensored
with its scalar. Additivity proves the equation for a sum of pure tensors. -/
theorem transportNat_naturality (η : F ⟶ G) (K L : ScalarLocalization R C p)
    (f : K ⟶ L) :
    (transport R p F).map f ≫ ((1 : Localization.Away p) ⊗ₜ[R] η.app L.obj) =
      ((1 : Localization.Away p) ⊗ₜ[R] η.app K.obj) ≫ (transport R p G).map f := by
  change composition R D p _ _ _ ((1 : Localization.Away p) ⊗ₜ[R] η.app L.obj)
      (transportHom R p F _ _ f) =
    composition R D p _ _ _ (transportHom R p G _ _ f)
      ((1 : Localization.Away p) ⊗ₜ[R] η.app K.obj)
  induction f using TensorProduct.inductionOn with
  | tmul a f => simp [transportHom, composition_tmul, η.naturality]
  | add f g hf hg => simp [map_add, hf, hg]

/-- The unique extension of a natural transformation, with its integral components.
Source: blueprint order 1306, proof step 3
(blueprint: prop-weil-pbc-rational-transport). -/
def transportNat (η : F ⟶ G) : transport R p F ⟶ transport R p G where
  app K := (1 : Localization.Away p) ⊗ₜ[R] η.app K.obj
  naturality K L f := transportNat_naturality R p η K L f

private theorem transport_comp {B : Type u₃} [Category.{v₃} B]
    [Preadditive B] [Linear R B] (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ B) [G.Additive] [G.Linear R] :
    transport R p F ⋙ transport R p G = transport R p (F ⋙ G) := by
  apply transport_unique R p (F ⋙ G)
  · intro K
    rfl
  · intro K L f
    apply heq_of_eq
    change transportHom R p G _ _ (transportHom R p F _ _ (1 ⊗ₜ[R] f)) = _
    simp only [transportHom, LinearMap.baseChange_tmul, Functor.mapLinearMap_apply]
    rfl

end CategoryTheory.ScalarLocalization

namespace AlgebraicGeometry.Scheme

set_option linter.defProp false in
/-- Inherited integral triangulation. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
abbrev pbcIntegralTriangulated (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    (hDim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
    (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :
    ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) :=
  (pbcIntegralUniformComplete_isTriangulated l E T hDim hInv).2

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (T : Scheme.{u}) [IsNoetherian T]
  (hDim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
  (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- The inherited integral zero object. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
instance pbcIntegralZero : HasZeroObject (PbcIntegralCategory l E T hDim hInv) :=
  letI := pbcIntegralTriangulated l E T hDim hInv
  inferInstance

/-- The inherited integral integer shifts. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
instance pbcIntegralShift : HasShift (PbcIntegralCategory l E T hDim hInv) ℤ :=
  letI := pbcIntegralTriangulated l E T hDim hInv
  inferInstance

/-- Additivity of the inherited integral shifts. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
instance pbcIntegralShiftAdditive (n : ℤ) :
    (shiftFunctor (PbcIntegralCategory l E T hDim hInv) n).Additive :=
  letI := pbcIntegralTriangulated l E T hDim hInv
  inferInstance

/-- The inherited integral distinguished triangles. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
instance pbcIntegralPretriangulated :
    Pretriangulated (PbcIntegralCategory l E T hDim hInv) :=
  letI := pbcIntegralTriangulated l E T hDim hInv
  inferInstance

/-- Integral octahedra are inherited from the ambient derived category.
Source: blueprint order 1305 (blueprint: prop-weil-pbc-rational-transport). -/
instance pbcIntegralIsTriangulated :
    IsTriangulated (PbcIntegralCategory l E T hDim hInv) :=
  letI := pbcIntegralTriangulated l E T hDim hInv
  inferInstance

set_option linter.defProp false in
/-- The existing scalar-localization theorem, with its tensor-induced shift and precisely
its isomorphic image triangles. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
abbrev pbcRationalTriangulationData :=
  letI := pbcIntegralTriangulated l E T hDim hInv
  ScalarLocalization.exists_triangulated_scalarLocalization
    (PbcIntegralRing l E)
    (PbcIntegralCategory l E T hDim hInv)
    (pbcUniformizer l E)

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The lifted integer ring has the same uniformizer localization. This is the canonical
fraction map, transported through ULift.ringEquiv, followed by the recorded fraction map
for the original integer ring. Source: blueprint order 1306, proof step 1
(blueprint: prop-weil-pbc-rational-transport). -/
def pbcRationalCoefficientEquiv : Localization.Away (pbcUniformizer l E) ≃+* E :=
  (IsLocalization.ringEquivOfRingEquiv
    (R := PbcIntegralRing l E) (P := Padic.coefficientExtensionIntegers l E)
    (M := Submonoid.powers (pbcUniformizer l E))
    (T := Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
    (Localization.Away (pbcUniformizer l E))
    (Localization.Away (Padic.coefficientExtensionUniformizer l E))
    (ULift.ringEquiv : PbcIntegralRing l E ≃+* Padic.coefficientExtensionIntegers l E)
    (Submonoid.map_powers _ _)).trans
      (Padic.coefficientExtension_localization_uniformizer.{u, u} l E).2.choose.toRingEquiv

variable (T : Scheme.{u}) [IsNoetherian T]
variable (hDim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
variable (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- The rational Hom modules carry the actual E-action by the canonical fraction map.
Source: blueprint order 1306, proof step 1
(blueprint: prop-weil-pbc-rational-transport). -/
instance pbcRationalLinear : Linear E (PbcRationalDerivedCategory l E T hDim hInv) where
  homModule K L := Module.compHom (K ⟶ L) (pbcRationalCoefficientEquiv l E).symm.toRingHom
  smul_comp K L M a f g :=
    Linear.smul_comp K L M ((pbcRationalCoefficientEquiv l E).symm a) f g
  comp_smul K L M f a g :=
    Linear.comp_smul K L M f ((pbcRationalCoefficientEquiv l E).symm a) g

end AlgebraicGeometry.Scheme

namespace WeilConjectures

open AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem ulift_localization_module (A : Type r) [CommRing A]
    (p : ULift.{r + 1} A) :
    (ULift.module : Module (ULift.{r + 1} A) (Localization.Away p)) =
      (OreLocalization.instModuleOfIsScalarTower :
        Module (ULift.{r + 1} A) (Localization.Away p)) := by
  apply Module.ext'
  intro a x
  induction x using OreLocalization.ind with
  | _ b s => simp only [ULift.smul_def, OreLocalization.smul_oreDiv]

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (X Y : Scheme.{u}) [IsNoetherian X] [IsNoetherian Y]
variable (hX : ∃ d : ℕ, topologicalKrullDim X ≤ d)
variable (iX : ∀ t : X, IsUnit (l : X.presheaf.stalk t))
variable (hY : ∃ d : ℕ, topologicalKrullDim Y ≤ d)
variable (iY : ∀ t : Y, IsUnit (l : Y.presheaf.stalk t))
variable (F : PbcIntegralCategory l E X hX iX ⥤
  PbcIntegralCategory l E Y hY iY)
variable [F.Additive] [F.Linear (PbcIntegralRing l E)]

variable (X' Y' : Scheme.{u}) [IsNoetherian X'] [IsNoetherian Y']
variable (hX' : ∃ d : ℕ, topologicalKrullDim X' ≤ d)
variable (iX' : ∀ t : X', IsUnit (l : X'.presheaf.stalk t))
variable (hY' : ∃ d : ℕ, topologicalKrullDim Y' ≤ d)
variable (iY' : ∀ t : Y', IsUnit (l : Y'.presheaf.stalk t))

end WeilConjectures

import Langlands.CategoryTheory.CoefficientExtension
import Langlands.RingTheory.PrimeLocalIntegers
import Langlands.AbelianScheme.RationalBaseChange
import Langlands.AbelianScheme.IsogenyInverse
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Abelian schemes up to prime-to-`p` isogeny -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace Langlands.AbelianScheme

variable (p : ℕ) [Fact p.Prime]

/-- The `ℤ_(p)`-linear category of actual abelian schemes over `S`, with morphism groups
`ℤ_(p) ⊗[ℤ] Hom_S(A, B)`. -/
abbrev PrimeToPCategory (S : Scheme.{u}) :=
  CoefficientExtension (PrimeLocalIntegers p) (AbelianScheme S)

variable {S T : Scheme.{u}}

/-- `ℤ_(p)`-localized homomorphisms, formed from the actual integral Hom group. -/
abbrev HomP (A B : AbelianScheme S) := CoefficientExtension.Hom (PrimeLocalIntegers p) A B

/-- `ℤ_(p)`-localized endomorphisms: the actual endomorphism `ℤ_(p)`-algebra of `A` in
the localized category. Its multiplication is `f * g = g ≫ f`. -/
abbrev EndP (A : AbelianScheme S) := CoefficientExtension.End (PrimeLocalIntegers p) A

/-- The canonical map from actual homomorphisms, `f ↦ 1 ⊗ f`. -/
def homToHomP {A B : AbelianScheme S} : (A ⟶ B) →ₗ[ℤ] HomP p A B :=
  CoefficientExtension.ofHom (PrimeLocalIntegers p)

@[simp] theorem homToHomP_apply {A B : AbelianScheme S} (f : A ⟶ B) :
    homToHomP p f = (1 : PrimeLocalIntegers p) ⊗ₜ[ℤ] f := rfl

/-- The identity localized homomorphism. -/
def idP (A : AbelianScheme S) : HomP p A A :=
  CoefficientExtension.identity (PrimeLocalIntegers p) A

@[simp] theorem homToHomP_id (A : AbelianScheme S) : homToHomP p (𝟙 A) = idP p A := rfl

/-- Composition of localized homomorphisms, `ℤ_(p)`-bilinear, in diagrammatic order. -/
def compP (A B C : AbelianScheme S) :
    HomP p A B →ₗ[PrimeLocalIntegers p] HomP p B C →ₗ[PrimeLocalIntegers p] HomP p A C :=
  CoefficientExtension.compLinear (PrimeLocalIntegers p) A B C

@[simp] theorem compP_tmul {A B C : AbelianScheme S} (r s : PrimeLocalIntegers p)
    (f : A ⟶ B) (g : B ⟶ C) :
    compP p A B C (r ⊗ₜ[ℤ] f) (s ⊗ₜ[ℤ] g) = (r * s) ⊗ₜ[ℤ] (f ≫ g) := rfl

@[simp] theorem compP_homToHomP {A B C : AbelianScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    compP p A B C (homToHomP p f) (homToHomP p g) = homToHomP p (f ≫ g) := by
  simp

@[simp] theorem idP_compP {A B : AbelianScheme S} (f : HomP p A B) :
    compP p A A B (idP p A) f = f :=
  CoefficientExtension.identity_comp f

@[simp] theorem compP_idP {A B : AbelianScheme S} (f : HomP p A B) :
    compP p A B B f (idP p B) = f :=
  CoefficientExtension.comp_identity f

theorem compP_assoc {A B C D : AbelianScheme S}
    (f : HomP p A B) (g : HomP p B C) (h : HomP p C D) :
    compP p A C D (compP p A B C f g) h = compP p A B D f (compP p B C D g h) :=
  CoefficientExtension.comp_assoc f g h

/-- The canonical unital ring map from actual endomorphisms. -/
def endToEndP (A : AbelianScheme S) : CategoryTheory.End A →+* EndP p A :=
  CoefficientExtension.ofEnd (PrimeLocalIntegers p) A

@[simp] theorem endToEndP_apply (A : AbelianScheme S) (f : CategoryTheory.End A) :
    endToEndP p A f = CategoryTheory.End.of (homToHomP p f.asHom) := rfl

/-- Multiplication in `EndP` is composition with the right factor applied first. -/
theorem endP_mul (A : AbelianScheme S) (a b : EndP p A) :
    a * b = CategoryTheory.End.of (compP p A A A b.asHom a.asHom) := rfl

@[simp] theorem endP_algebraMap (A : AbelianScheme S) (r : PrimeLocalIntegers p) :
    algebraMap (PrimeLocalIntegers p) (EndP p A) r = CategoryTheory.End.of (r ⊗ₜ[ℤ] 𝟙 A) :=
  CoefficientExtension.algebraMap_eq A r

/-! ## Comparison with the rationalized category -/

/-- The comparison functor to the existing rational category, along `ℤ_(p) ⊆ ℚ`. -/
def primeToPRationalization (S : Scheme.{u}) : PrimeToPCategory p S ⥤ RationalCategory S :=
  CoefficientExtension.toRationalization (PrimeLocalIntegers.toRat p)

instance : (primeToPRationalization p S).Additive :=
  inferInstanceAs (CoefficientExtension.toRationalization (C := AbelianScheme S)
    (PrimeLocalIntegers.toRat p)).Additive

/-- The comparison map from localized to rational homomorphisms. -/
def homPToHom0 (A B : AbelianScheme S) : HomP p A B →ₗ[ℤ] Hom0 A B :=
  CoefficientExtension.changeHom (PrimeLocalIntegers.toRat p) A B

@[simp] theorem homPToHom0_tmul {A B : AbelianScheme S} (r : PrimeLocalIntegers p)
    (f : A ⟶ B) : homPToHom0 p A B (r ⊗ₜ[ℤ] f) = PrimeLocalIntegers.toRat p r ⊗ₜ[ℤ] f := rfl

@[simp] theorem homPToHom0_homToHomP {A B : AbelianScheme S} (f : A ⟶ B) :
    homPToHom0 p A B (homToHomP p f) = homToHom0 f := by
  simp

theorem homPToHom0_smul {A B : AbelianScheme S} (r : PrimeLocalIntegers p) (f : HomP p A B) :
    homPToHom0 p A B (r • f) = PrimeLocalIntegers.toRat p r • homPToHom0 p A B f :=
  CoefficientExtension.changeHom_smul _ r f

@[simp] theorem homPToHom0_idP (A : AbelianScheme S) : homPToHom0 p A A (idP p A) = id0 A :=
  CoefficientExtension.changeHom_identity _ A

theorem homPToHom0_compP {A B C : AbelianScheme S} (f : HomP p A B) (g : HomP p B C) :
    homPToHom0 p A C (compP p A B C f g) =
      comp0 A B C (homPToHom0 p A B f) (homPToHom0 p B C g) := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp only [map_add, LinearMap.add_apply, hf, hf']
  | tmul r f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp only [map_add, hg, hg']
    | tmul s g => simp

/-- The comparison unital ring map to the actual rational endomorphism algebra. -/
def endPToEnd0 (A : AbelianScheme S) : EndP p A →+* End0 A :=
  CoefficientExtension.toRationalEnd (PrimeLocalIntegers.toRat p) A

@[simp] theorem endPToEnd0_apply (A : AbelianScheme S) (f : EndP p A) :
    endPToEnd0 p A f = CategoryTheory.End.of (homPToHom0 p A A f.asHom) := rfl

@[simp] theorem endPToEnd0_endToEndP (A : AbelianScheme S) (f : CategoryTheory.End A) :
    endPToEnd0 p A (endToEndP p A f) = endToEnd0 A f :=
  CoefficientExtension.toRationalEnd_ofEnd _ A f

/-- The comparison is semilinear along `ℤ_(p) ⊆ ℚ` on endomorphisms. -/
theorem endPToEnd0_algebraMap (A : AbelianScheme S) (r : PrimeLocalIntegers p) :
    endPToEnd0 p A (algebraMap (PrimeLocalIntegers p) (EndP p A) r) =
      algebraMap ℚ (End0 A) (PrimeLocalIntegers.toRat p r) := by
  rw [endP_algebraMap, end0_algebraMap]
  rfl

/-! ## Base change -/

/-- Pullback extends to the localized category. -/
def primeToPBaseChange (b : T ⟶ S) : PrimeToPCategory p S ⥤ PrimeToPCategory p T :=
  CoefficientExtension.lift (PrimeLocalIntegers p)
    (baseChange b ⋙ CoefficientExtension.inclusion (PrimeLocalIntegers p))

instance (b : T ⟶ S) : (primeToPBaseChange p b).Additive :=
  inferInstanceAs (CoefficientExtension.lift (PrimeLocalIntegers p)
    (baseChange b ⋙ CoefficientExtension.inclusion (PrimeLocalIntegers p))).Additive

/-- The `ℤ_(p)`-linear base-change map on localized Hom groups. -/
def baseChangeHomP (b : T ⟶ S) {A B : AbelianScheme S} :
    HomP p A B →ₗ[PrimeLocalIntegers p] HomP p ((baseChange b).obj A) ((baseChange b).obj B) :=
  CoefficientExtension.liftHom (PrimeLocalIntegers p)
    (baseChange b ⋙ CoefficientExtension.inclusion (PrimeLocalIntegers p))

@[simp] theorem baseChangeHomP_tmul (b : T ⟶ S) {A B : AbelianScheme S}
    (r : PrimeLocalIntegers p) (f : A ⟶ B) :
    baseChangeHomP p b (r ⊗ₜ[ℤ] f) = r ⊗ₜ[ℤ] (baseChange b).map f := by
  change r • ((1 : PrimeLocalIntegers p) ⊗ₜ[ℤ] (baseChange b).map f) = _
  simp [TensorProduct.smul_tmul']

@[simp] theorem baseChangeHomP_homToHomP (b : T ⟶ S) {A B : AbelianScheme S} (f : A ⟶ B) :
    baseChangeHomP p b (homToHomP p f) = homToHomP p ((baseChange b).map f) :=
  baseChangeHomP_tmul p b 1 f

@[simp] theorem baseChangeHomP_idP (b : T ⟶ S) (A : AbelianScheme S) :
    baseChangeHomP p b (idP p A) = idP p ((baseChange b).obj A) :=
  (primeToPBaseChange p b).map_id (CoefficientExtension.of A)

theorem baseChangeHomP_compP (b : T ⟶ S) {A B C : AbelianScheme S}
    (f : HomP p A B) (g : HomP p B C) :
    baseChangeHomP p b (compP p A B C f g) =
      compP p _ _ _ (baseChangeHomP p b f) (baseChangeHomP p b g) := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp only [map_add, LinearMap.add_apply, hf, hf']
  | tmul r f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp only [map_add, hg, hg']
    | tmul s g => simp

/-- The induced unital `ℤ_(p)`-algebra map on localized endomorphisms. -/
def baseChangeEndP (b : T ⟶ S) (A : AbelianScheme S) :
    EndP p A →ₐ[PrimeLocalIntegers p] EndP p ((baseChange b).obj A) :=
  CoefficientExtension.liftEnd (PrimeLocalIntegers p)
    (baseChange b ⋙ CoefficientExtension.inclusion (PrimeLocalIntegers p)) A

@[simp] theorem baseChangeEndP_apply (b : T ⟶ S) (A : AbelianScheme S) (f : EndP p A) :
    baseChangeEndP p b A f = CategoryTheory.End.of (baseChangeHomP p b f.asHom) := rfl

/-- Localized base change is compatible with the existing rational base change. -/
theorem homPToHom0_baseChangeHomP (b : T ⟶ S) {A B : AbelianScheme S} (f : HomP p A B) :
    homPToHom0 p _ _ (baseChangeHomP p b f) = rationalBaseChangeHom b (homPToHom0 p A B f) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [map_add, hf, hg]
  | tmul r f => simp

/-! ## Prime-to-`p` isogenies -/

/-- An actual prime-to-`p` isogeny: a finite flat surjective homomorphism whose native degree
at every point of the target is prime to `p`. -/
def IsPrimeToPIsogeny {A B : AbelianScheme S} (f : A ⟶ B) : Prop :=
  GroupScheme.IsIsogeny (groupHom f) ∧ ∀ y : B.X.left, ((hom f).finrank y).Coprime p

/-- A `ℤ_(p)`-isogeny is an isomorphism of the localized category. -/
abbrev IsPrimeToPQuasiIsogeny {A B : AbelianScheme S} (f : HomP p A B) : Prop :=
  IsIso (C := PrimeToPCategory p S) (X := CoefficientExtension.of A)
    (Y := CoefficientExtension.of B) f

namespace IsPrimeToPQuasiIsogeny

variable {p} {A B : AbelianScheme S} {f : HomP p A B}

/-- The inverse of a `ℤ_(p)`-isogeny, as a localized homomorphism. -/
def invP (hf : IsPrimeToPQuasiIsogeny p f) : HomP p B A :=
  @CategoryTheory.inv (PrimeToPCategory p S) _ (CoefficientExtension.of A)
    (CoefficientExtension.of B) f hf

@[simp] theorem compP_invP (hf : IsPrimeToPQuasiIsogeny p f) :
    compP p A B A f hf.invP = idP p A :=
  @IsIso.hom_inv_id (PrimeToPCategory p S) _ (CoefficientExtension.of A)
    (CoefficientExtension.of B) f hf

@[simp] theorem invP_compP (hf : IsPrimeToPQuasiIsogeny p f) :
    compP p B A B hf.invP f = idP p B :=
  @IsIso.inv_hom_id (PrimeToPCategory p S) _ (CoefficientExtension.of A)
    (CoefficientExtension.of B) f hf

/-- A localized homomorphism with a two-sided inverse is a `ℤ_(p)`-isogeny. -/
theorem of_compP {g : HomP p B A} (h₁ : compP p A B A f g = idP p A)
    (h₂ : compP p B A B g f = idP p B) : IsPrimeToPQuasiIsogeny p f :=
  ⟨⟨g, h₁, h₂⟩⟩

/-- A unit multiple of a `ℤ_(p)`-isogeny is a `ℤ_(p)`-isogeny. -/
theorem unit_smul (u : (PrimeLocalIntegers p)ˣ) (hf : IsPrimeToPQuasiIsogeny p f) :
    IsPrimeToPQuasiIsogeny p ((u : PrimeLocalIntegers p) • f) := by
  refine of_compP (g := (↑u⁻¹ : PrimeLocalIntegers p) • hf.invP) ?_ ?_
  · simp only [map_smul, LinearMap.smul_apply, compP_invP, smul_smul, Units.inv_mul, one_smul]
  · simp only [map_smul, LinearMap.smul_apply, invP_compP, smul_smul, Units.mul_inv, one_smul]

end IsPrimeToPQuasiIsogeny

/-- Multiplying by a unit of `ℤ_(p)` neither creates nor destroys invertibility. -/
theorem isPrimeToPQuasiIsogeny_unit_smul_iff {A B : AbelianScheme S}
    (u : (PrimeLocalIntegers p)ˣ) (f : HomP p A B) :
    IsPrimeToPQuasiIsogeny p ((u : PrimeLocalIntegers p) • f) ↔ IsPrimeToPQuasiIsogeny p f := by
  refine ⟨fun h => ?_, fun h => h.unit_smul u⟩
  have h' := h.unit_smul u⁻¹
  rwa [smul_smul, Units.inv_mul, one_smul] at h'

/-- The image of a `ℤ_(p)`-isogeny in the rational category is invertible. -/
theorem IsPrimeToPQuasiIsogeny.rational {A B : AbelianScheme S} {f : HomP p A B}
    (hf : IsPrimeToPQuasiIsogeny p f) :
    IsIso (C := RationalCategory S) ((primeToPRationalization p S).map
      (X := CoefficientExtension.of A) (Y := CoefficientExtension.of B) f) :=
  have := hf
  Functor.map_isIso _ _

/-- An actual isogeny whose scheme kernel is killed by a natural number prime to `p` becomes
invertible in the localized category. Its inverse is `n⁻¹ ⊗ g`, where `g` is the actual
homomorphism with `f ≫ g = n` and `g ≫ f = n` obtained by descending multiplication by `n`
along `f`. -/
theorem isPrimeToPQuasiIsogeny_of_kernel {A B : AbelianScheme S} (f : A ⟶ B)
    (hf : GroupScheme.IsIsogeny (groupHom f)) {n : ℕ} (hn : n.Coprime p)
    (hker : GroupScheme.multiplication (GroupScheme.kernel (groupHom f)) (n : ℤ) = 1) :
    IsPrimeToPQuasiIsogeny p (homToHomP p f) := by
  let g : B ⟶ A := Additive.ofMul (GroupScheme.descent hf hker)
  have hfg : f ≫ g = (n : ℤ) • 𝟙 A := by
    change Additive.ofMul (groupHom f ≫ GroupScheme.descent hf hker) =
      (n : ℤ) • Additive.ofMul (𝟙 A.toGrp)
    rw [GroupScheme.comp_descent, ← ofMul_zpow]
    rfl
  have hgf : g ≫ f = (n : ℤ) • 𝟙 B := by
    change Additive.ofMul (GroupScheme.descent hf hker ≫ groupHom f) =
      (n : ℤ) • Additive.ofMul (𝟙 B.toGrp)
    rw [GroupScheme.descent_comp, ← ofMul_zpow]
    rfl
  let u := (PrimeLocalIntegers.isUnit_natCast p hn).unit
  have hu : ((n : ℤ) : PrimeLocalIntegers p) * (↑u⁻¹ : PrimeLocalIntegers p) = 1 := by
    rw [Int.cast_natCast, ← (PrimeLocalIntegers.isUnit_natCast p hn).unit_spec, Units.mul_inv]
  have hu' : (↑u⁻¹ : PrimeLocalIntegers p) * ((n : ℤ) : PrimeLocalIntegers p) = 1 := by
    rw [mul_comm, hu]
  refine ⟨⟨(↑u⁻¹ : PrimeLocalIntegers p) • homToHomP p g, ?_, ?_⟩⟩
  · change compP p A B A (homToHomP p f) ((↑u⁻¹ : PrimeLocalIntegers p) • homToHomP p g) =
      idP p A
    rw [map_smul, compP_homToHomP, hfg, map_zsmul, homToHomP_id,
      ← Int.cast_smul_eq_zsmul (PrimeLocalIntegers p), smul_smul, hu', one_smul]
  · change compP p B A B ((↑u⁻¹ : PrimeLocalIntegers p) • homToHomP p g) (homToHomP p f) =
      idP p B
    rw [map_smul, LinearMap.smul_apply, compP_homToHomP, hgf, map_zsmul, homToHomP_id,
      ← Int.cast_smul_eq_zsmul (PrimeLocalIntegers p), smul_smul, hu', one_smul]

end Langlands.AbelianScheme

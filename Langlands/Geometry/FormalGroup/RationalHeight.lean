import Langlands.Geometry.FormalGroup.LocalQuasiIsogeny

/-! # Rational height presentations from actual kernel ranks -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

namespace Hom

/-- Coherent restriction preserves the actual constant kernel-rank height. -/
theorem HasHeight.algebraMapLinear {A B : CommAlgCat.{v} R}
    {f : Hom (M.overAlgebra A) (N.overAlgebra A)} {q h : ℕ}
    (hf : f.HasHeight q h) (φ : A ⟶ B) :
    (Hom.algebraMapLinear φ f).HasHeight q h := by
  apply hasHeight_of_isoSquare (f.map (coefficientAlgHom φ))
    (Hom.algebraMapLinear φ f) (M.overAlgebraIso φ) (N.overAlgebraIso φ)
  · change ((N.overAlgebraIso φ).hom.comp
      ((f.map (coefficientAlgHom φ)).comp (M.overAlgebraIso φ).inv)).comp
      (M.overAlgebraIso φ).hom = _
    rw [Hom.comp_assoc, Hom.comp_assoc, Iso.inv_hom, Hom.comp_id]
  · exact hf.map (coefficientAlgHom φ)

@[simp]
theorem algebraMapLinear_scalarHom {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (a : O) :
    Hom.algebraMapLinear φ ((M.overAlgebra A).scalarHom a) =
      (M.overAlgebra B).scalarHom a := by
  change Hom.algebraMapLinear φ (a • Hom.id (M.overAlgebra A)) =
    a • Hom.id (M.overAlgebra B)
  rw [map_smul, algebraMapLinear_hom_id]

end Hom

namespace RationalSection

/-- An actual scalar-denominator presentation with constant ranks for both
the numerator kernel and the scalar-power kernel on the source. -/
structure HeightPresentation (π : O) (q : ℕ) {U : Opens (PrimeSpectrum R)}
    (z : RationalSection F M N U) where
  exponent : ℕ
  representative : OpenIntegralHom M N U
  numeratorHeight : ℕ
  denominatorHeight : ℕ
  numerator : representative.HasHeight q numeratorHeight
  denominator :
    ((M.overAlgebra ((coefficientStructurePresheaf R).obj (op U))).scalarHom
      (π ^ exponent)).HasHeight q denominatorHeight
  represents : (algebraMap O F π) ^ exponent • z = ofIntegral U representative

namespace HeightPresentation

variable {π : O} {q : ℕ} {U V : Opens (PrimeSpectrum R)}
variable {z : RationalSection F M N U}

/-- The signed height formula: numerator kernel height minus scalar kernel height. -/
def index (P : HeightPresentation π q z) : ℤ :=
  (P.numeratorHeight : ℤ) - (P.denominatorHeight : ℤ)

@[simp]
theorem index_cast {w : RationalSection F M N U} (e : z = w)
    (P : HeightPresentation π q z) : (e ▸ P).index = P.index := by
  subst w
  rfl

/-- Restriction keeps the same rank exponents, using actual kernel base change. -/
def restrict (P : HeightPresentation π q z) (i : V ⟶ U) :
    HeightPresentation π q (RationalSection.restrict i z) where
  exponent := P.exponent
  representative := Hom.algebraMapLinear ((coefficientStructurePresheaf R).map i.op)
    P.representative
  numeratorHeight := P.numeratorHeight
  denominatorHeight := P.denominatorHeight
  numerator := P.numerator.algebraMapLinear _
  denominator := by
    have h := P.denominator.algebraMapLinear ((coefficientStructurePresheaf R).map i.op)
    simpa only [Hom.algebraMapLinear_scalarHom] using h
  represents := by
    have h := congrArg (RationalSection.restrict i) P.represents
    simpa only [map_smul, restrict_ofIntegral] using h

@[simp]
theorem index_restrict (P : HeightPresentation π q z) (i : V ⟶ U) :
    (P.restrict i).index = P.index := rfl

end HeightPresentation

/-- A height function is locally given by the signed difference of two actual
constant kernel-rank exponents in a scalar-denominator presentation. -/
def HasHeightFunction (π : O) (q : ℕ) {U : Opens (PrimeSpectrum R)}
    (z : RationalSection F M N U) (h : U → ℤ) : Prop :=
  ∀ x : U,
    ∃ (V : Opens (PrimeSpectrum R)) (_hx : (x : PrimeSpectrum R) ∈ V) (i : V ⟶ U)
      (P : HeightPresentation π q (restrict i z)),
      ∀ y : V, h ⟨y, (leOfHom i) y.property⟩ = P.index

namespace HasHeightFunction

variable {π : O} {q : ℕ} {U V : Opens (PrimeSpectrum R)}
variable {z : RationalSection F M N U} {h : U → ℤ}

/-- The local rank formula itself implies local constancy of the height function. -/
theorem isLocallyConstant (hh : HasHeightFunction π q z h) : IsLocallyConstant h := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨W, hxW, i, P, hP⟩ := hh x
  refine ⟨{y : U | (y : PrimeSpectrum R) ∈ W},
    W.isOpen.preimage continuous_subtype_val, hxW, ?_⟩
  intro y hy
  exact (hP ⟨y, hy⟩).trans (hP ⟨x, hxW⟩).symm

/-- A height presentation at every point also supplies the local isogeny condition. -/
theorem isLocallyScalarIsogeny (hh : HasHeightFunction π q z h) :
    IsLocallyScalarIsogeny π z := by
  intro x hx
  obtain ⟨W, hxW, i, P, _⟩ := hh ⟨x, hx⟩
  exact ⟨W, hxW, i, P.exponent, P.representative, P.numerator.1, P.represents⟩

/-- Restrict a height function and its local actual-rank presentations. -/
theorem restrict (hh : HasHeightFunction π q z h) (i : V ⟶ U) :
    HasHeightFunction π q (RationalSection.restrict i z)
      (fun x : V => h ⟨x, (leOfHom i) x.property⟩) := by
  intro x
  obtain ⟨W, hxW, j, P, hP⟩ := hh ⟨x, (leOfHom i) x.property⟩
  let a : W ⊓ V ⟶ W := homOfLE inf_le_left
  let b : W ⊓ V ⟶ V := homOfLE inf_le_right
  have heq : RationalSection.restrict a (RationalSection.restrict j z) =
      RationalSection.restrict b (RationalSection.restrict i z) := by
    rw [← restrict_comp, ← restrict_comp]
    congr 1
  refine ⟨W ⊓ V, ⟨hxW, x.property⟩, b, heq ▸ P.restrict a, ?_⟩
  intro y
  change h ⟨y, _⟩ = (heq ▸ P.restrict a).index
  rw [HeightPresentation.index_cast, HeightPresentation.index_restrict]
  exact hP ⟨y, y.property.1⟩

/-- Regard a verified height function as an actual locally constant map. -/
def locallyConstant (hh : HasHeightFunction π q z h) : LocallyConstant U ℤ :=
  ⟨h, hh.isLocallyConstant⟩

end HasHeightFunction

end RationalSection

end Langlands.FormalGroup.ModuleLaw

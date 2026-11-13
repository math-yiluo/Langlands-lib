import Langlands.Geometry.FormalGroup.RationalHomSheaf
import Langlands.Geometry.FormalGroup.IsogenyBaseChange

/-! # Rational sections locally given by scalar multiples of isogenies -/

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

/-- Coherent coefficient restriction preserves the actual isogeny condition. -/
theorem IsIsogeny.algebraMapLinear {A B : CommAlgCat.{v} R}
    {f : Hom (M.overAlgebra A) (N.overAlgebra A)} (hf : f.IsIsogeny)
    (φ : A ⟶ B) : (Hom.algebraMapLinear φ f).IsIsogeny := by
  apply isIsogeny_of_isoSquare (f.map (coefficientAlgHom φ))
    (Hom.algebraMapLinear φ f) (M.overAlgebraIso φ) (N.overAlgebraIso φ)
  · change ((N.overAlgebraIso φ).hom.comp
      ((f.map (coefficientAlgHom φ)).comp (M.overAlgebraIso φ).inv)).comp
      (M.overAlgebraIso φ).hom = _
    rw [Hom.comp_assoc, Hom.comp_assoc, Iso.inv_hom, Hom.comp_id]
  · exact hf.map (coefficientAlgHom φ)

end Hom

/-- Actual integral formal Hom over the section algebra of an open set. -/
abbrev OpenIntegralHom (M : ModuleLaw O R σ) (N : ModuleLaw O R τ)
    (U : Opens (PrimeSpectrum R)) :=
  Hom (M.overAlgebra ((coefficientStructurePresheaf R).obj (op U)))
    (N.overAlgebra ((coefficientStructurePresheaf R).obj (op U)))

/-- The integral formal map regarded as a section of the rational Hom sheaf. -/
def RationalSection.ofIntegral (U : Opens (PrimeSpectrum R))
    (f : OpenIntegralHom M N U) : RationalSection F M N U :=
  ofRational U (RationalHom.ofHom f)

theorem RationalSection.restrict_ofIntegral {U V : Opens (PrimeSpectrum R)}
    (i : V ⟶ U) (f : OpenIntegralHom M N U) :
    restrict i (ofIntegral U f : RationalSection F M N U) =
      ofIntegral V (Hom.algebraMapLinear ((coefficientStructurePresheaf R).map i.op) f) := by
  have h := RationalSection.restrict_ofRational (F := F) (M := M) (N := N)
    i (RationalHom.ofHom f)
  change RationalSection.restrict i (ofRational U (RationalHom.ofHom f)) = _
  rw [h]
  change ofRational V (RationalHom.algebraMapLinear
    ((coefficientStructurePresheaf R).map i.op) (RationalHom.ofHom f)) = _
  rw [RationalHom.algebraMapLinear_ofHom]
  rfl

/-- At each point, a power of π times the section is an integral isogeny
on a Zariski neighbourhood. The denominator may depend on the point. -/
def RationalSection.IsLocallyScalarIsogeny (π : O) {U : Opens (PrimeSpectrum R)}
    (z : RationalSection F M N U) : Prop :=
  ∀ x : PrimeSpectrum R, x ∈ U →
    ∃ (V : Opens (PrimeSpectrum R)) (_hx : x ∈ V) (i : V ⟶ U)
      (n : ℕ) (f : OpenIntegralHom M N V),
      f.IsIsogeny ∧
        (algebraMap O F π) ^ n • restrict i z = ofIntegral V f

namespace RationalSection.IsLocallyScalarIsogeny

variable {π : O} {U V : Opens (PrimeSpectrum R)}
variable {z : RationalSection F M N U}

/-- Intersect a witnessing neighbourhood with the smaller open and restrict
the actual integral isogeny along its structure-algebra map. -/
theorem restrict (hz : IsLocallyScalarIsogeny π z) (i : V ⟶ U) :
    IsLocallyScalarIsogeny π (RationalSection.restrict i z) := by
  intro x hx
  obtain ⟨W, hxW, j, n, f, hf, heq⟩ := hz x ((leOfHom i) hx)
  let a : W ⊓ V ⟶ W := homOfLE inf_le_left
  let b : W ⊓ V ⟶ V := homOfLE inf_le_right
  refine ⟨W ⊓ V, ⟨hxW, hx⟩, b, n,
    Hom.algebraMapLinear ((coefficientStructurePresheaf R).map a.op) f,
    hf.algebraMapLinear _, ?_⟩
  have h := congrArg (RationalSection.restrict a) heq
  have hi : b ≫ i = a ≫ j := Subsingleton.elim _ _
  simpa only [map_smul, restrict_ofIntegral, ← restrict_comp, hi] using h

/-- The condition is local for any open cover, without a uniform denominator. -/
theorem of_cover {ι : Type*} (V : ι → Opens (PrimeSpectrum R))
    (i : ∀ a, V a ⟶ U) (hcover : ∀ x ∈ U, ∃ a, x ∈ V a)
    (hz : ∀ a, IsLocallyScalarIsogeny π (RationalSection.restrict (i a) z)) :
    IsLocallyScalarIsogeny π z := by
  intro x hx
  obtain ⟨a, hxa⟩ := hcover x hx
  obtain ⟨W, hxW, j, n, f, hf, heq⟩ := hz a x hxa
  exact ⟨W, hxW, j ≫ i a, n, f, hf, by
    simpa only [restrict_comp] using heq⟩

/-- An actual integral isogeny supplies a section with exponent zero. -/
theorem ofIntegral (f : OpenIntegralHom M N U) (hf : f.IsIsogeny) :
    IsLocallyScalarIsogeny π (RationalSection.ofIntegral U f : RationalSection F M N U) := by
  intro x hx
  exact ⟨U, hx, 𝟙 U, 0, f, hf, by simp⟩

end RationalSection.IsLocallyScalarIsogeny

/-- Quasi-isogenies in the local rational-sheaf sense for globally coordinated
π-divisible formal modules. These retain the actual geometric hypotheses. -/
structure LocalQuasiIsogeny (F : Type v) [Field F] [Algebra O F] (π : O)
    (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) (U : Opens (PrimeSpectrum R)) where
  scalar_ne_zero : algebraMap O F π ≠ 0
  source_divisible : M.IsPiDivisible π
  target_divisible : N.IsPiDivisible π
  val : RationalSection F M N U
  isLocal : RationalSection.IsLocallyScalarIsogeny π val

namespace LocalQuasiIsogeny

variable {π : O} {U V : Opens (PrimeSpectrum R)}

/-- Restriction of a local quasi-isogeny, with no chosen inverse or denominator. -/
def restrict (z : LocalQuasiIsogeny F π M N U) (i : V ⟶ U) :
    LocalQuasiIsogeny F π M N V where
  scalar_ne_zero := z.scalar_ne_zero
  source_divisible := z.source_divisible
  target_divisible := z.target_divisible
  val := RationalSection.restrict i z.val
  isLocal := z.isLocal.restrict i

@[ext]
theorem ext (z w : LocalQuasiIsogeny F π M N U) (h : z.val = w.val) : z = w := by
  cases z
  cases w
  cases h
  rfl

@[simp]
theorem restrict_id (z : LocalQuasiIsogeny F π M N U) : z.restrict (𝟙 U) = z := by
  apply ext
  exact RationalSection.restrict_id U z.val

@[simp]
theorem restrict_comp {W : Opens (PrimeSpectrum R)} (z : LocalQuasiIsogeny F π M N U)
    (i : V ⟶ U) (j : W ⟶ V) : z.restrict (j ≫ i) = (z.restrict i).restrict j := by
  apply ext
  exact RationalSection.restrict_comp i j z.val

end LocalQuasiIsogeny

end Langlands.FormalGroup.ModuleLaw

import Langlands.AlgebraicGeometry.AlgebraicSpace.QuasiAffineSourceAFNoetherianSchemeApproximationStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SaturatedAffineOpensRepresentation
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-! # Skeleton of the approximation proof -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.QuasiAffineApproximation

open AlgebraicSpace AlgebraicSpace.SaturatedAffineOpensRepresentation EtaleEquivalenceRelation

/-- Part I: a presentation of the finite quasi-affine cover. -/
def PresentationInterface : Prop :=
  ∀ (R : Type u) [CommRing R] (U : Over (Spec (CommRingCat.of R)))
    (Y : AlgebraicSpace (Spec (CommRingCat.of R))) (f : (schemeToSpace _).obj U ⟶ Y),
    IsQuasiCompact Y → IsQuasiSeparated Y → U.left.IsQuasiAffine →
      AlgebraicSpace.IsFinite (hom f) → IsSurjective (hom f) →
        ∃ (E E' : EtaleEquivalenceRelation.{u}) (φ : E'.U ⟶ E.U) (g : E'.R ⟶ E.R)
          (q : E'.U ⟶ U.left),
          IsAffine E.U ∧ IsCartesianHom E' E φ g ∧ _root_.AlgebraicGeometry.IsFinite φ ∧
            Surjective φ ∧ IsPullback E'.t E'.s q q ∧ Flat q ∧
            LocallyOfFinitePresentation q ∧ Surjective q ∧
            ∀ w w', SameImage (hom f) w w' → ∃ ω ω', q ω = w ∧ q ω' = w' ∧ φ ω = φ ω'

/-- Part II: Noetherian approximation of a presentation with a finite cover with
quasi-affine quotient. -/
def ApproximationInterface : Prop :=
  ∀ (E E' : EtaleEquivalenceRelation.{u}) (φ : E'.U ⟶ E.U) (g : E'.R ⟶ E.R)
    (M : Scheme.{u}) (q : E'.U ⟶ M),
    IsAffine E.U → IsCartesianHom E' E φ g → _root_.AlgebraicGeometry.IsFinite φ →
      Surjective φ → M.IsQuasiAffine → IsPullback E'.t E'.s q q → Flat q →
        LocallyOfFinitePresentation q → Surjective q →
      ∃ (E₁ E₁' : EtaleEquivalenceRelation.{u}) (φ₁ : E₁'.U ⟶ E₁.U) (g₁ : E₁'.R ⟶ E₁.R)
        (M₁ : Scheme.{u}) (q₁ : E₁'.U ⟶ M₁) (hV : E.U ⟶ E₁.U) (hW : E'.U ⟶ E₁'.U)
        (hM : M ⟶ M₁),
        IsAffine E₁.U ∧ IsAffine E₁.R ∧ IsCartesianHom E₁' E₁ φ₁ g₁ ∧
          _root_.AlgebraicGeometry.IsFinite φ₁ ∧ Surjective φ₁ ∧ M₁.IsQuasiAffine ∧
          IsNoetherian M₁ ∧ IsPullback E₁'.t E₁'.s q₁ q₁ ∧ Flat q₁ ∧
          LocallyOfFinitePresentation q₁ ∧ Surjective q₁ ∧
          hW ≫ φ₁ = φ ≫ hV ∧ q ≫ hM = hW ≫ q₁ ∧ IsAffineHom hM

/-- Part III: the quotient space of a Noetherian level and the Noetherian case. -/
def QuotientInterface : Prop :=
  NoetherianSchemeQuasiAffineSourceAFStatement.{u} →
  ∀ (E₁ E₁' : EtaleEquivalenceRelation.{u}) (φ₁ : E₁'.U ⟶ E₁.U) (g₁ : E₁'.R ⟶ E₁.R)
    (M₁ : Scheme.{u}) (q₁ : E₁'.U ⟶ M₁),
    IsAffine E₁.U → IsAffine E₁.R → IsCartesianHom E₁' E₁ φ₁ g₁ →
      _root_.AlgebraicGeometry.IsFinite φ₁ → Surjective φ₁ → M₁.IsQuasiAffine →
      IsNoetherian M₁ → IsPullback E₁'.t E₁'.s q₁ q₁ → Flat q₁ →
      LocallyOfFinitePresentation q₁ → Surjective q₁ →
      ∃ (P : Scheme.{u}) (ψ : M₁ ⟶ P) (ψV : E₁.U ⟶ P),
        PointTopology.HasFiniteAffineNeighborhoods P ∧ IsAffineHom ψ ∧ q₁ ≫ ψ = φ₁ ≫ ψV

/-- An affine map to an AF scheme that is constant on points with the same image gives
saturated affine neighborhoods. -/
theorem hasSaturatedAffineNeighborhoods_of_affineHom {S : Scheme.{u}} {W : Over S}
    {Y : AlgebraicSpace S} (g : (schemeYoneda S).obj W ⟶ Y.presheaf) {P : Scheme.{u}}
    (hP : PointTopology.HasFiniteAffineNeighborhoods P) (φ : W.left ⟶ P) [IsAffineHom φ]
    (hφ : ∀ w w', SameImage g w w' → φ w = φ w') :
    HasSaturatedAffineNeighborhoods g := by
  intro F hF
  obtain ⟨A, hA⟩ := hP (φ '' F) (hF.image _)
  refine ⟨φ ⁻¹ᵁ A.1, A.2.preimage φ, fun w hw => hA ⟨w, hw, rfl⟩, ?_⟩
  intro w w' h hw
  change φ w' ∈ A.1
  rw [← hφ w w' h]
  exact hw

theorem approximation_of_interfaces (hI : PresentationInterface.{u})
    (hII : ApproximationInterface.{u}) (hIII : QuotientInterface.{u}) :
    QuasiAffineSourceAFNoetherianSchemeApproximationStatement.{u} := by
  intro hN R _ U Y f hqc hqs hqa hfin hsurj
  obtain ⟨E, E', φ, g, q, hEU, hcart, hφf, hφs, hpb, hfl, hlfp, hqs', hsame⟩ :=
    hI R U Y f hqc hqs hqa hfin hsurj
  obtain ⟨E₁, E₁', φ₁, g₁, M₁, q₁, hV, hW, hM, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    hc1, hc2, hMaff⟩ := hII E E' φ g U.left q hEU hcart hφf hφs hqa hpb hfl hlfp hqs'
  obtain ⟨P, ψ, ψV, hP, hψ, hc3⟩ :=
    hIII hN E₁ E₁' φ₁ g₁ M₁ q₁ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have hcomp : IsAffineHom (hM ≫ ψ) := inferInstance
  refine exists_AF_representation_of_saturated_affine_opens (hom f) hfin hsurj
    (hasSaturatedAffineNeighborhoods_of_affineHom (hom f) hP (hM ≫ ψ) ?_)
  intro w w' h
  obtain ⟨ω, ω', rfl, rfl, hωω'⟩ := hsame w w' h
  have key : ∀ x, (hM ≫ ψ) (q x) = (hV ≫ ψV) (φ x) := by
    intro x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Category.assoc, hc2,
      Category.assoc, hc3, ← Category.assoc, hc1, Category.assoc]
  rw [key, key, hωω']

end Langlands.AlgebraicGeometry.QuasiAffineApproximation

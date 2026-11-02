import Langlands.AlgebraicGeometry.Units.FiniteAlgebraDeterminant

/-! # Actual universal units of the finite-algebra determinant-open candidate -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.FiniteAlgebraUnits

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- The commutative-group-valued form of the actual unit presheaf. -/
abbrev groupPresheaf (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    (Over (base k))ᵒᵖ ⥤ CommGrpCat.{u} :=
  RelativeGlobalUnits.groupPresheaf (algebraSchemeMap k A)

@[simp]
lemma presheaf_obj (T : Over (base k)) :
    (presheaf k A).obj (op T) =
      ULift.{u + 1} (Γ(pullback T.hom (algebraSchemeMap k A), ⊤)ˣ) := rfl

@[simp]
lemma presheaf_restriction {T U : Over (base k)} (h : T ⟶ U)
    (a : (presheaf k A).obj (op U)) :
    ((presheaf k A).map h.op a).down =
      _root_.Units.map
        ((Picard.relativeSpace (algebraSchemeMap k A)).map h).appTop.hom.toMonoidHom
        a.down := rfl

variable {n : ℕ} (b : Module.Basis (Fin n) k A)

/-- The actual fibre product of the candidate and `Spec A`. -/
abbrev candidateFibre : Scheme.{u} :=
  (Picard.relativeSpace (algebraSchemeMap k A)).obj (candidate b)

/-- The canonical affine tensor-product comparison, with the candidate ring
as the first tensor factor. -/
def fibreSpecIso :
    candidateFibre b ≅ Spec (CommRingCat.of (candidateRing b ⊗[k] A)) :=
  pullbackSpecIso k (candidateRing b) A

/-- The comparison identifies the first projection with tensor inclusion. -/
lemma fibreSpecIso_hom_fst :
    (fibreSpecIso b).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (candidateRing b) (candidateRing b ⊗[k] A))) =
      pullback.fst (candidate b).hom (algebraSchemeMap k A) :=
  pullbackSpecIso_hom_fst' k (candidateRing b) A

/-- The comparison identifies the second projection with tensor inclusion. -/
lemma fibreSpecIso_hom_snd :
    (fibreSpecIso b).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : A →ₐ[k] candidateRing b ⊗[k] A).toRingHom) =
      pullback.snd (candidate b).hom (algebraSchemeMap k A) :=
  pullbackSpecIso_hom_snd k (candidateRing b) A

/-- Canonical identification of actual fibre-product global functions with
the tensor coordinate ring. -/
def fibreCoordinates :
    Γ(candidateFibre b, ⊤) ≅ CommRingCat.of (candidateRing b ⊗[k] A) :=
  (Scheme.Γ.mapIso (fibreSpecIso b).op).symm ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (candidateRing b ⊗[k] A))

/-- The universal unit on the actual scheme fibre product. -/
def universalUnit :
    RelativeGlobalUnits.sections (algebraSchemeMap k A) (candidate b) :=
  _root_.Units.map (fibreCoordinates b).inv.hom.toMonoidHom
    (algebraicUniversalUnit b)

/-- In canonical affine coordinates the actual universal unit is the localized
generic element. -/
lemma universalUnit_coordinates :
    (fibreCoordinates b).hom (universalUnit b : Γ(candidateFibre b, ⊤)) =
      localizedGenericElement b := by
  change ((fibreCoordinates b).inv ≫ (fibreCoordinates b).hom)
    (algebraicUniversalUnit b : candidateRing b ⊗[k] A) = _
  rw [Iso.inv_hom_id]
  exact algebraicUniversalUnit_val b

/-- The coordinate formula for the universal unit, including all basis coordinates. -/
lemma universalUnit_formula :
    (fibreCoordinates b).hom (universalUnit b : Γ(candidateFibre b, ⊤)) =
      ∑ i, algebraMap (coordinateRing k n) (candidateRing b) (MvPolynomial.X i) ⊗ₜ[k] b i := by
  rw [universalUnit_coordinates, localizedGenericElement_eq_sum]

/-- The canonical map from the actual candidate's functor of points to actual
relative global units. -/
def candidateMap :
    (AlgebraicSpace.schemeYoneda (base k)).obj (candidate b) ⟶ presheaf k A :=
  RelativeGlobalUnits.fromUniversalUnit (algebraSchemeMap k A) (candidate b) (universalUnit b)

/-- Every component pulls back the same universal unit along the induced
morphism of actual fibre products. -/
lemma candidateMap_app (T : Over (base k)) (h : T ⟶ candidate b) :
    ((candidateMap b).app (op T) ⟨h⟩).down =
      _root_.Units.map
        ((Picard.relativeSpace (algebraSchemeMap k A)).map h).appTop.hom.toMonoidHom
        (universalUnit b) := rfl

/-- Formula on the underlying global functions for every test scheme. -/
lemma candidateMap_app_val (T : Over (base k)) (h : T ⟶ candidate b) :
    (((candidateMap b).app (op T) ⟨h⟩).down :
        Γ((Picard.relativeSpace (algebraSchemeMap k A)).obj T, ⊤)) =
      ((Picard.relativeSpace (algebraSchemeMap k A)).map h).appTop
        (universalUnit b : Γ(candidateFibre b, ⊤)) := rfl

/-- Naturality on arbitrary scheme tests is the composition law for ordinary
pullback of the universal unit. -/
lemma candidateMap_naturality {T U : Over (base k)} (h : T ⟶ U)
    (j : U ⟶ candidate b) :
    (presheaf k A).map h.op ((candidateMap b).app (op U) ⟨j⟩) =
      (candidateMap b).app (op T) ⟨h ≫ j⟩ := by
  apply ULift.ext
  exact RelativeGlobalUnits.fromUniversalUnit_naturality
    (algebraSchemeMap k A) (candidate b) (universalUnit b) h j

end Langlands.AlgebraicGeometry.FiniteAlgebraUnits

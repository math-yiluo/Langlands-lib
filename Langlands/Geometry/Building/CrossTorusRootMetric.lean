import Langlands.Geometry.Building.ValuationApartmentMetric
import Langlands.Geometry.Building.CrossTorusApartmentComparison

/-! # Root-coordinate isometries under cross-torus apartment transport -/

noncomputable section

universe u uA uB

open CategoryTheory AlgebraicGeometry
open scoped BigOperators
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace RootTranslationMetric

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (i : S.toGrp ⟶ G) (j : S'.toGrp ⟶ H)
  [Fintype (relativeRoots i)] [Fintype (relativeRoots j)]

attribute [local instance] normedAddCommGroup normedSpace

/-- Matching the actual root coordinates up to a bijection preserves the root
norm. The two embeddings may involve different tori and ambient groups. -/
theorem norm_eq_of_rootForm_equiv (e : relativeRoots i ≃ relativeRoots j)
    (v : TranslationSpace i) (w : TranslationSpace j)
    (h : ∀ a, rootForm j (e a) w = rootForm i a v) : ‖w‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq, norm_sq]
  exact (Fintype.sum_equiv e _ _ (fun a => congrArg (fun r : ℝ => r ^ 2) (h a).symm)).symm

/-- An affine map preserving actual root coordinates up to a bijection is an
isometry for any apartment metrics induced by these same root norms. -/
theorem isometry_of_rootForm_equiv
    {A : Type uA} {B : Type uB}
    [MetricSpace A] [NormedAddTorsor (TranslationSpace i) A]
    [MetricSpace B] [NormedAddTorsor (TranslationSpace j) B]
    (c : A →ᵃ[ℝ] B) (e : relativeRoots i ≃ relativeRoots j)
    (h : ∀ a v, rootForm j (e a) (c.linear v) = rootForm i a v) :
    Isometry c := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm_vsub (TranslationSpace j), dist_eq_norm_vsub (TranslationSpace i),
    ← c.linearMap_vsub]
  exact norm_eq_of_rootForm_equiv i j e _ _ (fun a => h a (x -ᵥ y))

variable (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

/-- The actual quotient map of cocharacters under a based isomorphism preserves
its canonical root norm. No metric on a building is required. -/
theorem norm_translationSpaceTransportEquiv (v : TranslationSpace i) :
    ‖translationSpaceTransportEquiv e f h v‖ = ‖v‖ :=
  norm_eq_of_rootForm_equiv i j (relativeRootsTransportEquiv e f h) v _
    (fun a => rootForm_translationSpaceTransportEquiv e f h a v)

/-- Actual based transport is an isometry of the root-normed translation spaces. -/
theorem isometry_translationSpaceTransportEquiv :
    Isometry (translationSpaceTransportEquiv e f h) := by
  apply Isometry.of_dist_eq
  intro v w
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_translationSpaceTransportEquiv]

/-- The same actual based transport, bundled as an isometric equivalence for
both canonical root norms. -/
def translationSpaceTransportIsometryEquiv : TranslationSpace i ≃ᵢ TranslationSpace j where
  toEquiv := (translationSpaceTransportEquiv e f h).toEquiv
  isometry_toFun := isometry_translationSpaceTransportEquiv i j e f h

@[simp] theorem translationSpaceTransportIsometryEquiv_apply (v : TranslationSpace i) :
    translationSpaceTransportIsometryEquiv i j e f h v =
      translationSpaceTransportEquiv e f h v := rfl

end RootTranslationMetric

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [Fintype (relativeRoots i)] [Fintype (relativeRoots j)]
  {ω : kˣ → ℝ}
  (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
  (D : KPApartmentData i ω) (E : KPApartmentData j ω)

attribute [local instance] RootTranslationMetric.normedAddCommGroup
  RootTranslationMetric.normedSpace

/-- Comparing a transported full apartment class with separately supplied data
preserves the norm of every displacement, independently of the matching point. -/
theorem norm_vsub_apartmentTransportAffineEquivOfMem (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier)
    (x y : D.Apartment) :
    ‖D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀ x -ᵥ
      D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀ y‖ = ‖x -ᵥ y‖ := by
  change ‖(D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀).toAffineMap x -ᵥ
    (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀).toAffineMap y‖ = _
  rw [← (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀).toAffineMap.linearMap_vsub]
  change ‖translationSpaceTransportEquiv e f h (x -ᵥ y)‖ = ‖x -ᵥ y‖
  exact RootTranslationMetric.norm_translationSpaceTransportEquiv i j e f h _

/-- The actual comparison with separately supplied data is isometric for any
metrics realizing the canonical root norms of the two apartments. In particular,
this applies to inner conjugation without assuming either torus descends. -/
theorem isometry_apartmentTransportAffineEquivOfMem
    [MetricSpace D.Apartment] [MetricSpace E.Apartment]
    (hD : ∀ x y : D.Apartment, dist x y = ‖(x -ᵥ y : TranslationSpace i)‖)
    (hE : ∀ x y : E.Apartment, dist x y = ‖(x -ᵥ y : TranslationSpace j)‖)
    (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier) :
    Isometry (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [hE, hD]
  exact D.norm_vsub_apartmentTransportAffineEquivOfMem e f h E x₀ h₀ x y

/-- The actual full-apartment comparison bundled as an isometric equivalence.
The distance hypotheses refer to the apartments' original affine differences. -/
def apartmentTransportIsometryEquivOfMem
    [MetricSpace D.Apartment] [MetricSpace E.Apartment]
    (hD : ∀ x y : D.Apartment, dist x y = ‖(x -ᵥ y : TranslationSpace i)‖)
    (hE : ∀ x y : E.Apartment, dist x y = ‖(x -ᵥ y : TranslationSpace j)‖)
    (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier) :
    D.Apartment ≃ᵢ E.Apartment where
  toEquiv := (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀).toEquiv
  isometry_toFun := D.isometry_apartmentTransportAffineEquivOfMem e f h E hD hE x₀ h₀

@[simp] theorem apartmentTransportIsometryEquivOfMem_apply
    [MetricSpace D.Apartment] [MetricSpace E.Apartment]
    (hD : ∀ x y : D.Apartment, dist x y = ‖(x -ᵥ y : TranslationSpace i)‖)
    (hE : ∀ x y : E.Apartment, dist x y = ‖(x -ᵥ y : TranslationSpace j)‖)
    (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier) (x : D.Apartment) :
    D.apartmentTransportIsometryEquivOfMem e f h E hD hE x₀ h₀ x =
      D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀ x := rfl

end KPApartmentData

end Langlands.Geometry.Building

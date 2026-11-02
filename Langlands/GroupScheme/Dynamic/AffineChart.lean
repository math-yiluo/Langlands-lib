import Langlands.GroupScheme.Dynamic.Representability

/-! # Coordinate description of dynamic unipotent subgroups of affine group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic.AffineChart

open AffineLine

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

section Points

/-- The structure morphism of `G`, read on the spectrum of its global sections. -/
def chartMap : Spec Γ(G.X.left, ⊤) ⟶ Spec R :=
  G.X.left.isoSpec.inv ≫ G.X.hom

/-- The universal point of `G` over `Spec Γ(G, ⊤)`: the inverse of the canonical isomorphism
`G ≅ Spec Γ(G, ⊤)`. -/
def universalPoint : Over.mk (chartMap G) ⟶ G.X :=
  Over.homMk G.X.left.isoSpec.inv rfl

variable {G} {A : CommRingCat.{u}} {f : Spec A ⟶ Spec R}

/-- The ring map `Γ(G, ⊤) ⟶ A` classifying a point of `G` over `Spec A`. -/
def pointRing (x : Over.mk f ⟶ G.X) : Γ(G.X.left, ⊤) ⟶ A :=
  Spec.preimage (x.left ≫ G.X.left.isoSpec.hom)

theorem specMap_pointRing (x : Over.mk f ⟶ G.X) :
    Spec.map (pointRing x) = x.left ≫ G.X.left.isoSpec.hom :=
  Spec.map_preimage _

/-- Points over `Spec A` are determined by their classifying ring maps. -/
theorem hom_ext_of_pointRing {x y : Over.mk f ⟶ G.X} (h : pointRing x = pointRing y) :
    x = y := by
  apply Over.OverMorphism.ext
  have h' := congrArg Spec.map h
  rw [specMap_pointRing, specMap_pointRing] at h'
  exact (cancel_mono _).1 h'

/-- The classifying ring map of a restricted point. -/
theorem pointRing_comp {A' : CommRingCat.{u}} {f' : Spec A' ⟶ Spec R}
    (y : Over.mk f' ⟶ Over.mk f) (x : Over.mk f ⟶ G.X) :
    pointRing (y ≫ x) = pointRing x ≫ Spec.preimage y.left := by
  apply Spec.map_injective
  rw [specMap_pointRing, Spec.map_comp, Spec.map_preimage, specMap_pointRing, Over.comp_left,
    Category.assoc]

/-- A point of `G` over `Spec A`, as a morphism to `Spec Γ(G, ⊤)` over `Spec R`. -/
def chartHom (x : Over.mk f ⟶ G.X) : Over.mk f ⟶ Over.mk (chartMap G) :=
  Over.homMk (x.left ≫ G.X.left.isoSpec.hom) (by
    simp only [Over.mk_hom, chartMap, Category.assoc, Iso.hom_inv_id_assoc]
    exact Over.w x)

/-- Every point over `Spec A` is the pullback of the universal point. -/
theorem chartHom_comp_universalPoint (x : Over.mk f ⟶ G.X) :
    chartHom x ≫ universalPoint G = x :=
  Over.OverMorphism.ext (by
    change (x.left ≫ G.X.left.isoSpec.hom) ≫ G.X.left.isoSpec.inv = x.left
    simp)

variable (G) in
/-- The counit `Γ(G, ⊤) ⟶ R`: the ring map classifying the identity point over `Spec R`. -/
def counit : Γ(G.X.left, ⊤) ⟶ R :=
  pointRing (1 : Over.mk (𝟙 (Spec R)) ⟶ G.X)

/-- The identity point over `Spec A` is classified by the counit followed by `R ⟶ A`. -/
theorem pointRing_one : pointRing (1 : Over.mk f ⟶ G.X) = counit G ≫ Spec.preimage f := by
  have h : (Over.homMk f (Category.comp_id f) : Over.mk f ⟶ Over.mk (𝟙 (Spec R))) ≫
      (1 : Over.mk (𝟙 (Spec R)) ⟶ G.X) = 1 :=
    MonObj.comp_one _
  rw [← h, pointRing_comp]
  rfl

end Points

section Coaction

variable {G} (χ : (Gm (Spec R)).toGrp ⟶ G)

/-- The coaction `Γ(G, ⊤) ⟶ Γ(G, ⊤)[T, T⁻¹]` of `𝔾_m` on `G` by conjugation through `χ`: the
ring map classifying the orbit map of the universal point on `Spec Γ(G, ⊤)[T, T⁻¹]`. -/
def coaction : Γ(G.X.left, ⊤) ⟶ CommRingCat.of (LaurentPolynomial Γ(G.X.left, ⊤)) :=
  pointRing (laurentPoint (chartMap G) ≫ orbit χ (universalPoint G))

variable {A : CommRingCat.{u}} {f : Spec A ⟶ Spec R}

/-- The orbit map on `Spec A[T, T⁻¹]` of a point `x` over `Spec A` is classified by the
coaction followed by the coefficient map of `x`. -/
theorem pointRing_laurentPoint_comp_orbit (x : Over.mk f ⟶ G.X) :
    pointRing (laurentPoint f ≫ orbit χ x) = coaction χ ≫ laurentCoeffMap (pointRing x) := by
  have h : laurentPoint f ≫ orbit χ x =
      laurentMap (chartHom x) ≫ laurentPoint (chartMap G) ≫ orbit χ (universalPoint G) := by
    conv_lhs => rw [← chartHom_comp_universalPoint x]
    rw [← whiskerRight_orbit, reassoc_of% (laurentPoint_comp_whiskerRight (chartHom x))]
  rw [h, pointRing_comp]
  change coaction χ ≫ Spec.preimage (Spec.map (laurentCoeffMap (pointRing x))) = _
  rw [Spec.preimage_map]

end Coaction

section Extension

variable {G} (χ : (Gm (Spec R)).toGrp ⟶ G) {A : CommRingCat.{u}} {f : Spec A ⟶ Spec R}

/-- A ring map `θ : Γ(G, ⊤) ⟶ A[X]` lifting the coaction composed with the classifying map of
`x` defines a morphism `Spec A[X] ⟶ G` over `Spec R`. -/
def polynomialExtension (x : Over.mk f ⟶ G.X)
    (θ : Γ(G.X.left, ⊤) ⟶ CommRingCat.of (Polynomial A))
    (hθ : θ ≫ polynomialToLaurent A = coaction χ ≫ laurentCoeffMap (pointRing x)) :
    polynomialScheme f ⟶ G.X :=
  Over.homMk (Spec.map θ ≫ G.X.left.isoSpec.inv) (by
    apply specMap_polynomialToLaurent_cancel
    have h1 : Spec.map (polynomialToLaurent A) ≫ Spec.map θ ≫ G.X.left.isoSpec.inv =
        (laurentPoint f ≫ orbit χ x).left := by
      rw [← Category.assoc, ← Spec.map_comp, hθ, ← pointRing_laurentPoint_comp_orbit,
        specMap_pointRing, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h2 : Spec.map (polynomialToLaurent A) ≫ (Spec.map θ ≫ G.X.left.isoSpec.inv) ≫ G.X.hom =
        (laurentPoint f ≫ orbit χ x).left ≫ G.X.hom := by
      rw [← h1]
      simp only [Category.assoc]
    exact h2.trans (Over.w (laurentPoint f ≫ orbit χ x)))

variable {χ}

theorem laurentInclusion_comp_polynomialExtension (x : Over.mk f ⟶ G.X)
    (θ : Γ(G.X.left, ⊤) ⟶ CommRingCat.of (Polynomial A))
    (hθ : θ ≫ polynomialToLaurent A = coaction χ ≫ laurentCoeffMap (pointRing x)) :
    laurentInclusion f ≫ polynomialExtension χ x θ hθ = laurentPoint f ≫ orbit χ x := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  change Spec.map (polynomialToLaurent A) ≫ Spec.map θ ≫ G.X.left.isoSpec.inv = _
  rw [← Category.assoc, ← Spec.map_comp, hθ, ← pointRing_laurentPoint_comp_orbit,
    specMap_pointRing, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem pointRing_polynomialExtension (x : Over.mk f ⟶ G.X)
    (θ : Γ(G.X.left, ⊤) ⟶ CommRingCat.of (Polynomial A))
    (hθ : θ ≫ polynomialToLaurent A = coaction χ ≫ laurentCoeffMap (pointRing x)) :
    pointRing (polynomialExtension χ x θ hθ) = θ := by
  change Spec.preimage ((Spec.map θ ≫ G.X.left.isoSpec.inv) ≫ G.X.left.isoSpec.hom) = θ
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Spec.preimage_map]

/-- The classifying ring map of an extension along `Spec A[X, X⁻¹] ⊆ Spec A[X]` of the orbit map
of `x` lifts the coaction composed with the classifying map of `x`. -/
theorem pointRing_comp_polynomialToLaurent {x : Over.mk f ⟶ G.X}
    {E : polynomialScheme f ⟶ G.X}
    (h : laurentInclusion f ≫ E = laurentPoint f ≫ orbit χ x) :
    pointRing E ≫ polynomialToLaurent A = coaction χ ≫ laurentCoeffMap (pointRing x) := by
  rw [← pointRing_laurentPoint_comp_orbit, ← h, pointRing_comp]
  change _ = pointRing E ≫ Spec.preimage (Spec.map (polynomialToLaurent A))
  rw [Spec.preimage_map]

theorem pointRing_polynomialZero_comp (E : polynomialScheme f ⟶ G.X) :
    pointRing (polynomialZero f ≫ E) = pointRing E ≫ polynomialEvalZero A := by
  rw [pointRing_comp]
  change _ ≫ Spec.preimage (Spec.map (polynomialEvalZero A)) = _
  rw [Spec.preimage_map]

end Extension

section Membership

variable {G} (χ : (Gm (Spec R)).toGrp ⟶ G) {A : CommRingCat.{u}} {f : Spec A ⟶ Spec R}

/-- A point over `Spec A` lies in `U_G(χ)` exactly when its classifying ring map kills the
coefficients of negative degree of the coaction, and sends the constant coefficient of `c(b)` to
the image of the counit `ε(b)` in `A`. -/
theorem mem_unipotent_iff (x : Over.mk f ⟶ G.X) :
    x ∈ (unipotent χ).carrier (Over.mk f) ↔
      (∀ b, ∀ n < 0, pointRing x ((coaction χ b).coeff n) = 0) ∧
        ∀ b, pointRing x ((coaction χ b).coeff 0) = Spec.preimage f (counit G b) := by
  constructor
  · rintro ⟨E, hE, hE0⟩
    have hθ := pointRing_comp_polynomialToLaurent (laurentInclusion_comp_of_whiskerLeft f hE)
    have hc : ∀ b n, pointRing x ((coaction χ b).coeff n) =
        (Polynomial.toLaurent (pointRing (polynomialPoint f ≫ E) b)).coeff n := by
      intro b n
      rw [← Corepresented.coeff_laurentCoeffMap, ← CommRingCat.comp_apply, ← hθ]
      rfl
    refine ⟨fun b n hn => by rw [hc]; exact coeff_toLaurent_of_neg _ hn, fun b => ?_⟩
    have h0 : polynomialZero f ≫ polynomialPoint f ≫ E = 1 := by
      rw [← evalZero_polynomialPointInv, ← Category.assoc,
        polynomialPointInv_comp_polynomialPoint, Category.id_comp, hE0]
    have h1 := congrArg pointRing h0
    rw [pointRing_polynomialZero_comp, pointRing_one] at h1
    have h2 := congrArg (fun φ => φ b) h1
    calc pointRing x ((coaction χ b).coeff 0)
        = (Polynomial.toLaurent (pointRing (polynomialPoint f ≫ E) b)).coeff ((0 : ℕ) : ℤ) :=
          hc b 0
      _ = (pointRing (polynomialPoint f ≫ E) b).eval 0 := by
          rw [coeff_toLaurent_natCast, Polynomial.coeff_zero_eq_eval_zero]
      _ = Spec.preimage f (counit G b) := h2
  · rintro ⟨hP, h0⟩
    have hL : ∀ b, ∀ n < 0, ((coaction χ ≫ laurentCoeffMap (pointRing x)) b).coeff n = 0 :=
      fun b n hn =>
        (Corepresented.coeff_laurentCoeffMap (pointRing x) (coaction χ b) n).trans (hP b n hn)
    refine ⟨polynomialPointInv f ≫ polynomialExtension χ x _ (polynomialLift_comp _ hL),
      whiskerLeft_comp_of_laurentInclusion f (laurentInclusion_comp_polynomialExtension x _ _), ?_⟩
    rw [evalZero_polynomialPointInv]
    apply hom_ext_of_pointRing
    rw [pointRing_polynomialZero_comp, pointRing_polynomialExtension, pointRing_one]
    refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    calc (polynomialLift _ hL ≫ polynomialEvalZero A).hom b
        = (LaurentPolynomial.trunc (laurentCoeffMap (pointRing x) (coaction χ b))).coeff 0 :=
          (Polynomial.coeff_zero_eq_eval_zero _).symm
      _ = pointRing x ((coaction χ b).coeff 0) :=
          Corepresented.coeff_laurentCoeffMap (pointRing x) (coaction χ b) 0
      _ = (counit G ≫ Spec.preimage f).hom b := h0 b

end Membership

end Langlands.GroupScheme.Dynamic.AffineChart

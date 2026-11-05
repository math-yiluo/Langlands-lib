import Langlands.GroupScheme.IdentityComponentRationalGalois
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Coefficient action on actual scheme components -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The semilinear automorphism of the actual pullback scheme, using the inverse
coefficient spectrum map so that its action agrees with coefficient conjugation. -/
def coefficientSchemeMap (σ : L ≃ₐ[k] L) :
    (baseChanged k L G).X.left ⟶ (baseChanged k L G).X.left :=
  pullback.lift (pullback.fst G.X.hom (baseMap k L))
    (pullback.snd G.X.hom (baseMap k L) ≫ galoisBaseMap k L σ⁻¹)
    (by rw [Category.assoc, galoisBaseMap_over]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem coefficientSchemeMap_fst (σ : L ≃ₐ[k] L) :
    coefficientSchemeMap k L G σ ≫ pullback.fst G.X.hom (baseMap k L) =
      pullback.fst G.X.hom (baseMap k L) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem coefficientSchemeMap_snd (σ : L ≃ₐ[k] L) :
    coefficientSchemeMap k L G σ ≫ pullback.snd G.X.hom (baseMap k L) =
      pullback.snd G.X.hom (baseMap k L) ≫ galoisBaseMap k L σ⁻¹ :=
  pullback.lift_snd _ _ _

@[simp]
theorem coefficientSchemeMap_one :
    coefficientSchemeMap k L G 1 = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- Scheme morphisms compose in diagrammatic order; the induced point maps
compose in the left-action order. -/
theorem coefficientSchemeMap_mul (σ τ : L ≃ₐ[k] L) :
    coefficientSchemeMap k L G (σ * τ) =
      coefficientSchemeMap k L G τ ≫ coefficientSchemeMap k L G σ := by
  apply pullback.hom_ext <;>
    simp [mul_inv_rev, galoisBaseMap_mul, Category.assoc]

/-- The actual scheme isomorphism inducing coefficient conjugation on components.
It is semilinear over `Spec L`, and lies over the original `k`-group scheme. -/
def coefficientSchemeIso (σ : L ≃ₐ[k] L) :
    (baseChanged k L G).X.left ≅ (baseChanged k L G).X.left where
  hom := coefficientSchemeMap k L G σ
  inv := coefficientSchemeMap k L G σ⁻¹
  hom_inv_id := by
    rw [← coefficientSchemeMap_mul, inv_mul_cancel, coefficientSchemeMap_one]
  inv_hom_id := by
    rw [← coefficientSchemeMap_mul, mul_inv_cancel, coefficientSchemeMap_one]

/-- On rational sections, coefficient conjugation is semilinear composition
with the actual pullback-scheme automorphism. -/
theorem rationalConjugate_left (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) :
    (rationalConjugate k L G σ x).left =
      galoisBaseMap k L σ ≫ x.left ≫ coefficientSchemeMap k L G σ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, coefficientSchemeMap_fst]
    have h := congrArg (fun p => p.left)
      (baseChangeCoeffEquiv_rationalConjugate k L G σ x)
    rw [baseChangeCoeffEquiv_left] at h
    change (rationalConjugate k L G σ x).left ≫
        pullback.fst G.X.hom (baseMap k L) =
      galoisBaseMap k L σ ≫ (baseChangeCoeffEquiv k L G x).left at h
    rwa [baseChangeCoeffEquiv_left] at h
  · simp only [Category.assoc, coefficientSchemeMap_snd]
    have hx : x.left ≫ pullback.snd G.X.hom (baseMap k L) = 𝟙 _ := x.w
    have hσ : galoisBaseMap k L σ ≫ galoisBaseMap k L σ⁻¹ = 𝟙 _ := by
      rw [← galoisBaseMap_mul, mul_inv_cancel, galoisBaseMap_one]
    rw [← Category.assoc x.left, hx, Category.id_comp]
    exact (rationalConjugate k L G σ x).w.trans hσ.symm

/-- The unique point of `Spec L` removes the source reparametrization from
the semilinear section equation. -/
theorem rationalConjugate_point (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) :
    (rationalConjugate k L G σ x).left (IdentityComponent.basePoint L) =
      coefficientSchemeMap k L G σ (x.left (IdentityComponent.basePoint L)) := by
  rw [rationalConjugate_left, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact congrArg
    (fun p : Spec (CommRingCat.of L) => coefficientSchemeMap k L G σ (x.left p))
    (Subsingleton.elim _ _)

/-- The permutation of all connected components of the actual pullback scheme. -/
def coefficientComponents (σ : L ≃ₐ[k] L) :
    Equiv.Perm (_root_.ConnectedComponents (baseChanged k L G).X.left) where
  toFun := (coefficientSchemeIso k L G σ).hom.continuous.connectedComponentsMap
  invFun := (coefficientSchemeIso k L G σ).inv.continuous.connectedComponentsMap
  left_inv := by
    intro c
    obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    simp only [Continuous.connectedComponentsMap_mk]
    change _root_.ConnectedComponents.mk
      (((coefficientSchemeIso k L G σ).hom ≫
        (coefficientSchemeIso k L G σ).inv) p) = _root_.ConnectedComponents.mk p
    rw [Iso.hom_inv_id]
    rfl
  right_inv := by
    intro c
    obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    simp only [Continuous.connectedComponentsMap_mk]
    change _root_.ConnectedComponents.mk
      (((coefficientSchemeIso k L G σ).inv ≫
        (coefficientSchemeIso k L G σ).hom) p) = _root_.ConnectedComponents.mk p
    rw [Iso.inv_hom_id]
    rfl

@[simp]
theorem coefficientComponents_mk (σ : L ≃ₐ[k] L) (p : (baseChanged k L G).X.left) :
    coefficientComponents k L G σ (_root_.ConnectedComponents.mk p) =
      _root_.ConnectedComponents.mk (coefficientSchemeMap k L G σ p) :=
  rfl

@[simp]
theorem coefficientComponents_one : coefficientComponents k L G 1 = 1 := by
  ext c
  obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  simp

theorem coefficientComponents_mul (σ τ : L ≃ₐ[k] L) :
    coefficientComponents k L G (σ * τ) =
      coefficientComponents k L G σ * coefficientComponents k L G τ := by
  ext c
  obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  simp only [Equiv.Perm.mul_apply, coefficientComponents_mk]
  rw [coefficientSchemeMap_mul, Scheme.Hom.comp_apply]

/-- The coefficient-automorphism action on actual scheme connected components. -/
def schemeComponentGaloisAction :
    (L ≃ₐ[k] L) →* Equiv.Perm
      (_root_.ConnectedComponents (baseChanged k L G).X.left) where
  toFun := coefficientComponents k L G
  map_one' := coefficientComponents_one k L G
  map_mul' := coefficientComponents_mul k L G

/-- The action on actual components agrees with conjugation of rational sections. -/
theorem coefficientComponents_pointComponent (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) :
    coefficientComponents k L G σ
        (IdentityComponent.pointComponent (baseChanged k L G) x) =
      IdentityComponent.pointComponent (baseChanged k L G)
        (rationalConjugate k L G σ x) := by
  exact congrArg _root_.ConnectedComponents.mk (rationalConjugate_point k L G σ x).symm

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- The existing embedding of rational-component quotients into actual scheme
components intertwines the two constructed coefficient actions. -/
theorem rationalComponentEmbedding_conjugate (σ : L ≃ₐ[k] L)
    (c : RationalComponentQuotient (baseChanged k L H)) :
    rationalComponentEmbedding (baseChanged k L H)
        (rationalComponentConjugate k L H σ c) =
      coefficientComponents k L H σ
        (rationalComponentEmbedding (baseChanged k L H) c) := by
  obtain ⟨x, rfl⟩ := rationalComponentProjection_surjective _ c
  rw [rationalComponentConjugate_projection,
    rationalComponentEmbedding_projection, rationalComponentEmbedding_projection]
  exact (coefficientComponents_pointComponent k L H σ x).symm

/-- Fixedness of a rational-component class is detected on its actual scheme component. -/
theorem rationalComponentEmbedding_fixed_iff
    (c : RationalComponentQuotient (baseChanged k L H)) :
    (∀ σ : L ≃ₐ[k] L, coefficientComponents k L H σ
      (rationalComponentEmbedding (baseChanged k L H) c) =
        rationalComponentEmbedding (baseChanged k L H) c) ↔
      c ∈ rationalComponentFixedSubgroup k L H := by
  constructor
  · intro hc σ
    apply (rationalComponentEmbedding (baseChanged k L H)).injective
    rw [rationalComponentEmbedding_conjugate]
    exact hc σ
  · intro hc σ
    rw [← rationalComponentEmbedding_conjugate, hc σ]

/-- The image of rational-component classes is preserved and reflected by
every coefficient permutation of actual scheme components. -/
theorem coefficientComponents_mem_range_rationalComponentEmbedding_iff
    (σ : L ≃ₐ[k] L)
    (c : _root_.ConnectedComponents (baseChanged k L H).X.left) :
    coefficientComponents k L H σ c ∈
        Set.range (rationalComponentEmbedding (baseChanged k L H)) ↔
      c ∈ Set.range (rationalComponentEmbedding (baseChanged k L H)) := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨(rationalComponentConjugate k L H σ).symm d, ?_⟩
    apply (coefficientComponents k L H σ).injective
    rw [← rationalComponentEmbedding_conjugate, MulEquiv.apply_symm_apply, hd]
  · rintro ⟨d, rfl⟩
    exact ⟨rationalComponentConjugate k L H σ d,
      rationalComponentEmbedding_conjugate k L H σ d⟩

/-- Actual scheme components arising by extension of a rational class from the
base field are fixed under every coefficient permutation. -/
theorem coefficientComponents_rationalComponentBaseChange
    (σ : L ≃ₐ[k] L) (c : RationalComponentQuotient H) :
    coefficientComponents k L H σ
        (rationalComponentEmbedding (baseChanged k L H)
          (rationalComponentBaseChange H (algebraMap k L) c)) =
      rationalComponentEmbedding (baseChanged k L H)
        (rationalComponentBaseChange H (algebraMap k L) c) := by
  rw [← rationalComponentEmbedding_conjugate, rationalComponentConjugate_baseChange]

end Langlands.GroupScheme.IdentityComponent

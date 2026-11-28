import Langlands.Geometry.Building.DepthZero.GeneralLinear.ZeroSubgroup
import Langlands.Geometry.Building.BuildingFacetPartition

/-!
# Scalar matrices and facets of KP building data of `GL_N`

* A scalar matrix `u · 1` is central in `GL_N(F)`, its inner automorphism of the group scheme
  `GL_N` is the identity, and it fixes every point of the reduced building of any building data
  (`scalarPoint_mem_fixer`): it normalizes the maximal split torus through the identity, so it
  acts trivially on the valuations of the root datum, and it commutes with `G(F)`.
* For building data satisfying the one-group axioms, the parahoric `D.parahoric x` of a facet is
  `G(F)^0` intersected with the pointwise fixer of the facet (Axiom 4.1.20,
  `ModelAxiomClauses.neutral_points`), and a facet containing a vertex `y` is `{y}`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.GeneralLinearParahoric

variable {F : Type u} [Field F] {N : ℕ}

/-- The scalar matrix `u · 1` as a rational point of `GL_N`. -/
def scalarPoint (u : Fˣ) : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) :=
  toMatrixGL.symm (diagGL fun _ => u)

theorem diagGL_const_commute (u : Fˣ) (M : GL (Fin N) F) :
    diagGL (fun _ => u) * M = M * diagGL (fun _ => u) := by
  ext p q : 2
  simp only [Units.val_mul, coe_diagGL, diagonal_mul, mul_diagonal, mul_comm]

/-- Scalar matrices are central. -/
theorem scalarPoint_commute (u : Fˣ)
    (g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :
    scalarPoint u * g = g * scalarPoint u := by
  apply toMatrixGL.injective
  rw [map_mul, map_mul, scalarPoint, MulEquiv.apply_symm_apply, diagGL_const_commute]

/-- A scalar matrix over any ring commutes with all invertible matrices. -/
theorem diagonal_const_commute {A : Type*} [CommRing A] (a : A) (M : Matrix (Fin N) (Fin N) A) :
    diagonal (fun _ => a) * M = M * diagonal (fun _ => a) := by
  ext p q
  simp only [diagonal_mul, mul_diagonal, mul_comm]

/-- The inner automorphism of `GL_N` given by a scalar matrix is the identity. -/
theorem innerIso_scalarPoint (u : Fˣ) :
    ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).innerIso
      (scalarPoint u)).hom = 𝟙 _ := by
  apply hom_ext_points
  intro U x
  apply (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) U).injective
  rw [comp_innerIso_hom]
  change _ = GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) U x
  rw [map_mul, map_mul, map_inv]
  have hc : ((GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) U
      ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).constantPoint (scalarPoint u) U) :
        GL (Fin N) Γ(U.left, ⊤)) : Matrix (Fin N) (Fin N) Γ(U.left, ⊤)) =
      diagonal fun _ => U.hom.appTop.hom
        ((GeneralLinear.globalSectionsEquiv (CommRingCat.of F)).symm (u : F)) := by
    rw [GeneralLinear.pointsEquiv_constantPoint]
    ext p q
    change U.hom.appTop.hom _ = _
    have hpt : GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) (Over.mk (𝟙 _))
        (scalarPoint u) =
        GeneralLinear.glRingEquiv (GeneralLinear.globalSectionsEquiv (CommRingCat.of F)).symm
          (diagGL fun _ => u) := by
      apply (GeneralLinear.glRingEquiv
        (GeneralLinear.globalSectionsEquiv (CommRingCat.of F))).injective
      change toMatrixGL (scalarPoint u) = _
      rw [scalarPoint, MulEquiv.apply_symm_apply]
      ext p q : 2
      simp [GeneralLinear.glRingEquiv_apply]
    rw [hpt, GeneralLinear.glRingEquiv_apply, coe_diagGL, diagonal_apply, diagonal_apply]
    split_ifs <;> simp
  have hcomm : GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) U
      ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).constantPoint (scalarPoint u) U) *
        GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) U x =
      GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) U x *
        GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) U
          ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).constantPoint
            (scalarPoint u) U) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hc, diagonal_const_commute]
  rw [hcomm, mul_inv_cancel_right]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- A scalar matrix fixes every point of the reduced building of any building data of `GL_N`. -/
theorem scalarPoint_mem_fixer
    (B : ValuationBuildingData (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)))
    (u : Fˣ) (y : B.ReducedBuilding) : scalarPoint u ∈ B.fixer y := by
  have hn : scalarPoint u ∈ normalizerPoints B.i :=
    ⟨Iso.refl _, by
      rw [isNormalizingPoint_refl_iff, innerIso_scalarPoint, Category.comp_id]⟩
  let n : normalizerPoints B.i := ⟨scalarPoint u, hn⟩
  have hw : weylAction B.i n = 1 := by
    apply LinearEquiv.ext
    intro χ
    rw [weylAction_eq B.i (σ := Iso.refl _)
      (by rw [isNormalizingPoint_refl_iff, innerIso_scalarPoint, Category.comp_id]) χ]
    exact Category.id_comp χ
  have hfix : ∀ x : B.Apartment, n • x = x := by
    intro x
    apply KPApartmentData.Apartment.ext
    rw [KPApartmentData.val_smul]
    ext a g
    rw [RootFunctionFamily.smul_apply, map_inv, hw, inv_one, LinearEquiv.coe_one, id]
    congr 1
    change (scalarPoint u)⁻¹ * g * scalarPoint u = g
    rw [mul_assoc, ← scalarPoint_commute, inv_mul_cancel_left]
  obtain ⟨h, x, rfl⟩ := B.exists_smul_apartmentMap y
  rw [ValuationBuildingData.mem_fixer, ← mul_smul, scalarPoint_commute, mul_smul]
  congr 1
  change n.1 • B.apartmentMap x = B.apartmentMap x
  rw [B.normalizer_smul_apartmentMap, hfix]

end Langlands.Geometry.Building.GeneralLinearParahoric

namespace Langlands.Geometry.Building.KPBuildingDatum

open BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (D : KPBuildingDatum G)

/-- Under Axiom 4.1.20 the parahoric of a facet is `G(F)^0` intersected with the pointwise fixer
of the facet. -/
theorem parahoric_eq_pointwiseFixer_inf (hD : D.SatisfiesGroupAxioms)
    (x : BuildingFacet D.base.toValuationBuildingData) :
    D.parahoric x = D.base.pointwiseFixer x.val ⊓ D.base.zeroSubgroup :=
  hD.bruhatTitsGroupSchemes.neutral_points (BuildingModelIndex.ofFacet x)

/-- Under the apartment axioms, the facet containing a vertex `y` is `{y}`. -/
theorem val_eq_singleton_of_isVertex (hD : D.SatisfiesGroupAxioms)
    {y : D.base.ReducedBuilding} (hy : D.base.IsVertex y)
    (x : BuildingFacet D.base.toValuationBuildingData) (hx : y ∈ x.val) : x.val = {y} := by
  obtain ⟨g, x₀, rfl, hx₀⟩ := hy
  have hfacet : D.base.IsFacet {g • D.base.apartmentMap x₀} :=
    ⟨g, {x₀}, ⟨x₀, hx₀⟩, by rw [Set.image_singleton]⟩
  exact x.property.eq_of_mem_mem D.base.toValuationBuildingData
    hD.affineRootSystem.apartmentAxioms hfacet hx rfl

end Langlands.Geometry.Building.KPBuildingDatum

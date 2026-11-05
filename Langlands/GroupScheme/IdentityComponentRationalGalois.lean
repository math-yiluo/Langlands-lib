import Langlands.GroupScheme.IdentityComponentRationalBaseChange
import Langlands.GroupScheme.GaloisPointRational

/-! # Coefficient automorphisms on rational identity-component quotients -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Coefficient conjugation commutes with a homomorphism defined over the base field. -/
theorem rationalConjugate_naturality (f : G ⟶ H) (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) :
    rationalConjugate k L H σ
        (x ≫ ((GroupScheme.baseChange (baseMap k L)).map f).hom.hom) =
      rationalConjugate k L G σ x ≫
        ((GroupScheme.baseChange (baseMap k L)).map f).hom.hom := by
  change rationalConjugate k L H σ
      (rationalPoints.map ((GroupScheme.baseChange (baseMap k L)).map f) x) =
    rationalPoints.map ((GroupScheme.baseChange (baseMap k L)).map f)
      (rationalConjugate k L G σ x)
  apply (baseChangeCoeffEquiv k L H).injective
  rw [baseChangeCoeffEquiv_rationalConjugate,
    baseChangeCoeffEquiv_map, baseChangeCoeffEquiv_map,
    baseChangeCoeffEquiv_rationalConjugate]
  exact G.affinePointAut_target f σ _

/-- The published coefficient extension is the actual pullback of a rational section. -/
theorem rationalExtend_eq_baseChangeSectionHom (x : rationalPoints G) :
    rationalExtend k L G x = baseChangeSectionHom (baseMap k L) G x := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (rationalExtend_fst k L G x).trans
      (baseChangeSectionHom_fst (baseMap k L) G x).symm
  · exact (rationalExtend k L G x).w.trans
      (baseChangeSectionHom (baseMap k L) G x).w.symm

/-- Coefficient automorphisms fix every pulled-back rational section. -/
@[simp]
theorem rationalConjugate_baseChangeSectionHom (σ : L ≃ₐ[k] L)
    (x : rationalPoints G) :
    rationalConjugate k L G σ (baseChangeSectionHom (baseMap k L) G x) =
      baseChangeSectionHom (baseMap k L) G x := by
  rw [← rationalExtend_eq_baseChangeSectionHom k L]
  apply (baseChangeCoeffEquiv k L G).injective
  simp

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- Coefficient conjugation preserves the actual identity-component subgroup. -/
theorem rationalConjugate_mem_rationalIdentitySubgroup (σ : L ≃ₐ[k] L)
    {x : rationalPoints (baseChanged k L H)}
    (hx : x ∈ rationalIdentitySubgroup (baseChanged k L H)) :
    rationalConjugate k L H σ x ∈
      rationalIdentitySubgroup (baseChanged k L H) := by
  rcases (mem_rationalIdentitySubgroup _ x).mp hx with ⟨y, rfl⟩
  let y' : rationalPoints (baseChanged k L (identityComponent H)) :=
    y ≫ (baseChangeIso H (algebraMap k L)).inv.hom.hom
  have hy' : y' ≫
        ((GroupScheme.baseChange (baseMap k L)).map (identityComponentι H)).hom.hom =
      y ≫ (identityComponentι (baseChanged k L H)).hom.hom := by
    dsimp only [y']
    rw [Category.assoc, ← Grp.comp_hom_hom, baseChangeIso_inv_comp]
  apply (mem_rationalIdentitySubgroup _ _).mpr
  refine ⟨rationalConjugate k L (identityComponent H) σ y' ≫
    (baseChangeIso H (algebraMap k L)).hom.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, baseChangeIso_hom_identityComponentι]
  rw [← hy', rationalConjugate_naturality]

/-- Coefficient conjugation detects identity-component membership as well as preserving it. -/
theorem rationalConjugate_mem_rationalIdentitySubgroup_iff (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L H)) :
    rationalConjugate k L H σ x ∈ rationalIdentitySubgroup (baseChanged k L H) ↔
      x ∈ rationalIdentitySubgroup (baseChanged k L H) := by
  constructor
  · intro hx
    have h := rationalConjugate_mem_rationalIdentitySubgroup k L H σ⁻¹ hx
    rwa [← rationalConjugate_mul, inv_mul_cancel, rationalConjugate_one] at h
  · exact rationalConjugate_mem_rationalIdentitySubgroup k L H σ

/-- Descend coefficient conjugation through the actual identity-component subgroup. -/
def rationalComponentConjugateHom (σ : L ≃ₐ[k] L) :
    RationalComponentQuotient (baseChanged k L H) →*
      RationalComponentQuotient (baseChanged k L H) :=
  rationalComponentLift (baseChanged k L H)
    ((rationalComponentProjection _).comp (rationalConjugate k L H σ).toMonoidHom)
    (by
      intro x hx
      change rationalComponentProjection _ (rationalConjugate k L H σ x) = 1
      apply MonoidHom.mem_ker.mp
      rw [ker_rationalComponentProjection]
      exact rationalConjugate_mem_rationalIdentitySubgroup k L H σ hx)

@[simp]
theorem rationalComponentConjugateHom_projection (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L H)) :
    rationalComponentConjugateHom k L H σ (rationalComponentProjection _ x) =
      rationalComponentProjection _ (rationalConjugate k L H σ x) :=
  rfl

@[simp]
theorem rationalComponentConjugateHom_one :
    rationalComponentConjugateHom k L H 1 =
      MonoidHom.id (RationalComponentQuotient (baseChanged k L H)) := by
  apply rationalComponentHom_ext
  intro x
  simp

theorem rationalComponentConjugateHom_mul (σ τ : L ≃ₐ[k] L) :
    rationalComponentConjugateHom k L H (σ * τ) =
      (rationalComponentConjugateHom k L H σ).comp
        (rationalComponentConjugateHom k L H τ) := by
  apply rationalComponentHom_ext
  intro x
  simp only [MonoidHom.comp_apply, rationalComponentConjugateHom_projection,
    rationalConjugate_mul]

/-- The automorphism of the ordinary rational-component group induced by a coefficient
automorphism. Its inverse is induced by the inverse coefficient automorphism. -/
def rationalComponentConjugate (σ : L ≃ₐ[k] L) :
    MulAut (RationalComponentQuotient (baseChanged k L H)) where
  toFun := rationalComponentConjugateHom k L H σ
  invFun := rationalComponentConjugateHom k L H σ⁻¹
  left_inv := by
    intro c
    change ((rationalComponentConjugateHom k L H σ⁻¹).comp
      (rationalComponentConjugateHom k L H σ)) c = c
    rw [← rationalComponentConjugateHom_mul, inv_mul_cancel,
      rationalComponentConjugateHom_one]
    rfl
  right_inv := by
    intro c
    change ((rationalComponentConjugateHom k L H σ).comp
      (rationalComponentConjugateHom k L H σ⁻¹)) c = c
    rw [← rationalComponentConjugateHom_mul, mul_inv_cancel,
      rationalComponentConjugateHom_one]
    rfl
  map_mul' := (rationalComponentConjugateHom k L H σ).map_mul

@[simp]
theorem rationalComponentConjugate_toMonoidHom (σ : L ≃ₐ[k] L) :
    (rationalComponentConjugate k L H σ).toMonoidHom =
      rationalComponentConjugateHom k L H σ :=
  rfl

@[simp]
theorem rationalComponentConjugate_projection (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L H)) :
    rationalComponentConjugate k L H σ (rationalComponentProjection _ x) =
      rationalComponentProjection _ (rationalConjugate k L H σ x) :=
  rfl

@[simp]
theorem rationalComponentConjugate_one :
    rationalComponentConjugate k L H 1 = 1 := by
  ext c
  change rationalComponentConjugateHom k L H 1 c = c
  rw [rationalComponentConjugateHom_one]
  rfl

theorem rationalComponentConjugate_mul (σ τ : L ≃ₐ[k] L) :
    rationalComponentConjugate k L H (σ * τ) =
      rationalComponentConjugate k L H σ * rationalComponentConjugate k L H τ := by
  ext c
  exact congrArg (fun f => f c) (rationalComponentConjugateHom_mul k L H σ τ)

/-- The natural action of the coefficient-automorphism group on rational components. -/
def rationalComponentGaloisAction :
    (L ≃ₐ[k] L) →* MulAut (RationalComponentQuotient (baseChanged k L H)) where
  toFun := rationalComponentConjugate k L H
  map_one' := rationalComponentConjugate_one k L H
  map_mul' := rationalComponentConjugate_mul k L H

/-- Every rational-component class pulled back from the base field is fixed. -/
@[simp]
theorem rationalComponentConjugate_baseChange (σ : L ≃ₐ[k] L)
    (c : RationalComponentQuotient H) :
    rationalComponentConjugate k L H σ
        (rationalComponentBaseChange H (algebraMap k L) c) =
      rationalComponentBaseChange H (algebraMap k L) c := by
  obtain ⟨x, rfl⟩ := rationalComponentProjection_surjective H c
  rw [rationalComponentBaseChange_projection, rationalComponentConjugate_projection,
    rationalConjugate_baseChangeSectionHom]

/-- The subgroup of classes fixed by every coefficient automorphism. -/
def rationalComponentFixedSubgroup :
    Subgroup (RationalComponentQuotient (baseChanged k L H)) where
  carrier := {c | ∀ σ : L ≃ₐ[k] L, rationalComponentConjugate k L H σ c = c}
  one_mem' σ := map_one _
  mul_mem' hc hd σ := by rw [map_mul, hc σ, hd σ]
  inv_mem' hc σ := by rw [map_inv, hc σ]

@[simp]
theorem mem_rationalComponentFixedSubgroup
    (c : RationalComponentQuotient (baseChanged k L H)) :
    c ∈ rationalComponentFixedSubgroup k L H ↔
      ∀ σ : L ≃ₐ[k] L, rationalComponentConjugate k L H σ c = c :=
  Iff.rfl

/-- Field extension factors through the subgroup of fixed rational-component classes. -/
def rationalComponentBaseChangeToFixed :
    RationalComponentQuotient H →* rationalComponentFixedSubgroup k L H where
  toFun c := ⟨rationalComponentBaseChange H (algebraMap k L) c,
    fun σ => rationalComponentConjugate_baseChange k L H σ c⟩
  map_one' := Subtype.ext (map_one (rationalComponentBaseChange H (algebraMap k L)))
  map_mul' c d := Subtype.ext (map_mul (rationalComponentBaseChange H (algebraMap k L)) c d)

@[simp]
theorem rationalComponentBaseChangeToFixed_val (c : RationalComponentQuotient H) :
    (rationalComponentBaseChangeToFixed k L H c).val =
      rationalComponentBaseChange H (algebraMap k L) c :=
  rfl

/-- The fixed-class factorization is injective, as is the underlying field-extension map. -/
theorem rationalComponentBaseChangeToFixed_injective :
    Function.Injective (rationalComponentBaseChangeToFixed k L H) := by
  intro c d h
  apply rationalComponentBaseChange_injective H (algebraMap k L)
  exact congrArg Subtype.val h

variable {H}
  {H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- Actual homomorphisms defined over the base field induce equivariant component maps. -/
theorem rationalComponentConjugate_naturality (f : H ⟶ H') (σ : L ≃ₐ[k] L)
    (c : RationalComponentQuotient (baseChanged k L H)) :
    rationalComponentConjugate k L H' σ
        (rationalComponentMap ((GroupScheme.baseChange (baseMap k L)).map f) c) =
      rationalComponentMap ((GroupScheme.baseChange (baseMap k L)).map f)
        (rationalComponentConjugate k L H σ c) := by
  obtain ⟨x, rfl⟩ := rationalComponentProjection_surjective _ c
  simp only [rationalComponentMap_projection, rationalComponentConjugate_projection,
    rationalConjugate_naturality]

end Langlands.GroupScheme.IdentityComponent

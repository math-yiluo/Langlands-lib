import Langlands.AlgebraicGeometry.Modules.AffineBaseSections
import Langlands.AlgebraicGeometry.Modules.ClosedImmersionStalkQuotient
import Langlands.AlgebraicGeometry.Modules.StalkPullback
import Langlands.AlgebraicGeometry.Picard.FormalLineBundleSystem
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Actual adic thickening stalks as quotients -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Modules.AdicStalkQuotient

open Picard.FormalLineBundle

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))

/-- The base ring action on an actual stalk. -/
def baseStalkHom (x : X) : R →+* X.presheaf.stalk x :=
  (f.stalkMap x).hom.comp
    (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f x) trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

lemma germ_comp_baseSectionHom (U : X.Opens) (x : X) (hx : x ∈ U) :
    (X.presheaf.germ U x hx).hom.comp (baseSectionHom f U) = baseStalkHom f x := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top ≫
      X.presheaf.germ U x hx).hom =
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec (CommRingCat.of R)).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x).hom
  congr 1
  rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc,
    TopCat.Presheaf.germ_res]

instance (I : Ideal R) (n : ℕ) : IsClosedImmersion (adicProjection f I n) := by
  let : IsClosedImmersion (adicBaseProjection I n) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) Ideal.Quotient.mk_surjective
  dsimp only [adicProjection]
  infer_instance

/-- The affine-section kernel of the actual adic projection. -/
lemma ker_adicProjection_app (I : Ideal R) (n : ℕ) (U : X.Opens)
    (hU : IsAffineOpen U) :
    RingHom.ker ((adicProjection f I n).app U).hom =
      (I ^ (n + 1)).map (baseSectionHom f U) := by
  let p := adicProjection f I n
  let q := pullback.snd f (adicBaseProjection I n)
  have H : IsPullback p q f (adicBaseProjection I n) := IsPullback.of_hasPullback _ _
  have hUY : p ⁻¹ᵁ U = p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ ⊤ := by simp
  have h1 := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    le_top le_top hUY (isAffineOpen_top _) (isAffineOpen_top _) hU
  have h2 := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U)
    le_top le_top hUY).mp h1
  have hleg : (adicBaseProjection I n).appLE ⊤ ⊤ le_top =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (n + 1)))).inv := by
    change (adicBaseProjection I n).appTop = _
    dsimp only [adicBaseProjection]
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  have hg : Function.Surjective ((adicBaseProjection I n).appLE ⊤ ⊤ le_top).hom := by
    rw [hleg]
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (n + 1)))).inv).2.comp
      (Ideal.Quotient.mk_surjective.comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).2)
  have hker := P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.CommRingCat.ker_eq_map_ker_of_isPushout h2 hg
  rw [Scheme.Hom.appLE_eq_app] at hker
  rw [hker, hleg]
  have hbase : RingHom.ker
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (n + 1)))).inv).hom =
        (I ^ (n + 1)).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    change RingHom.ker
      ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (n + 1)))).inv.hom.comp
        ((Ideal.Quotient.mk (I ^ (n + 1))).comp
          (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom)) = _
    rw [RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (n + 1)))).inv).1,
      ← RingHom.comap_ker, Ideal.mk_ker]
    exact (Ideal.map_symm
      ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv)).symm
  rw [hbase, Ideal.map_map]
  rfl

/-- The kernel on actual adic stalks is a power of one fixed extended ideal. -/
lemma ker_adicProjection_stalkMap (I : Ideal R) (n : ℕ) (y : adicSpace f I n) :
    RingHom.ker ((adicProjection f I n).stalkMap y).hom =
      (I.map (baseStalkHom f (adicProjection f I n y))) ^ (n + 1) := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := adicProjection f I n y) (by simp)
  rw [ClosedImmersion.ker_stalkMap_eq_map (adicProjection f I n) y U hU hx,
    ker_adicProjection_app f I n U hU, Ideal.map_map, germ_comp_baseSectionHom, Ideal.map_pow]

/-- The actual adic stalk as an algebra over its original ambient stalk. -/
def quotientStalkAlgEquiv (I : Ideal R) (n : ℕ) (y : adicSpace f I n) :
    letI := ((adicProjection f I n).stalkMap y).hom.toAlgebra
    (X.presheaf.stalk (adicProjection f I n y) ⧸
      (I.map (baseStalkHom f (adicProjection f I n y))) ^ (n + 1)) ≃ₐ[
        X.presheaf.stalk (adicProjection f I n y)] (adicSpace f I n).presheaf.stalk y := by
  letI := ((adicProjection f I n).stalkMap y).hom.toAlgebra
  exact (Ideal.quotientEquivAlgOfEq (X.presheaf.stalk (adicProjection f I n y))
    (ker_adicProjection_stalkMap f I n y).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (f := Algebra.ofId (X.presheaf.stalk (adicProjection f I n y))
          ((adicSpace f I n).presheaf.stalk y))
        ((adicProjection f I n).stalkMap_surjective y))

/-- Ordinary pullback to the actual adic thickening has the expected quotient stalk,
with linearity over the original ambient stalk. -/
def pullbackStalkQuotientEquiv (M : X.Modules) (I : Ideal R) (n : ℕ)
    (y : adicSpace f I n) :
    letI := ((adicProjection f I n).stalkMap y).hom.toAlgebra
    letI := relativeStalkModule (adicProjection f I n)
      ((Scheme.Modules.pullback (adicProjection f I n)).obj M) y
    stalk ((Scheme.Modules.pullback (adicProjection f I n)).obj M) y ≃ₗ[
      X.presheaf.stalk (adicProjection f I n y)]
      stalk M (adicProjection f I n y) ⧸
        ((I.map (baseStalkHom f (adicProjection f I n y))) ^ (n + 1) •
          (⊤ : Submodule (X.presheaf.stalk (adicProjection f I n y))
            (stalk M (adicProjection f I n y)))) := by
  letI := ((adicProjection f I n).stalkMap y).hom.toAlgebra
  letI := relativeStalkModule (adicProjection f I n)
    ((Scheme.Modules.pullback (adicProjection f I n)).obj M) y
  have : IsScalarTower (X.presheaf.stalk (adicProjection f I n y))
      ((adicSpace f I n).presheaf.stalk y)
      (stalk ((Scheme.Modules.pullback (adicProjection f I n)).obj M) y) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  exact ((StalkPullback.pullbackStalkTensorEquiv (adicProjection f I n) y M).restrictScalars
      (X.presheaf.stalk (adicProjection f I n y))).trans
    ((TensorProduct.congr (quotientStalkAlgEquiv f I n y).symm.toLinearEquiv
      (LinearEquiv.refl _ _)).trans
        (TensorProduct.quotTensorEquivQuotSMul _ _))

end Langlands.AlgebraicGeometry.Modules.AdicStalkQuotient

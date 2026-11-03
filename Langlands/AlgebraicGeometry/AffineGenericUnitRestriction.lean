import Langlands.AlgebraicGeometry.AffineScalarLocalization
import Langlands.CommutativeAlgebra.ScalarLocalizationUnitRestriction

/-! # Detecting total units by restriction between affine closed-fibre opens -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped nonZeroDivisors

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R))
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U)

/-- Restriction between actual affine section algebras, with the algebra
structures recovered from their common structure morphism. -/
def affineSectionRestrictionAlgHom :
    letI := affineSectionAlgebra p hU
    letI := affineSectionAlgebra p hV
    Γ(X, U) →ₐ[R] Γ(X, V) := by
  let := affineSectionAlgebra p hU
  let := affineSectionAlgebra p hV
  refine { (X.presheaf.map (homOfLE hVU).op).hom with commutes' := ?_ }
  intro r
  have hs : CommRingCat.ofHom (algebraMap R Γ(X, U)) ≫
      X.presheaf.map (homOfLE hVU).op =
      CommRingCat.ofHom (algebraMap R Γ(X, V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, affineSectionAlgebra_specMap p hU,
      affineSectionAlgebra_specMap p hV, ← Category.assoc,
      IsAffineOpen.map_fromSpec]
  exact congrArg (fun f => f.hom r) hs

variable [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (q : Y ⟶ X) (s : Y ⟶ Spec (CommRingCat.of K))
    (H : IsPullback q s p (Spec.map (CommRingCat.ofHom (algebraMap R K))))

include hV K s H in
/-- A generic unit on an affine open lifts to a total unit if its restriction
to a smaller affine open meeting the closed fibre lifts. Projectivity is
required only on the larger affine section algebra. -/
theorem exists_unit_of_affine_generic_restriction [Smooth p] [GeometricallyConnected p]
    (hmeet : (p ⁻¹' {IsLocalRing.closedPoint R} ∩ (V : Set X)).Nonempty)
    (hproj : letI := affineSectionAlgebra p hU; Module.Projective R Γ(X, U))
    (b : Γ(Y, q ⁻¹ᵁ U)ˣ) (c : Γ(X, V)ˣ)
    (hc : Y.presheaf.map (homOfLE (q.preimage_mono hVU)).op (b : Γ(Y, q ⁻¹ᵁ U)) =
      q.app V (c : Γ(X, V))) :
    ∃ a : Γ(X, U)ˣ, q.app U (a : Γ(X, U)) = (b : Γ(Y, q ⁻¹ᵁ U)) := by
  let := affineSectionAlgebra p hU
  let := affineSectionAlgebra p hV
  let := pullbackSectionAlgebra q U
  let := pullbackSectionAlgebra q V
  let : Module.Projective R Γ(X, U) := hproj
  let : Module.Flat R Γ(X, V) := flat_affineSectionAlgebra p hV
  let : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, U) R⁰) Γ(Y, q ⁻¹ᵁ U) :=
    isLocalization_pullbackSectionAlgebra q U K p s H hU
  let : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, V) R⁰) Γ(Y, q ⁻¹ᵁ V) :=
    isLocalization_pullbackSectionAlgebra q V K p s H hV
  have hmeetU : (p ⁻¹' {IsLocalRing.closedPoint R} ∩ (U : Set X)).Nonempty := by
    obtain ⟨x, hx, hVx⟩ := hmeet
    exact ⟨x, hx, hVU hVx⟩
  have hpU := closedFibreIdeal_isPrime_affineSectionAlgebra p hU hmeetU
  have hpV := closedFibreIdeal_isPrime_affineSectionAlgebra p hV hmeet
  let f := affineSectionRestrictionAlgHom p hU hV hVU
  let g := (Y.presheaf.map (homOfLE (q.preimage_mono hVU)).op).hom
  apply Langlands.CommutativeAlgebra.exists_unit_of_scalarLocalization_restriction
    hpU hpV.ne_top f g _ b c hc
  intro a
  change Y.presheaf.map (homOfLE (q.preimage_mono hVU)).op (q.app U a) =
    q.app V (X.presheaf.map (homOfLE hVU).op a)
  simp only [Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply,
    Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- Choose the total unit detected by the smaller closed-fibre neighbourhood,
retaining the equality under the original generic section map. -/
def affineGenericUnitOfRestriction [Smooth p] [GeometricallyConnected p]
    (hmeet : (p ⁻¹' {IsLocalRing.closedPoint R} ∩ (V : Set X)).Nonempty)
    (hproj : letI := affineSectionAlgebra p hU; Module.Projective R Γ(X, U))
    (b : Γ(Y, q ⁻¹ᵁ U)ˣ) (c : Γ(X, V)ˣ)
    (hc : Y.presheaf.map (homOfLE (q.preimage_mono hVU)).op (b : Γ(Y, q ⁻¹ᵁ U)) =
      q.app V (c : Γ(X, V))) :
    {a : Γ(X, U)ˣ // q.app U (a : Γ(X, U)) = (b : Γ(Y, q ⁻¹ᵁ U))} :=
  ⟨Classical.choose
      (exists_unit_of_affine_generic_restriction p hU hV hVU K q s H hmeet hproj b c hc),
    Classical.choose_spec
      (exists_unit_of_affine_generic_restriction p hU hV hVU K q s H hmeet hproj b c hc)⟩

end Langlands.AlgebraicGeometry

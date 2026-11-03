import Langlands.GroupScheme.Dynamic.SmoothConnectedStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.AffineDecomposition
import Langlands.GroupScheme.Dynamic.CoactionGrading
import Langlands.GroupScheme.SmoothProducts
import Langlands.CommutativeAlgebra.GradedFormallySmooth

/-! # Proof: smoothness of dynamic subgroups of a smooth affine group over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace DynamicSmooth

open CommutativeAlgebra.GradedFormallySmooth

variable {R : CommRingCat.{u}}

/-- The spectrum of an `R`-algebra is smooth over `Spec R` exactly when the algebra is smooth. -/
theorem smooth_algSpec_iff (A : CommAlgCat.{u} R) :
    Smooth ((algSpec R).obj (op A)).hom ↔ Algebra.Smooth R A := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔ _
  rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom, RingHom.smooth_algebraMap]

/-- A formally smooth quotient of a smooth algebra over a noetherian ring is smooth. -/
theorem smooth_quotient [IsNoetherianRing R] {B : CommAlgCat.{u} R} [Algebra.Smooth R B]
    {I : Ideal B} (h : Algebra.FormallySmooth R (B ⧸ I)) : Algebra.Smooth R (B ⧸ I) where
  formallySmooth := h
  finitePresentation := by
    have : Algebra.FiniteType R (B ⧸ I) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
    exact Algebra.FinitePresentation.of_finiteType.mp this

/-- A retract over `Spec R` of the spectrum of a formally smooth `R`-algebra is the spectrum of a
formally smooth `R`-algebra. -/
theorem formallySmooth_of_algSpec_retract {A A' : CommAlgCat.{u} R} [Algebra.FormallySmooth R A]
    (s : (algSpec R).obj (op A') ⟶ (algSpec R).obj (op A))
    (r : (algSpec R).obj (op A) ⟶ (algSpec R).obj (op A')) (h : s ≫ r = 𝟙 _) :
    Algebra.FormallySmooth R A' := by
  have h' : (algSpec.fullyFaithful.preimage r).unop ≫ (algSpec.fullyFaithful.preimage s).unop =
      𝟙 A' := by
    have h1 := congrArg algSpec.fullyFaithful.preimage h
    rw [Functor.FullyFaithful.preimage_comp, Functor.FullyFaithful.preimage_id] at h1
    simpa using congrArg Quiver.Hom.unop h1
  refine formallySmooth_of_retract (algSpec.fullyFaithful.preimage r).unop.hom
    (algSpec.fullyFaithful.preimage s).unop.hom ?_
  rw [← CommAlgCat.hom_comp, h', CommAlgCat.hom_id]

/-- A section `X ⟶ Y` of `Y ≅ X ⊗ Z ⟶ X` through a point of `Z`. -/
theorem lift_comp_hom_comp_inv_comp_fst {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {X Y Z : C} (g : X ⟶ Z) (i : X ⊗ Z ≅ Y) :
    (lift (𝟙 X) g ≫ i.hom) ≫ i.inv ≫ fst X Z = 𝟙 X := by
  rw [Category.assoc, Iso.hom_inv_id_assoc, lift_fst]

section Corepresented

variable {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B} [Algebra.Smooth R B]
  (χ : (Gm (Spec R)).toGrp ⟶ Corepresented.groupScheme F e)

theorem formallySmooth_parabolic :
    Algebra.FormallySmooth R (B ⧸ Corepresented.parabolicIdeal χ) :=
  formallySmooth_quotient_negIdeal (c := (Corepresented.coaction χ).hom)
    (Corepresented.coaction_algebraMap χ) (Corepresented.sum_coeff_coaction χ)
    (Corepresented.coaction_coeff_coaction χ)

theorem formallySmooth_centralizer :
    Algebra.FormallySmooth R (B ⧸ Corepresented.centralizerIdeal χ) :=
  formallySmooth_quotient_offIdeal (c := (Corepresented.coaction χ).hom)
    (Corepresented.coaction_algebraMap χ) (Corepresented.coaction_coeff_coaction χ)

/-- The constructed dynamic parabolic `P_G(χ)` is smooth. -/
theorem smooth_parabolicScheme [IsNoetherianRing R] :
    Smooth (Corepresented.parabolicScheme χ).X.hom :=
  (smooth_algSpec_iff (Corepresented.quotientAlgebra (Corepresented.parabolicIdeal χ))).2
    (smooth_quotient (formallySmooth_parabolic χ))

/-- The constructed centralizer `Z_G(χ)` is smooth. -/
theorem smooth_centralizerScheme [IsNoetherianRing R] :
    Smooth (Corepresented.centralizerScheme χ).X.hom :=
  (smooth_algSpec_iff (Corepresented.quotientAlgebra (Corepresented.centralizerIdeal χ))).2
    (smooth_quotient (formallySmooth_centralizer χ))

/-- The constructed dynamic unipotent subgroup `U_G(χ)` is a retract of `P_G(χ)` over `Spec R`,
through the multiplication isomorphism `U_G(χ) × Z_G(χ) ≅ P_G(χ)`, so it is smooth. -/
theorem smooth_unipotentScheme [IsNoetherianRing R] :
    Smooth (Corepresented.unipotentScheme χ).X.hom := by
  have : Algebra.FormallySmooth R (B ⧸ Corepresented.parabolicIdeal χ) :=
    formallySmooth_parabolic χ
  have hU : Algebra.FormallySmooth R (B ⧸ Corepresented.unipotentIdeal χ) :=
    formallySmooth_of_algSpec_retract
      (A := Corepresented.quotientAlgebra (Corepresented.parabolicIdeal χ))
      (A' := Corepresented.quotientAlgebra (Corepresented.unipotentIdeal χ))
      (lift (𝟙 _) 1 ≫ (Corepresented.multiplicationIso χ).hom)
      ((Corepresented.multiplicationIso χ).inv ≫ fst _ _)
      (lift_comp_hom_comp_inv_comp_fst 1 (Corepresented.multiplicationIso χ))
  exact (smooth_algSpec_iff (Corepresented.quotientAlgebra (Corepresented.unipotentIdeal χ))).2
    (smooth_quotient hU)

end Corepresented

end DynamicSmooth

open DynamicSmooth in
/-- **Smoothness of dynamic subgroups.** For a smooth affine group scheme `G` over a field and a
cocharacter `χ`, every representative of `P_G(χ)`, `Z_G(χ)` or `U_G(χ)` is smooth. -/
theorem dynamicSmooth : DynamicSmoothStatement.{u} := by
  intro k _ G _ _ χ H j
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hB : Algebra.Smooth (CommRingCat.of k) (AffineCoordinates.algebra G) :=
    (smooth_algSpec_iff (AffineCoordinates.algebra G)).1
      (smooth_of_over_iso ((Grp.forget _).mapIso (AffineCoordinates.groupSchemeIso G))
        (inferInstance : Smooth G.X.hom))
  refine ⟨fun hj => ?_, fun hj => ?_, fun hj => ?_⟩
  · exact smooth_of_over_iso
      ((Grp.forget _).mapIso
        (hj.isoOfIsRepresentedBy (Dynamic.Affine.isRepresentedBy_parabolicHom χ)))
      (smooth_parabolicScheme (Dynamic.Affine.cocharacter χ))
  · exact smooth_of_over_iso
      ((Grp.forget _).mapIso
        (hj.isoOfIsRepresentedBy (Dynamic.Affine.isRepresentedBy_centralizerHom χ)))
      (smooth_centralizerScheme (Dynamic.Affine.cocharacter χ))
  · exact smooth_of_over_iso
      ((Grp.forget _).mapIso
        (hj.isoOfIsRepresentedBy (Dynamic.Affine.isRepresentedBy_unipotentHom χ)))
      (smooth_unipotentScheme (Dynamic.Affine.cocharacter χ))

end Langlands.GroupScheme

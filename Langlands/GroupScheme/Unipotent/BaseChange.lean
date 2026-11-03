import Langlands.GroupScheme.Unipotent.CoordinateBialgebra
import Langlands.GroupScheme.Unipotent.ScalarExtension
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.HopfBaseChange
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Unipotence is invariant under extension of the base field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.Unipotent

open AffineLinearEmbedding

/-- Bialgebra structures built from algebra maps agree when their comultiplications and counits
agree. -/
theorem ofAlgHom_congr {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {comul comul' : A →ₐ[R] A ⊗[R] A} {counit counit' : A →ₐ[R] R} (h₁ : comul = comul')
    (h₂ : counit = counit') {p₁ p₂ p₃} :
    Bialgebra.ofAlgHom comul counit p₁ p₂ p₃ = Bialgebra.ofAlgHom comul' counit'
      (by subst h₁; exact p₁) (by subst h₁ h₂; exact p₂) (by subst h₁ h₂; exact p₃) := by
  subst h₁ h₂
  rfl

section Cogroup

variable {R : CommRingCat.{u}} (C : Grp (CommAlgCat.{u} R)ᵒᵖ)

/-- The comultiplication of the coordinate bialgebra of the point functor of an algebra cogroup
is the cogroup comultiplication. -/
theorem comul_cogroupCorepresentation :
    comul (Corepresented.cogroupCorepresentation C) = μ[C.X].unop.hom := by
  have h : comul (Corepresented.cogroupCorepresentation C) =
      (Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
        Algebra.TensorProduct.includeRight fun _ _ => .all _ _).comp μ[C.X].unop.hom := rfl
  rw [h, Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_comp]

/-- The counit of the coordinate bialgebra of the point functor of an algebra cogroup is the
cogroup counit. -/
theorem counit_cogroupCorepresentation :
    counit (Corepresented.cogroupCorepresentation C) = η[C.X].unop.hom :=
  rfl

/-- The coordinate bialgebra structure of the point functor of an algebra cogroup is the
bialgebra structure of the cogroup. -/
theorem bialgebra_cogroupCorepresentation :
    bialgebra (Corepresented.cogroupCorepresentation C) =
      (inferInstance : Bialgebra R C.X.unop) := by
  unfold bialgebra
  exact ofAlgHom_congr (comul_cogroupCorepresentation C) (counit_cogroupCorepresentation C)

end Cogroup

section Field

variable {k : Type u} [Field k] (C : Grp (CommAlgCat.{u} (CommRingCat.of k))ᵒᵖ)

/-- If the spectrum of an algebra cogroup over a field is unipotent, every nonzero
finite-dimensional right-translation stable subspace of its coordinate bialgebra contains `1`. -/
theorem oneMemStable_of_isUnipotent_cogroup
    (h : IsUnipotent ((algSpec _).mapGrp.obj C)) : OneMemStable k C.X.unop := by
  have h' := oneMemStable_of_isUnipotent (Corepresented.cogroupCorepresentation C)
    (IsUnipotent.of_iso ((algSpec _).mapGrp.mapIso (Corepresented.cogroupRecoveryIso C)) h)
  rwa [bialgebra_cogroupCorepresentation] at h'

/-- Conversely, if every nonzero finite-dimensional right-translation stable subspace of the
coordinate bialgebra of an algebra cogroup over a field contains `1`, its spectrum is
unipotent. -/
theorem isUnipotent_cogroup_of_oneMemStable (h : OneMemStable k C.X.unop) :
    IsUnipotent ((algSpec _).mapGrp.obj C) := by
  refine IsUnipotent.of_iso
    ((algSpec _).mapGrp.mapIso (Corepresented.cogroupRecoveryIso C)).symm ?_
  apply isUnipotent_of_oneMemStable
  rwa [bialgebra_cogroupCorepresentation]

end Field

/-- Unipotence of an affine group scheme over a field is preserved by extension of the base
field. -/
theorem _root_.Langlands.GroupScheme.IsUnipotent.baseChange {k K : Type u} [Field k] [Field K]
    [Algebra k K] {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (hH : IsUnipotent H) :
    IsUnipotent ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H) := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let C := AffineCoordinates.coordinateCogroup H
  have h1 : OneMemStable k C.X.unop := oneMemStable_of_isUnipotent_cogroup C
    (IsUnipotent.of_iso (AffineCoordinates.coordinateCogroupIso H) hH)
  have h2 : OneMemStable K (K ⊗[k] C.X.unop) := h1.baseChange K
  let C' := ((commHopfAlgCatEquivCogrpCommAlgCat (CommRingCat.of K)).functor.obj
    (HopfCoordinates.scalarExtension k K C.X.unop)).unop
  have h3 := isUnipotent_cogroup_of_oneMemStable C' h2
  refine IsUnipotent.of_iso ?_ h3
  exact (GroupScheme.baseChange _).mapIso (AffineCoordinates.hopfSpecIso H).symm ≪≫
    HopfCoordinates.baseChangeSpecIso k K C.X.unop

end Langlands.GroupScheme.Unipotent

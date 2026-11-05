import Langlands.Algebra.PTorsionHopf.PolynomialStructure
import Langlands.GroupScheme.Rational.CommutativeVectorClassificationStatement
import Langlands.GroupScheme.Rational.TorusSplitUnipotenceProof
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.HopfPrimitiveQuotient
import Langlands.GroupScheme.CentralIsogeny.KernelTorsion

/-! # Smooth connected commutative groups killed by `p` are vector groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial WithConv
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace HopfPrimitive

variable {R : CommRingCat.{u}} (A : CommHopfAlgCat.{u} R) {n : ℕ} {y : Fin n → A}
  (hy : ∀ i, Bialgebra.IsPrimitiveElem R (y i))

/-- The natural homomorphism `g ↦ (g(yᵢ))ᵢ` from points of `Spec A` to `𝔾ₐⁿ`, on algebras. -/
def familyPointsHom :
    yonedaGrp.obj (cogroup A) ⟶ Corepresented.presheaf (VectorGroup.functor R n) where
  app _ := GrpCat.ofHom (MonoidHom.mk' (fun g => Multiplicative.ofAdd fun i => g.unop.hom (y i))
    (fun g h => Multiplicative.toAdd.injective
      (funext fun i => mul_unop_hom_apply A (hy i) g h)))
  naturality _ _ _ := rfl

/-- The cogroup homomorphism dual to the Hopf algebra map `R[X₁, …, Xₙ] ⟶ A`, `Xᵢ ↦ yᵢ`. -/
def familyCogroupHom :
    cogroup A ⟶
      Corepresented.cogroup (VectorGroup.functor R n) (VectorGroup.corepresentableBy R n) :=
  yonedaGrpFullyFaithful.preimage
    (familyPointsHom A hy ≫ (Corepresented.pointsIso _ (VectorGroup.corepresentableBy R n)).inv)

/-- The homomorphism `Spec A ⟶ 𝔾ₐⁿ` given by a family of primitive elements. -/
def familyHom : (hopfSpec R).obj (op A) ⟶ VectorGroup.groupScheme R n :=
  (algSpec R).mapGrp.map (familyCogroupHom A hy)

theorem familyHom_left :
    (familyHom A hy).hom.hom.left =
      Spec.map (CommRingCat.ofHom (aeval y : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom) := rfl

/-- A Hopf algebra which is a polynomial algebra on primitive elements has spectrum isomorphic,
as a group scheme, to the vector group. -/
def isoVectorGroup (hbij : Function.Bijective (aeval y : MvPolynomial (Fin n) R →ₐ[R] A)) :
    (hopfSpec R).obj (op A) ≅ VectorGroup.groupScheme R n :=
  have h1 : IsIso (CommRingCat.ofHom (aeval y : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbij
  have h2 : IsIso (Spec.map
      (CommRingCat.ofHom (aeval y : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom)) :=
    ⟨Spec.map (inv (CommRingCat.ofHom (aeval y : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom)),
      by rw [← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id],
      by rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]⟩
  have : IsIso ((Over.forget _).map (familyHom A hy).hom.hom) := by
    change IsIso (familyHom A hy).hom.hom.left
    rw [familyHom_left]
    exact h2
  have : IsIso (familyHom A hy).hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  Grp.mkIso' (asIso (familyHom A hy).hom.hom)

end HopfPrimitive

namespace RelativeRoot

/-- **Smooth connected commutative groups killed by `p` are vector groups.** Over an
algebraically closed field of characteristic `p`, every smooth connected commutative affine
group scheme whose points on every test scheme are killed by `p` is a vector group. -/
theorem smoothCommutativePTorsionVector : SmoothCommutativePTorsionVectorStatement.{u} := by
  intro k _ _ p _ _ G hSmooth hAff hConn htors
  have : IsAffineHom G.X.hom := hAff
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let A := AffineCoordinates.hopfAlgebra G.toGrp
  let e := AffineCoordinates.hopfSpecIso G.toGrp
  have hSm := smooth_hom_of_iso e hSmooth
  have hC := connectedSpace_left_of_iso e hConn
  have : Algebra.Smooth (CommRingCat.of k) A :=
    (Langlands.Algebra.GradedHopf.smooth_hopfSpec_iff _).1 hSm
  have : Algebra.FiniteType k A :=
    inferInstanceAs (Algebra.FiniteType (CommRingCat.of k) A)
  have : IsDomain A := Langlands.Algebra.GradedHopf.isDomain_of_hopfSpec A hSm hC
  let Y := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))
  let f : Y ⟶ G.X := e.hom.hom.hom
  have : IsMonHom f := e.hom.hom.isMonHom_hom
  have hgf : e.inv.hom.hom ≫ f = 𝟙 G.X := congrArg (fun φ => φ.hom.hom) e.inv_hom_id
  have hfg : f ≫ e.inv.hom.hom = 𝟙 Y := congrArg (fun φ => φ.hom.hom) e.hom_inv_id
  have : IsIso f := ⟨e.inv.hom.hom, hfg, hgf⟩
  have : Coalgebra.IsCocomm k A := isCocomm_of_commute A fun a b => by
    apply (cancel_mono f).1
    rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]
  have hA : ∀ φ : A →ₐ[k] k, toConv φ.toLinearMap ^ p = 1 := by
    intro φ
    have hx : Spec.mapMulEquiv (R := k) (S := A) (T := k) (toConv φ ^ p) = 1 := by
      rw [map_pow]
      apply (cancel_mono f).1
      rw [MonObj.pow_comp, htors, MonObj.one_comp]
    have hp : toConv φ ^ p = 1 :=
      (Spec.mapMulEquiv (R := k) (S := A) (T := k)).injective (by rw [hx, map_one])
    have := AlgHom.toLinearMap_convPow (toConv φ) p
    rw [hp, AlgHom.toLinearMap_convOne] at this
    exact this.symm
  obtain ⟨s, y, hy, hbij⟩ :=
    Langlands.Algebra.PTorsionHopf.exists_primitive_polynomial_coordinates p hA
  exact ⟨s, isVectorGroupOfDimension_iff_nonempty_iso.2
    ⟨e.symm ≪≫ HopfPrimitive.isoVectorGroup A hy hbij⟩⟩

end RelativeRoot

end Langlands.GroupScheme

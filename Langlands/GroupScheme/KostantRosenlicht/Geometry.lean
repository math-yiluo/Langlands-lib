import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.SchemeAction

/-! # Orbit maps of affine group schemes on affine schemes, in coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.KostantRosenlicht

open AffineLinearEmbedding

variable {R : CommRingCat.{u}}

/-- The structure morphism of `Spec C` to the spectrum of the base algebra itself. -/
def toBase (C : CommAlgCat.{u} R) :
    (algSpec R).obj (op C) ⟶ (algSpec R).obj (op (CommAlgCat.of R R)) :=
  (algSpec R).map (CommAlgCat.ofHom (Algebra.ofId R C)).op

/-- Every morphism of affine spectra is compatible with the structure morphisms. -/
@[reassoc]
theorem comp_toBase {C D : CommAlgCat.{u} R}
    (w : (algSpec R).obj (op D) ⟶ (algSpec R).obj (op C)) : w ≫ toBase C = toBase D := by
  obtain ⟨f, rfl⟩ := algSpec.fullyFaithful.map_surjective w
  rw [toBase, toBase, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  ext : 1
  exact Subsingleton.elim _ _

variable {U : GroupScheme (Spec R)} {B : CommAlgCat.{u} R}
  (j : (algSpec R).obj (op B) ≅ U.X) {X : Over (Spec R)} (a : SchemeAction U X)
  {A : CommAlgCat.{u} R} (jX : (algSpec R).obj (op A) ≅ X) (x : 𝟙_ (Over (Spec R)) ⟶ X)

/-- The inverted orbit map `u ↦ u⁻¹ • x`. -/
def invOrbit : U.X ⟶ X :=
  a.act (𝟙 U.X)⁻¹ (toUnit U.X ≫ x)

theorem comp_invOrbit {T : Over (Spec R)} (w : T ⟶ U.X) :
    w ≫ invOrbit a x = a.act w⁻¹ (toUnit T ≫ x) := by
  rw [invOrbit, SchemeAction.naturality, GrpObj.comp_inv, Category.comp_id,
    ← Category.assoc, comp_toUnit]

/-- The orbit map is the inverted orbit map precomposed with inversion. -/
theorem orbit_eq_inv_comp_invOrbit :
    a.act (𝟙 U.X) (toUnit U.X ≫ x) = (𝟙 U.X)⁻¹ ≫ invOrbit a x := by
  rw [comp_invOrbit, inv_inv]

/-- The comorphism of the inverted orbit map on coordinate algebras. -/
def coordMap : A ⟶ B :=
  (algSpec.fullyFaithful.preimage (j.hom ≫ invOrbit a x ≫ jX.inv)).unop

theorem algSpec_map_coordMap :
    (algSpec R).map (coordMap j a jX x).op = j.hom ≫ invOrbit a x ≫ jX.inv := by
  simp [coordMap]

/-- The comorphism of left translation by `g⁻¹` on `X`, for a point `g` of `U` over the base. -/
def leftTranslate (g : (algSpec R).obj (op (CommAlgCat.of R R)) ⟶ U.X) : A ⟶ A :=
  (algSpec.fullyFaithful.preimage (a.act (toBase A ≫ g⁻¹) jX.hom ≫ jX.inv)).unop

theorem algSpec_map_leftTranslate (g : (algSpec R).obj (op (CommAlgCat.of R R)) ⟶ U.X) :
    (algSpec R).map (leftTranslate a jX g).op = a.act (toBase A ≫ g⁻¹) jX.hom ≫ jX.inv := by
  simp [leftTranslate]

/-- The point of `U` over the base classified by an algebra map `v : B → R`. -/
def basePoint (v : B →ₐ[R] R) : (algSpec R).obj (op (CommAlgCat.of R R)) ⟶ U.X :=
  (algSpec R).map (CommAlgCat.ofHom v).op ≫ j.hom

/-- The coordinate right translation of the corepresentation of `U` by `B` is right
multiplication by the classified point. -/
theorem algSpec_map_rightTranslate_comp (v : B →ₐ[R] R) :
    (algSpec R).map (CommAlgCat.ofHom ((Algebra.TensorProduct.productMap (AlgHom.id R B)
        ((Algebra.ofId R B).comp v)).comp (comul (corepresentableBy U j)))).op ≫ j.hom =
      j.hom * (toBase B ≫ basePoint j v) := by
  have h := pt_productMap_comp_comul (corepresentableBy U j) (A := B) (AlgHom.id R B)
    ((Algebra.ofId R B).comp v)
  change _ = ((algSpec R).map (CommAlgCat.ofHom (AlgHom.id R B)).op ≫ j.hom) *
    ((algSpec R).map (CommAlgCat.ofHom ((Algebra.ofId R B).comp v)).op ≫ j.hom) at h
  refine Eq.trans h ?_
  rw [CommAlgCat.ofHom_id, op_id, CategoryTheory.Functor.map_id, Category.id_comp, basePoint, toBase,
    ← Category.assoc, ← Functor.map_comp, ← op_comp]
  rfl

/-- Right translation by a point of `U` over the base corresponds, through the inverted
orbit map, to left translation by its inverse on `X`. -/
theorem coordMap_comp_rightTranslate (v : B →ₐ[R] R) :
    coordMap j a jX x ≫ CommAlgCat.ofHom ((Algebra.TensorProduct.productMap (AlgHom.id R B)
        ((Algebra.ofId R B).comp v)).comp (comul (corepresentableBy U j))) =
      leftTranslate a jX (basePoint j v) ≫ coordMap j a jX x := by
  apply Quiver.Hom.op_inj
  apply algSpec.fullyFaithful.map_injective
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp, algSpec_map_leftTranslate,
    ← cancel_mono jX.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [SchemeAction.naturality, comp_toBase_assoc, algSpec_map_coordMap]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, algSpec_map_rightTranslate_comp, comp_invOrbit, comp_invOrbit,
    ← SchemeAction.act_mul, mul_inv_rev, GrpObj.comp_inv]
  rfl

/-- Closedness of the range of the orbit map follows from closedness of the range of the
comorphism `coordMap` on prime spectra. -/
theorem isClosed_range_orbit
    (h : IsClosed (Set.range (PrimeSpectrum.comap (coordMap j a jX x).hom.toRingHom))) :
    IsClosed (Set.range (a.act (𝟙 U.X) (toUnit U.X ≫ x)).left) := by
  have hinv : (𝟙 U.X)⁻¹ ≫ (𝟙 U.X)⁻¹ = 𝟙 U.X := by
    rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
  have : IsIso ((𝟙 U.X)⁻¹) := ⟨⟨(𝟙 U.X)⁻¹, hinv, hinv⟩⟩
  have : IsIso ((𝟙 U.X)⁻¹ ≫ j.inv).left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((𝟙 U.X)⁻¹ ≫ j.inv)))
  have : IsIso jX.hom.left := inferInstanceAs (IsIso ((Over.forget _).map jX.hom))
  have heq : a.act (𝟙 U.X) (toUnit U.X ≫ x) =
      ((𝟙 U.X)⁻¹ ≫ j.inv) ≫ (algSpec R).map (coordMap j a jX x).op ≫ jX.hom := by
    rw [orbit_eq_inv_comp_invOrbit, algSpec_map_coordMap]
    simp
  rw [heq]
  change IsClosed (Set.range (jX.hom.left.homeomorph ∘ (((algSpec R).map (coordMap j a jX x).op).left ∘
    ((𝟙 U.X)⁻¹ ≫ j.inv).left.homeomorph)))
  rw [Set.range_comp, (((𝟙 U.X)⁻¹ ≫ j.inv).left.homeomorph.surjective).range_comp]
  exact jX.hom.left.homeomorph.isClosedMap _ h

end Langlands.GroupScheme.KostantRosenlicht

import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.TauCeti.Algebra.AlgebraicGroup.Hopf.CentralPoint

/-! # Hopf spectrum points for the Cartier pairing -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite WithConv
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}}

/-- The relative spectrum of the supplied commutative algebra. -/
abbrev specOver (R : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra R B] : Over (Spec R) :=
  (algSpec R).obj (op (CommAlgCat.of R B))

/-- The morphism on relative spectra induced by an algebra map. -/
abbrev specMap {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (f : B →ₐ[R] C) : specOver R C ⟶ specOver R B :=
  (algSpec R).map (CommAlgCat.ofHom f).op

theorem specMap_comp {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D] (f : B →ₐ[R] C) (g : C →ₐ[R] D) :
    specMap (g.comp f) = specMap g ≫ specMap f :=
  (algSpec R).map_comp (CommAlgCat.ofHom g).op (CommAlgCat.ofHom f).op

/-- The algebra of global sections with its relative structure map. -/
abbrev sections (T : Over (Spec R)) := ((algΓ R).obj T).unop

/-- Pullback of relative global sections. -/
abbrev sectionsMap {T V : Over (Spec R)} (a : V ⟶ T) : sections T →ₐ[R] sections V :=
  ((algΓ R).map a).unop.hom

/-- Global sections of a relative spectrum recover its scalar algebra. -/
def sectionsSpec (R : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra R B] :
    sections (specOver R B) ≃ₐ[R] B :=
  { (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv with
    commutes' := fun r => by
      let f : R ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap R B)
      have h : (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of B)).hom = f := by
        rw [Scheme.ΓSpecIso_naturality f, Iso.inv_hom_id_assoc]
      exact ConcreteCategory.congr_hom h r }

theorem sectionsSpec_naturality {B C : Type u} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (f : B →ₐ[R] C) (x : sections (specOver R B)) :
    sectionsSpec R C (sectionsMap (specMap f) x) = f (sectionsSpec R B x) := by
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f.toRingHom)) x

/-- The relative spectrum adjunction written with unbundled algebra homomorphisms. -/
def specHomEquiv (T : Over (Spec R)) (B : Type u) [CommRing B] [Algebra R B] :
    (B →ₐ[R] sections T) ≃ (T ⟶ specOver R B) :=
  (show (B →ₐ[R] sections T) ≃ (((algΓ R).obj T) ⟶ op (CommAlgCat.of R B)) from
    { toFun := fun f => (CommAlgCat.ofHom f).op
      invFun := fun f => f.unop.hom
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans ((algΓAlgSpecAdjunction R).homEquiv _ _)

theorem specHomEquiv_apply (T : Over (Spec R)) (B : Type u) [CommRing B] [Algebra R B]
    (f : B →ₐ[R] sections T) :
    specHomEquiv T B f = (algΓAlgSpecAdjunction R).unit.app T ≫ specMap f :=
  Adjunction.homEquiv_unit (algΓAlgSpecAdjunction R) T (op (CommAlgCat.of R B))
    (CommAlgCat.ofHom f).op

theorem specHomEquiv_naturality {T V : Over (Spec R)} (a : V ⟶ T) {B : Type u}
    [CommRing B] [Algebra R B] (x : T ⟶ specOver R B) :
    (specHomEquiv V B).symm (a ≫ x) = (sectionsMap a).comp ((specHomEquiv T B).symm x) := by
  change (((algΓAlgSpecAdjunction R).homEquiv _ _).symm (a ≫ x)).unop.hom = _
  rw [Adjunction.homEquiv_naturality_left_symm]
  rfl

theorem specHomEquiv_postcomp {T : Over (Spec R)} {B C : Type u} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (x : T ⟶ specOver R C) (f : B →ₐ[R] C) :
    (specHomEquiv T B).symm (x ≫ specMap f) = ((specHomEquiv T C).symm x).comp f := by
  change (((algΓAlgSpecAdjunction R).homEquiv _ _).symm (x ≫ specMap f)).unop.hom = _
  rw [Adjunction.homEquiv_naturality_right_symm]
  rfl

theorem specHomEquiv_specMap {B C : Type u} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (f : B →ₐ[R] C) :
    (specHomEquiv (specOver R C) B).symm (specMap f) =
      (sectionsSpec R C).symm.toAlgHom.comp f := by
  rw [← Category.id_comp (specMap f), specHomEquiv_postcomp]
  change (((algΓAlgSpecAdjunction R).homEquiv _ _).symm (𝟙 (specOver R C))).unop.hom.comp f = _
  rw [Adjunction.homEquiv_counit, (algΓ R).map_id (specOver R C), Category.id_comp]
  rfl

section HopfSpectrum

variable (R) (A : Type u) [CommRing A] [HopfAlgebra R A]

local instance : GrpObj (specOver R A) :=
  ((hopfSpec R).obj (op (CommHopfAlgCat.of R A))).grp

/-- Spectrum of a cocommutative Hopf algebra as an actual commutative group scheme. -/
def specGroup [Coalgebra.IsCocomm R A] : CommGroupScheme (Spec R) :=
  { (hopfSpec R).obj (op (CommHopfAlgCat.of R A)) with
    comm := inferInstanceAs (IsCommMonObj ((Spec (CommRingCat.of A)).asOver (Spec R))) }

/-- The convolution point group on global functions is the actual point group of the spectrum. -/
def specPoints (T : Over (Spec R)) :
    (T ⟶ specOver R A) ≃* WithConv (A →ₐ[R] sections T) :=
  (show WithConv (A →ₐ[R] sections T) ≃* (T ⟶ specOver R A) from
    { (WithConv.equiv _).trans (specHomEquiv T A) with
      map_mul' := fun x y => by
        change specHomEquiv T A (x * y).ofConv =
          specHomEquiv T A x.ofConv * specHomEquiv T A y.ofConv
        rw [specHomEquiv_apply, specHomEquiv_apply, specHomEquiv_apply]
        change (algΓAlgSpecAdjunction R).unit.app T ≫ Spec.mapMulEquiv (x * y) =
          ((algΓAlgSpecAdjunction R).unit.app T ≫ Spec.mapMulEquiv x) *
            ((algΓAlgSpecAdjunction R).unit.app T ≫ Spec.mapMulEquiv y)
        rw [map_mul, MonObj.comp_mul] }).symm

theorem specPoints_apply (T : Over (Spec R)) (x : T ⟶ specOver R A) :
    specPoints R A T x = toConv ((specHomEquiv T A).symm x) := rfl

theorem specPoints_naturality {T V : Over (Spec R)} (a : V ⟶ T)
    (x : T ⟶ specOver R A) :
    specPoints R A V (a ≫ x) = toConv ((sectionsMap a).comp (specPoints R A T x).ofConv) := by
  simp only [specPoints_apply, specHomEquiv_naturality, ofConv_toConv]

theorem specPoints_specMap {C : Type u} [CommRing C] [Algebra R C] (f : A →ₐ[R] C) :
    specPoints R A (specOver R C) (specMap f) =
      toConv ((sectionsSpec R C).symm.toAlgHom.comp f) := by
  rw [specPoints_apply, specHomEquiv_specMap]

end HopfSpectrum

/-- The affine Hopf coordinates of an actual commutative group scheme are cocommutative. -/
theorem affineCoordinates_isCocomm (G : CommGroupScheme (Spec R)) [IsAffine G.X.left] :
    Coalgebra.IsCocomm R (AffineCoordinates.hopfAlgebra G.toGrp) := by
  let A := AffineCoordinates.hopfAlgebra G.toGrp
  let T := specOver R (A ⊗[R] A)
  let i : WithConv (A →ₐ[R] A ⊗[R] A) ≃* (T ⟶ G.X) :=
    (Spec.mapMulEquiv (R := R) (S := A) (T := A ⊗[R] A)).trans
    ((yonedaGrp.mapIso (AffineCoordinates.hopfSpecIso G.toGrp)).app (op T)).groupIsoToMulEquiv
  apply (TauCeti.HopfAlgebra.commute_includeLeft_includeRight_iff_isCocomm R A).mp
  apply i.injective
  rw [map_mul, map_mul, mul_comm]

end Langlands.GroupScheme.Cartier.FiniteDual

import Langlands.Geometry.FormalGroup.CoefficientCoherence
import Langlands.Geometry.FormalGroup.NilpotentAlgebras

/-! # Coherent Hom functors on coefficient algebras -/

noncomputable section

universe u v w x

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Extend a formal O-module along the structural map of an R-algebra. -/
abbrev overAlgebra (M : ModuleLaw O R σ) (A : CommAlgCat.{w} R) :=
  M.map (IsScalarTower.toAlgHom O R A)

/-- The O-algebra map underlying a morphism of coefficient R-algebras. -/
def coefficientAlgHom {A B : CommAlgCat.{w} R} (φ : A ⟶ B) : A →ₐ[O] B :=
  φ.hom.restrictScalars O

/-- The two structural coefficient extensions are identified by identity coordinates. -/
def overAlgebraIso (M : ModuleLaw O R σ) {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    Iso ((M.overAlgebra A).map (coefficientAlgHom φ)) (M.overAlgebra B) :=
  Iso.ofIdenticalCoordinates
    (by
      change (M.groupLaw.addition.map (algebraMap R A)).map φ.hom.toRingHom =
        M.groupLaw.addition.map (algebraMap R B)
      rw [CoordinateMap.map_ringHom_comp]
      exact congrArg (fun g => M.groupLaw.addition.map g) (RingHom.ext φ.hom.commutes))
    (fun a => by
      change ((M.action a).toCoordinateMap.map (algebraMap R A)).map φ.hom.toRingHom =
        (M.action a).toCoordinateMap.map (algebraMap R B)
      rw [CoordinateMap.map_ringHom_comp]
      exact congrArg (fun g => (M.action a).toCoordinateMap.map g)
        (RingHom.ext φ.hom.commutes))

namespace Hom

/-- Actual formal homomorphism restriction along an R-algebra map, with the
canonical identity-coordinate comparisons incorporated. -/
def algebraMapLinear {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    Hom (M.overAlgebra A) (N.overAlgebra A) →ₗ[O]
      Hom (M.overAlgebra B) (N.overAlgebra B) where
  toFun f := (N.overAlgebraIso φ).hom.comp
    ((f.map (coefficientAlgHom φ)).comp (M.overAlgebraIso φ).inv)
  map_add' f g := by
    simp only [show (f + g).map (coefficientAlgHom φ) =
      f.map (coefficientAlgHom φ) + g.map (coefficientAlgHom φ) from
        (mapLinear (coefficientAlgHom φ)).map_add f g, add_comp, comp_add]
  map_smul' a f := by
    simp only [show (a • f).map (coefficientAlgHom φ) =
      a • f.map (coefficientAlgHom φ) from
        (mapLinear (coefficientAlgHom φ)).map_smul a f, smul_comp, comp_smul,
      RingHom.id_apply]

@[simp]
theorem algebraMapLinear_coordinates {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : Hom (M.overAlgebra A) (N.overAlgebra A)) :
    (algebraMapLinear φ f).toHom.toCoordinateMap =
      f.toHom.toCoordinateMap.map φ.hom.toRingHom := by
  change CoordinateMap.id.comp
    ((f.toHom.toCoordinateMap.map φ.hom.toRingHom).comp CoordinateMap.id) = _
  rw [CoordinateMap.comp_id, CoordinateMap.id_comp]

@[simp]
theorem algebraMapLinear_id (A : CommAlgCat.{w} R)
    (f : Hom (M.overAlgebra A) (N.overAlgebra A)) : algebraMapLinear (𝟙 A) f = f := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  rw [algebraMapLinear_coordinates]
  exact CoordinateMap.map_ringHom_id _

@[simp]
theorem algebraMapLinear_comp {A B C : CommAlgCat.{w} R} (φ : A ⟶ B) (ψ : B ⟶ C)
    (f : Hom (M.overAlgebra A) (N.overAlgebra A)) :
    algebraMapLinear (φ ≫ ψ) f = algebraMapLinear ψ (algebraMapLinear φ f) := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  simp only [algebraMapLinear_coordinates, CoordinateMap.map_ringHom_comp]
  rfl

@[simp]
theorem algebraMapLinear_hom_id {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    algebraMapLinear φ (id (M.overAlgebra A)) = id (M.overAlgebra B) := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  rw [algebraMapLinear_coordinates]
  exact CoordinateMap.map_id _

@[simp]
theorem algebraMapLinear_hom_comp {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : Hom (N.overAlgebra A) (P.overAlgebra A))
    (f : Hom (M.overAlgebra A) (N.overAlgebra A)) :
    algebraMapLinear φ (g.comp f) = (algebraMapLinear φ g).comp (algebraMapLinear φ f) := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  rw [algebraMapLinear_coordinates]
  change (g.toHom.toCoordinateMap.comp f.toHom.toCoordinateMap).map φ.hom.toRingHom =
    ((algebraMapLinear φ g).toHom.toCoordinateMap).comp
      ((algebraMapLinear φ f).toHom.toCoordinateMap)
  rw [algebraMapLinear_coordinates, algebraMapLinear_coordinates, CoordinateMap.map_comp]

end Hom

/-- The O-module of actual formal homomorphisms on every coefficient algebra. -/
def algebraHomFunctor (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) :
    CommAlgCat.{w} R ⥤ ModuleCat.{w} O where
  obj A := ModuleCat.of O (Hom (M.overAlgebra A) (N.overAlgebra A))
  map φ := ModuleCat.ofHom (Hom.algebraMapLinear φ)
  map_id A := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact Hom.algebraMapLinear_id A
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact Hom.algebraMapLinear_comp φ ψ

namespace RationalHom

variable {F : Type x} [Field F] [Algebra O F]

/-- Coherent coefficient restriction of the actual tensor product Hom. -/
def algebraMapLinear {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    RationalHom F (M.overAlgebra A) (N.overAlgebra A) →ₗ[F]
      RationalHom F (M.overAlgebra B) (N.overAlgebra B) :=
  (Hom.algebraMapLinear φ).baseChange F

@[simp]
theorem algebraMapLinear_tmul {A B : CommAlgCat.{w} R} (φ : A ⟶ B) (a : F)
    (f : Hom (M.overAlgebra A) (N.overAlgebra A)) :
    algebraMapLinear φ (a ⊗ₜ[O] f) = a ⊗ₜ[O] Hom.algebraMapLinear φ f :=
  LinearMap.baseChange_tmul _ _ _

@[simp]
theorem algebraMapLinear_id (A : CommAlgCat.{w} R)
    (f : RationalHom F (M.overAlgebra A) (N.overAlgebra A)) :
    algebraMapLinear (𝟙 A) f = f := by
  induction f using TensorProduct.inductionOn with
  | tmul a f => simp only [algebraMapLinear_tmul, Hom.algebraMapLinear_id]
  | add f g hf hg => simp only [map_add, hf, hg]

@[simp]
theorem algebraMapLinear_comp {A B C : CommAlgCat.{w} R} (φ : A ⟶ B) (ψ : B ⟶ C)
    (f : RationalHom F (M.overAlgebra A) (N.overAlgebra A)) :
    algebraMapLinear (φ ≫ ψ) f = algebraMapLinear ψ (algebraMapLinear φ f) := by
  induction f using TensorProduct.inductionOn with
  | tmul a f => simp only [algebraMapLinear_tmul, Hom.algebraMapLinear_comp]
  | add f g hf hg => simp only [map_add, hf, hg]

@[simp]
theorem algebraMapLinear_ofHom {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : Hom (M.overAlgebra A) (N.overAlgebra A)) :
    algebraMapLinear φ (ofHom (F := F) f) = ofHom (Hom.algebraMapLinear φ f) :=
  algebraMapLinear_tmul φ 1 f

@[simp]
theorem algebraMapLinear_hom_id {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    algebraMapLinear φ (id (F := F) (M.overAlgebra A)) = id (M.overAlgebra B) := by
  simp only [id, algebraMapLinear_ofHom, Hom.algebraMapLinear_hom_id]

@[simp]
theorem algebraMapLinear_hom_comp {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : RationalHom F (N.overAlgebra A) (P.overAlgebra A))
    (f : RationalHom F (M.overAlgebra A) (N.overAlgebra A)) :
    algebraMapLinear φ (comp g f) = comp (algebraMapLinear φ g) (algebraMapLinear φ f) := by
  induction g using TensorProduct.inductionOn with
  | add g h hg hh => simp only [add_comp, map_add, hg, hh]
  | tmul a g =>
    induction f using TensorProduct.inductionOn with
    | add f h hf hh => simp only [comp_add, map_add, hf, hh]
    | tmul b f => simp only [comp_tmul, algebraMapLinear_tmul,
        Hom.algebraMapLinear_hom_comp]

end RationalHom

/-- Rational Hom is a genuine F-module-valued functor on coefficient algebras. -/
def rationalHomFunctor (F : Type x) [Field F] [Algebra O F]
    (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) :
    CommAlgCat.{w} R ⥤ ModuleCat.{max w x} F where
  obj A := ModuleCat.of F (RationalHom F (M.overAlgebra A) (N.overAlgebra A))
  map φ := ModuleCat.ofHom (RationalHom.algebraMapLinear φ)
  map_id A := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact RationalHom.algebraMapLinear_id A
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact RationalHom.algebraMapLinear_comp φ ψ

end Langlands.FormalGroup.ModuleLaw

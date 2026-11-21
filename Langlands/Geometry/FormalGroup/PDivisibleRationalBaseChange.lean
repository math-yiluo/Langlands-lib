import Langlands.Geometry.FormalGroup.PDivisibleBaseChange
import Langlands.Geometry.FormalGroup.PDivisibleRationalHom

/-! # Pullback of actual rational p-divisible group morphisms -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.PDivisibleGroup

open GroupScheme.HomScheme

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {p : ℕ} [Fact p.Prime]
variable {G H J : PDivisibleGroup (CommRingCat.of R) p}

/-- Pullback commutes with the natural p-adic scalar on an actual tower. -/
theorem baseChangeFunctor_map_padicAction (G : PDivisibleGroup (CommRingCat.of R) p) (a : ℤ_[p]) :
    (baseChangeFunctor R S p).map (G.padicAction a) = (G.baseChange (S := S)).padicAction a := by
  apply Hom.ext
  intro n
  let B := CommGroupScheme.baseChange (specBase R S)
  change B.map (G.levelPadicAction n a) = (G.baseChange (S := S)).levelPadicAction n a
  rw [G.levelPadicAction_eq_nsmul_of_le (le_refl n),
    (G.baseChange (S := S)).levelPadicAction_eq_nsmul_of_le (le_refl n), B.map_nsmul, B.map_id]
  rfl

/-- Pullback of integral morphisms is p-adic linear. -/
def Hom.baseChangeLinear : (G ⟶ H) →ₗ[ℤ_[p]] (G.baseChange (S := S) ⟶ H.baseChange (S := S)) where
  toFun f := (baseChangeFunctor R S p).map f
  map_add' f g := (baseChangeFunctor R S p).map_add (f := f) (g := g)
  map_smul' a f := by
    change (baseChangeFunctor R S p).map (a • f) = a • (baseChangeFunctor R S p).map f
    rw [smul_eq_comp_padicAction, smul_eq_comp_padicAction, Functor.map_comp,
      baseChangeFunctor_map_padicAction]
    rfl

namespace RationalHom

/-- Pull back the actual group schemes and extend their morphism map to the scalar tensor. -/
def baseChangeMap : RationalHom G H →ₗ[ℚ_[p]]
    RationalHom (G.baseChange (S := S)) (H.baseChange (S := S)) :=
  (Hom.baseChangeLinear (S := S)).baseChange ℚ_[p]

@[simp] theorem baseChangeMap_tmul (a : ℚ_[p]) (f : G ⟶ H) :
    baseChangeMap (S := S) (a ⊗ₜ[ℤ_[p]] f) = a ⊗ₜ[ℤ_[p]] (baseChangeFunctor R S p).map f :=
  rfl

@[simp] theorem baseChangeMap_ofHom (f : G ⟶ H) :
    baseChangeMap (S := S) (ofHom f) = ofHom ((baseChangeFunctor R S p).map f) := rfl

@[simp] theorem baseChangeMap_id (G : PDivisibleGroup (CommRingCat.of R) p) :
    baseChangeMap (S := S) (id G) = id (G.baseChange (S := S)) := by
  let F := baseChangeFunctor R S p
  have h : F.map (𝟙 G) = 𝟙 (G.baseChange (S := S)) := F.map_id G
  exact congrArg (ofHom (G := G.baseChange (S := S)) (H := G.baseChange (S := S))) h

@[simp] theorem baseChangeMap_comp (f : RationalHom G H) (g : RationalHom H J) :
    baseChangeMap (S := S) (comp f g) =
      comp (baseChangeMap (S := S) f) (baseChangeMap (S := S) g) := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp only [add_comp, map_add, hf, hf']
  | tmul a f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp only [comp_add, map_add, hg, hg']
    | tmul b g => simp only [comp_tmul, baseChangeMap_tmul, Functor.map_comp]

end RationalHom

/-- Pullback of actual p-divisible towers extends to their category up to isogeny. -/
def rationalBaseChangeFunctor (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : ℕ) [Fact p.Prime] : RationalCategory (CommRingCat.of R) p ⥤
      RationalCategory (CommRingCat.of S) p where
  obj G := RationalCategory.of (G.val.baseChange (S := S))
  map f := RationalHom.baseChangeMap f
  map_id G := RationalHom.baseChangeMap_id G.val
  map_comp f g := RationalHom.baseChangeMap_comp f g

instance : (rationalBaseChangeFunctor R S p).Additive where
  map_add {_ _ f g} := map_add (RationalHom.baseChangeMap (S := S)) f g

/-- An actual quasi-isogeny pulls back to the new affine base. -/
def QuasiIsogeny.baseChange (e : QuasiIsogeny G H) :
    QuasiIsogeny (G.baseChange (S := S)) (H.baseChange (S := S)) :=
  (rationalBaseChangeFunctor R S p).mapIso e

@[simp] theorem QuasiIsogeny.baseChange_hom (e : QuasiIsogeny G H) :
    (e.baseChange (S := S)).hom = RationalHom.baseChangeMap (S := S) e.hom := rfl

end Langlands.PDivisibleGroup

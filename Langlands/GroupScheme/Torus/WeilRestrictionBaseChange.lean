import Langlands.GroupScheme.Torus.WeilRestriction
import Langlands.GroupScheme.Torus.Split

/-! # Base change of the Weil restriction `Res_{B/A} 𝔾ₘ` -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.WeilGm

/-! ### The algebraic comparison -/

section Algebraic

variable (A A' B R : Type u) [CommRing A] [CommRing A'] [CommRing B] [CommRing R]
  [Algebra A A'] [Algebra A B] [Algebra A' R] [Algebra A R] [IsScalarTower A A' R]

/-- The canonical ring isomorphism `B ⊗[A] R ≃ (A' ⊗[A] B) ⊗[A'] R` for an `A'`-algebra `R`,
sending `b ⊗ r` to `(1 ⊗ b) ⊗ r`. -/
def baseChangeTensorEquiv : B ⊗[A] R ≃+* (A' ⊗[A] B) ⊗[A'] R :=
  (Algebra.TensorProduct.comm A B R).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange A A' R R B).symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm A' R (A' ⊗[A] B)).toRingEquiv)

@[simp] theorem baseChangeTensorEquiv_tmul (b : B) (r : R) :
    baseChangeTensorEquiv A A' B R (b ⊗ₜ r) = ((1 : A') ⊗ₜ b) ⊗ₜ r := by
  simp [baseChangeTensorEquiv]

/-- The isomorphism is `R`-linear for the action of `R` on the right tensor factors. -/
theorem baseChangeTensorEquiv_mul_tmul (x : B ⊗[A] R) (r : R) :
    baseChangeTensorEquiv A A' B R (x * (1 ⊗ₜ r)) =
      baseChangeTensorEquiv A A' B R x * (1 ⊗ₜ r) := by
  rw [map_mul, baseChangeTensorEquiv_tmul, Algebra.TensorProduct.one_def]

/-- The isomorphism commutes with every map of `A'`-algebras `R → R'`; `ψ` is the same map
regarded as a map of `A`-algebras. -/
theorem baseChangeTensorEquiv_natural {R' : Type u} [CommRing R'] [Algebra A' R'] [Algebra A R']
    [IsScalarTower A A' R'] (φ : R →ₐ[A'] R') (ψ : R →ₐ[A] R') (h : ∀ r, ψ r = φ r)
    (w : B ⊗[A] R) :
    baseChangeTensorEquiv A A' B R' (Algebra.TensorProduct.lTensor (S := B) B ψ w) =
      Algebra.TensorProduct.lTensor (S := A' ⊗[A] B) (A' ⊗[A] B) φ
        (baseChangeTensorEquiv A A' B R w) := by
  induction w using TensorProduct.inductionOn with
  | tmul b r => simp [h]
  | add w w' hw hw' => simp only [map_add, hw, hw']

end Algebraic

/-! ### The group-scheme isomorphism -/

section Scheme

variable (A A' : CommRingCat.{u}) [Algebra A A'] (B : Type u) [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The morphism of affine bases induced by the algebra structure of `A'`. -/
abbrev baseMap : Spec A' ⟶ Spec A :=
  Spec.map (CommRingCat.ofHom (algebraMap A A'))

/-- Global sections of a test scheme over `Spec A'`, as an `A`-algebra through `Spec A`. -/
abbrev restrictedSections (T : Over (Spec A')) : CommAlgCat A :=
  ((algΓ A).obj ((Over.map (baseMap A A')).obj T)).unop

/-- The `A'`-algebra structure of the restricted global sections. -/
instance restrictedSectionsAlgebra (T : Over (Spec A')) :
    Algebra A' (restrictedSections A A' T) :=
  inferInstanceAs (Algebra A' ((algΓ A').obj T).unop)

instance restrictedSectionsScalarTower (T : Over (Spec A')) :
    IsScalarTower A A' (restrictedSections A A' T) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro r
  change (T.hom ≫ baseMap A A').appTop ((Scheme.ΓSpecIso A).inv r) =
    T.hom.appTop ((Scheme.ΓSpecIso A').inv (algebraMap A A' r))
  rw [Scheme.Hom.comp_appTop]
  exact congrArg T.hom.appTop
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap A A'))) r).symm

/-- Points of the base change of `Res_{B/A} 𝔾ₘ` are units of `(A' ⊗[A] B) ⊗[A'] Γ(T)`. -/
def basePointsEquiv (T : Over (Spec A')) :
    (T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (groupScheme A B)).X) ≃*
      ((A' ⊗[A] B) ⊗[A'] ((algΓ A').obj T).unop)ˣ :=
  (GroupScheme.baseChangePointsEquiv (baseMap A A') (groupScheme A B) T).trans
    ((pointsEquiv A B ((Over.map (baseMap A A')).obj T)).trans
      (Units.mapEquiv (baseChangeTensorEquiv A A' B (restrictedSections A A' T)).toMulEquiv))

theorem basePointsEquiv_apply (T : Over (Spec A'))
    (x : T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (groupScheme A B)).X) :
    basePointsEquiv A A' B T x =
      Units.map (baseChangeTensorEquiv A A' B (restrictedSections A A' T)).toMonoidHom
        (pointsEquiv A B ((Over.map (baseMap A A')).obj T)
          (GroupScheme.baseChangePointsEquiv (baseMap A A') (groupScheme A B) T x)) :=
  rfl

/-- The point model of the base change is natural in the test scheme. -/
theorem basePointsEquiv_naturality {T T' : Over (Spec A')} (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (groupScheme A B)).X) :
    basePointsEquiv A A' B T' (a ≫ x) =
      Units.map (Algebra.TensorProduct.lTensor (S := A' ⊗[A] B) (A' ⊗[A] B)
        ((algΓ A').map a).unop.hom : (A' ⊗[A] B) ⊗[A'] _ →* (A' ⊗[A] B) ⊗[A'] _)
        (basePointsEquiv A A' B T x) := by
  apply Units.ext
  rw [basePointsEquiv_apply, basePointsEquiv_apply,
    GroupScheme.baseChangePointsEquiv_naturality, pointsEquiv_naturality]
  set_option backward.isDefEq.respectTransparency false in
  exact baseChangeTensorEquiv_natural A A' B (restrictedSections A A' T)
    (R' := restrictedSections A A' T')
    ((algΓ A').map a).unop.hom ((algΓ A).map ((Over.map (baseMap A A')).map a)).unop.hom
    (fun _ => rfl) _

/-- Base change of `Res_{B/A} 𝔾ₘ` along `Spec A' → Spec A` is `Res_{(A' ⊗[A] B)/A'} 𝔾ₘ`. -/
def algebraBaseChangeIso :
    (GroupScheme.baseChange (baseMap A A')).obj (groupScheme A B) ≅
      groupScheme A' (A' ⊗[A] B) :=
  isoOfPointModels (fun T : Over (Spec A') => ((A' ⊗[A] B) ⊗[A'] ((algΓ A').obj T).unop)ˣ)
    (fun a => Units.map (Algebra.TensorProduct.lTensor (S := A' ⊗[A] B) (A' ⊗[A] B)
      ((algΓ A').map a).unop.hom : (A' ⊗[A] B) ⊗[A'] _ →* (A' ⊗[A] B) ⊗[A'] _))
    (basePointsEquiv A A' B) (pointsEquiv A' (A' ⊗[A] B))
    (fun a x => basePointsEquiv_naturality A A' B a x)
    (fun a y => pointsEquiv_naturality A' (A' ⊗[A] B) a y)

/-- On points, the isomorphism is the unit map of `B ⊗[A] Γ(T) ≃ (A' ⊗[A] B) ⊗[A'] Γ(T)`. -/
theorem algebraBaseChangeIso_hom_points (T : Over (Spec A'))
    (x : T ⟶ ((GroupScheme.baseChange (baseMap A A')).obj (groupScheme A B)).X) :
    pointsEquiv A' (A' ⊗[A] B) T (x ≫ (algebraBaseChangeIso A A' B).hom.hom.hom) =
      Units.map (baseChangeTensorEquiv A A' B (restrictedSections A A' T)).toMonoidHom
        (pointsEquiv A B ((Over.map (baseMap A A')).obj T)
          (GroupScheme.baseChangePointsEquiv (baseMap A A') (groupScheme A B) T x)) :=
  isoOfPointModels_hom (fun T : Over (Spec A') => ((A' ⊗[A] B) ⊗[A'] ((algΓ A').obj T).unop)ˣ)
    (fun a => Units.map (Algebra.TensorProduct.lTensor (S := A' ⊗[A] B) (A' ⊗[A] B)
      ((algΓ A').map a).unop.hom : (A' ⊗[A] B) ⊗[A'] _ →* (A' ⊗[A] B) ⊗[A'] _))
    (basePointsEquiv A A' B) (pointsEquiv A' (A' ⊗[A] B))
    (fun a x => basePointsEquiv_naturality A A' B a x)
    (fun a y => pointsEquiv_naturality A' (A' ⊗[A] B) a y) T x

end Scheme

/-! ### Base change along a ring map -/

variable {A A' : CommRingCat.{u}} (f : A ⟶ A') (B : Type u) [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- Base change of `Res_{B/A} 𝔾ₘ` along `Spec f` is `Res_{(A' ⊗[A] B)/A'} 𝔾ₘ`, where `A'` is an
`A`-algebra through `f`. -/
def baseChangeIso :
    letI := f.hom.toAlgebra
    (GroupScheme.baseChange (Spec.map f)).obj (groupScheme A B) ≅
      groupScheme A' (A' ⊗[A] B) :=
  letI := f.hom.toAlgebra
  algebraBaseChangeIso A A' B

/-- `baseChangeIso f B` and `algebraBaseChangeIso` have the same effect on points; the two
sides differ only in writing `Spec.map f` or `baseMap A A'`. -/
private theorem baseChangeIso_points_eq (T : Over (Spec A'))
    (x : T ⟶ ((GroupScheme.baseChange (Spec.map f)).obj (groupScheme A B)).X) :
    letI := f.hom.toAlgebra
    pointsEquiv A' (A' ⊗[A] B) T (x ≫ (baseChangeIso f B).hom.hom.hom) =
      pointsEquiv A' (A' ⊗[A] B) T (x ≫ (algebraBaseChangeIso A A' B).hom.hom.hom) :=
  rfl

/-- The point model of the base change along `Spec.map f` agrees with the one along
`baseMap A A'`. -/
private theorem basePoints_specMap_eq (T : Over (Spec A'))
    (x : T ⟶ ((GroupScheme.baseChange (Spec.map f)).obj (groupScheme A B)).X) :
    letI := f.hom.toAlgebra
    Units.map (baseChangeTensorEquiv A A' B (restrictedSections A A' T)).toMonoidHom
        (pointsEquiv A B ((Over.map (Spec.map f)).obj T)
          (GroupScheme.baseChangePointsEquiv (Spec.map f) (groupScheme A B) T x)) =
      Units.map (baseChangeTensorEquiv A A' B (restrictedSections A A' T)).toMonoidHom
        (pointsEquiv A B ((Over.map (baseMap A A')).obj T)
          (GroupScheme.baseChangePointsEquiv (baseMap A A') (groupScheme A B) T x)) :=
  rfl

/-- On the points over `T`, `baseChangeIso f B` is the unit map of the canonical isomorphism
`B ⊗[A] Γ(T) ≃ (A' ⊗[A] B) ⊗[A'] Γ(T)`. -/
theorem baseChangeIso_hom_points (T : Over (Spec A'))
    (x : T ⟶ ((GroupScheme.baseChange (Spec.map f)).obj (groupScheme A B)).X) :
    letI := f.hom.toAlgebra
    pointsEquiv A' (A' ⊗[A] B) T (x ≫ (baseChangeIso f B).hom.hom.hom) =
      Units.map (baseChangeTensorEquiv A A' B (restrictedSections A A' T)).toMonoidHom
        (pointsEquiv A B ((Over.map (Spec.map f)).obj T)
          (GroupScheme.baseChangePointsEquiv (Spec.map f) (groupScheme A B) T x)) := by
  let _ := f.hom.toAlgebra
  rw [baseChangeIso_points_eq f B T x, algebraBaseChangeIso_hom_points A A' B T x]
  exact (basePoints_specMap_eq f B T x).symm

end Langlands.GroupScheme.WeilGm

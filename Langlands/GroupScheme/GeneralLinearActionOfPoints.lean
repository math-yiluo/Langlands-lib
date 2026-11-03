import Langlands.AlgebraicGeometry.AffinePointGluing
import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.SchemeActionOfPointLaws

/-! # Actions of `GL_n` from natural actions on affine points

Over `Spec R`, an action of the groups `GL_n(A)` on the `A`-points of a scheme `X`, natural in
the `R`-algebra `A` and satisfying the identity and multiplication laws, comes from an actual
scheme action of the general linear group scheme. On an affine point `x` and a point `h` of
`GL_n` over the same `R`-algebra `A`, the scheme action is the given action of the matrix of `h`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Langlands.AlgebraicGeometry.AffinePoints
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n] {R : Type u} [CommRing R]

section Matrix

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The matrix over `A` of a point of `GL_n` on the affine test scheme `Spec A`. -/
def matrixOf (h : specOver (R := R) A ⟶ (groupScheme n (CommRingCat.of R)).X) : GL n A :=
  Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    (pointsEquiv n _ _ h)

theorem matrixOf_injective :
    Function.Injective (matrixOf (n := n) (R := R) (A := A)) := by
  intro h h' e
  refine (pointsEquiv n _ _).injective (Units.ext (Matrix.ext fun i j => ?_))
  have := congrArg (fun g : GL n A => (g : Matrix n n A) i j) e
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective this

@[simp] theorem matrixOf_one :
    matrixOf (1 : specOver (R := R) A ⟶ (groupScheme n (CommRingCat.of R)).X) = 1 := by
  rw [matrixOf, pointsEquiv_one, map_one]

@[simp] theorem matrixOf_mul (h h' : specOver (R := R) A ⟶ (groupScheme n (CommRingCat.of R)).X) :
    matrixOf (h * h') = matrixOf h * matrixOf h' := by
  rw [matrixOf, pointsEquiv_mul, map_mul]
  rfl

/-- The matrix of a point is natural in the `R`-algebra. -/
theorem matrixOf_comp {B : Type u} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (h : specOver (R := R) A ⟶ (groupScheme n (CommRingCat.of R)).X) :
    matrixOf (specMapOver φ ≫ h) = Matrix.GeneralLinearGroup.map φ.toRingHom (matrixOf h) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (pointsEquiv n _ _ (specMapOver φ ≫ h) i j) =
    φ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (pointsEquiv n _ _ h i j))
  rw [pointsEquiv_comp_apply, specMapOver_left]
  exact congrArg (fun f => f.hom (pointsEquiv n _ _ h i j))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom))

end Matrix

variable {X : Over (Spec (CommRingCat.of R))}

/-- An action of the groups `GL_n(A)` on the `A`-points of `X`, natural in the `R`-algebra `A`
and satisfying the identity and multiplication laws, is induced by a scheme action of `GL_n`. -/
theorem exists_schemeAction_of_affine
    (act : ∀ (A : Type u) [CommRing A] [Algebra R A], GL n A →
      (specOver (R := R) A ⟶ X) → (specOver (R := R) A ⟶ X))
    (hnat : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (φ : A →ₐ[R] B) (g : GL n A) (x : specOver (R := R) A ⟶ X),
      act B (Matrix.GeneralLinearGroup.map φ.toRingHom g) (specMapOver φ ≫ x) =
        specMapOver φ ≫ act A g x)
    (hone : ∀ (A : Type u) [CommRing A] [Algebra R A] (x : specOver (R := R) A ⟶ X),
      act A 1 x = x)
    (hmul : ∀ (A : Type u) [CommRing A] [Algebra R A] (g g' : GL n A)
      (x : specOver (R := R) A ⟶ X), act A (g * g') x = act A g (act A g' x)) :
    ∃ a : SchemeAction (groupScheme n (CommRingCat.of R)) X,
      ∀ (A : Type u) [CommRing A] [Algebra R A]
        (h : specOver (R := R) A ⟶ (groupScheme n (CommRingCat.of R)).X)
        (x : specOver (R := R) A ⟶ X), a.act h x = act A (matrixOf h) x := by
  let G := (groupScheme n (CommRingCat.of R)).X
  obtain ⟨f, hf⟩ := exists_over_hom (X := G ⊗ X) (Y := X)
    (fun A _ _ y => act A (matrixOf (y ≫ fst G X)) (y ≫ snd G X))
    (fun A B _ _ _ _ φ y => by
      simp only [Category.assoc]
      rw [matrixOf_comp, hnat])
  have hpt : ∀ (A : Type u) [CommRing A] [Algebra R A] (h : specOver (R := R) A ⟶ G)
      (x : specOver (R := R) A ⟶ X), lift h x ≫ f = act A (matrixOf h) x := by
    intro A _ _ h x
    rw [hf, lift_fst, lift_snd]
  refine ⟨schemeActionOfPointLaws f (fun x => ?_) (fun h h' x => ?_), fun A _ _ h x => hpt A h x⟩
  · refine over_hom_ext fun A _ _ z => ?_
    rw [← Category.assoc, comp_lift, MonObj.comp_one, hpt, matrixOf_one, hone]
  · refine over_hom_ext fun A _ _ z => ?_
    simp only [← Category.assoc, comp_lift, MonObj.comp_mul, hpt, matrixOf_mul, hmul]

end Langlands.GroupScheme.GeneralLinear

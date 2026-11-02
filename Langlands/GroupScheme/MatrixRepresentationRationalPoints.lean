import Langlands.GroupScheme.MatrixRepresentation

/-! # Rational-point matrices of actual group-scheme representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- A monomorphic representation is injective on the matrices of every test scheme. -/
theorem pointMatrix_injective (ρ : MatrixRepresentation G n) [Mono ρ.hom.hom]
    (T : Over (Spec R)) : Function.Injective (ρ.pointMatrix T) := by
  intro x y h
  apply (cancel_mono ρ.hom.hom).1
  exact (GeneralLinear.pointsEquiv n R T).injective h

/-- The matrix of an actual `R`-point, with entries in `R` through `Γ(Spec R, O) ≅ R`. -/
def rationalMatrix (ρ : MatrixRepresentation G n) :
    (Over.mk (𝟙 (Spec R)) ⟶ G.X) →* GL n R :=
  (Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso R).hom.hom).comp
    (ρ.pointMatrix (Over.mk (𝟙 (Spec R))))

@[simp] theorem rationalMatrix_apply (ρ : MatrixRepresentation G n)
    (x : Over.mk (𝟙 (Spec R)) ⟶ G.X) :
    ρ.rationalMatrix x =
      Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso R).hom.hom
        (GeneralLinear.pointsEquiv n R (Over.mk (𝟙 (Spec R))) (x ≫ ρ.hom.hom)) := rfl

/-- Each rational matrix entry is the pullback of the corresponding GL coordinate. -/
theorem rationalMatrix_apply_apply (ρ : MatrixRepresentation G n)
    (x : Over.mk (𝟙 (Spec R)) ⟶ G.X) (i j : n) :
    (ρ.rationalMatrix x : Matrix n n R) i j =
      (Scheme.ΓSpecIso R).hom
        ((x ≫ ρ.hom.hom).left.appTop (GeneralLinear.entrySection n R i j)) := by
  change (Scheme.ΓSpecIso R).hom
    (GeneralLinear.pointsEquiv n R _ (x ≫ ρ.hom.hom) i j) = _
  rw [GeneralLinear.pointsEquiv_apply_apply]

@[simp] theorem rationalMatrix_restrict (ρ : MatrixRepresentation G n) (f : H ⟶ G)
    (x : Over.mk (𝟙 (Spec R)) ⟶ H.X) :
    (ρ.restrict f).rationalMatrix x = ρ.rationalMatrix (x ≫ f.hom.hom) := by
  change Matrix.GeneralLinearGroup.map _ ((ρ.restrict f).pointMatrix _ x) = _
  rw [pointMatrix_restrict]
  rfl

/-- A monomorphic representation gives an injective homomorphism on actual rational points. -/
theorem rationalMatrix_injective (ρ : MatrixRepresentation G n) [Mono ρ.hom.hom] :
    Function.Injective ρ.rationalMatrix := by
  intro x y h
  apply pointMatrix_injective ρ (Over.mk (𝟙 (Spec R)))
  apply Units.ext
  ext i j
  apply (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
  exact congrArg (fun g : GL n R => g i j) h

end Langlands.GroupScheme.MatrixRepresentation

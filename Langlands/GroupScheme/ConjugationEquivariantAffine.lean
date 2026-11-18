import Langlands.GroupScheme.RestrictedAffinePointEndomorphism
import Langlands.GroupScheme.SubgroupFunctor

/-! # Conjugation equivariance detected on affine tests -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- A group-scheme endomorphism commutes with every conjugation on every
relative scheme test. -/
def IsConjugationEquivariant {S : Scheme.{u}} {G : GroupScheme S} (ψ : G ⟶ G) : Prop :=
  ∀ (T : Over S) (g x : T ⟶ G.X),
    (g * x * g⁻¹) ≫ ψ.hom.hom = g * (x ≫ ψ.hom.hom) * g⁻¹

/-- Conjugation equivariance makes the full pointwise image normal. -/
theorem IsConjugationEquivariant.range_isNormal {S : Scheme.{u}} {G : GroupScheme S}
    {ψ : G ⟶ G} (hψ : IsConjugationEquivariant ψ) :
    (SubgroupFunctor.range ψ).IsNormal := by
  intro T g z _ hz
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  exact SubgroupFunctor.mem_range.mpr ⟨g * x * g⁻¹, hψ T g x⟩

/-- For an affine group, all affine algebra tests detect full scheme-test
conjugation equivariance. -/
theorem IsConjugationEquivariant.of_affinePoints
    {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
    (ψ : G ⟶ G)
    (hψ : ∀ (A : CommAlgCat.{u} R) (g x : G.affinePoints A),
      (g * x * g⁻¹) ≫ ψ.hom.hom = g * (x ≫ ψ.hom.hom) * g⁻¹) :
    IsConjugationEquivariant ψ := by
  let H : GroupScheme (Spec R) := G ⊗ G
  have : IsAffine H.X.left := by
    change IsAffine (pullback G.X.hom G.X.hom)
    infer_instance
  let e := AffinePointComparison.presentation H
  have hu : (fst G.X G.X * snd G.X G.X * (fst G.X G.X)⁻¹) ≫ ψ.hom.hom =
      fst G.X G.X * (snd G.X G.X ≫ ψ.hom.hom) * (fst G.X G.X)⁻¹ := by
    apply (cancel_epi e.hom).mp
    simpa only [← Category.assoc, MonObj.comp_mul, GrpObj.comp_inv] using
      hψ _ (e.hom ≫ fst G.X G.X) (e.hom ≫ snd G.X G.X)
  intro T g x
  have h := congrArg (fun f : H.X ⟶ G.X => lift g x ≫ f) hu
  simpa only [← Category.assoc, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd] using h

namespace RestrictedAffinePoints

variable {R : Type u} [CommRing R] (T : CommAlgCat.{u} (CommRingCat.of R))
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  (θ : Under.forget T ⋙ G.affinePointFunctor ⟶
    Under.forget T ⋙ G.affinePointFunctor)

/-- Normality of the original transformation reconstructs conjugation
equivariance on all relative scheme tests, not only affine ones. -/
theorem endomorphism_conjugationEquivariant
    (hθ : ∀ (X : Under T)
      (g x : (Under.forget T ⋙ G.affinePointFunctor).obj X),
      θ.app X (g * x * g⁻¹) = g * θ.app X x * g⁻¹) :
    IsConjugationEquivariant (endomorphism T G θ) := by
  have : IsAffine ((baseChange (Spec.algebraMap R T)).obj G).X.left := by
    change IsAffine (pullback G.X.hom (Spec.algebraMap R T))
    infer_instance
  apply IsConjugationEquivariant.of_affinePoints
  intro X g x
  apply (pointsEquiv T G X).injective
  simpa only [endomorphism_points, map_mul, map_inv, MulEquiv.apply_symm_apply] using
    hθ ((induced T).obj X) (pointsEquiv T G X g) (pointsEquiv T G X x)

end RestrictedAffinePoints
end Langlands.GroupScheme

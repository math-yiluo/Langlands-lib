import Langlands.GroupScheme.Rational.PolynomialHomCentralDescent
import Langlands.GroupScheme.Rational.AffineLineRigidity

/-! # Central additive lines over algebraic Galois extensions of wound groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Affine-line constancy rules out central monomorphic standard additive
lines after any algebraic Galois scalar extension. -/
def WoundCentralGaloisStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    HasConstantAffineLineMaps G →
      ∀ (f : VectorGroup.groupScheme (CommRingCat.of L) 1 ⟶
        Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G)
        [Mono f.hom.hom], ¬ IsCentral f

namespace HasConstantAffineLineMaps

set_option backward.isDefEq.respectTransparency false

open PolynomialPoint

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "G_L" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G

/-- A central additive line over a finite Galois extension has zero tangent
when every ground-field affine-line morphism is constant. -/
theorem inputTangent_eq_zero_of_finiteGalois [IsAffine G.X.left]
    [FiniteDimensional k L] [IsGalois k L]
    (hG : HasConstantAffineLineMaps G)
    (f : VectorGroup.groupScheme (CommRingCat.of L) 1 ⟶ G_L)
    (hf : IsCentral f) (v : Fin 1 → k) : inputTangent k L G f v = 0 := by
  by_contra hv
  obtain ⟨a, ha⟩ := exists_normOfCentralHom_tangent_ne_zero k L G f hf v hv
  have hq := hG.hom_eq_zero_of_isVectorGroupOfDimension_one
    ⟨VectorGroup.coordinates (CommRingCat.of k) 1,
      VectorGroup.isNaturalVectorCoordinates⟩ (normOfCentralHom k L G f hf a)
  apply ha
  rw [hq]
  apply Additive.toMul.injective
  apply Subtype.ext
  exact MonObj.comp_one _

/-- An arbitrary algebraic Galois extension cannot create a central
monomorphic standard additive line in an affine, locally finite-type group
whose ground-field affine-line morphisms are all constant. -/
theorem not_isCentral_of_mono_galois [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [IsGalois k L]
    (hG : HasConstantAffineLineMaps G)
    (f : VectorGroup.groupScheme (CommRingCat.of L) 1 ⟶ G_L)
    [Mono f.hom.hom] : ¬ IsCentral f := by
  intro hf
  let D := finiteGaloisHomModel (k := k) (L := L) (G := G) f
  let v : Fin 1 → k := fun _ => 1
  have hv : inputTangent k L G f v ≠ 0 :=
    inputTangent_ne_zero k L G f v 0 one_ne_zero
  exact D.inputTangent_ne_zero v hv
    (inputTangent_eq_zero_of_finiteGalois hG D.hom (D.isCentral hf) v)

end HasConstantAffineLineMaps

/-- Central additive lines cannot arise over an algebraic Galois extension
of an affine group with affine-line constancy. -/
theorem woundCentralGalois : WoundCentralGaloisStatement := by
  intro k L _ _ _ _ G _ _ hG f _
  exact hG.not_isCentral_of_mono_galois f

end Langlands.GroupScheme

import Langlands.GroupScheme.Descent.Data
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.FieldTheory.Galois.Basic

/-! # Finite-Galois effective descent for actual affine group schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual Čech datum on an affine group over a finite Galois extension
has a solution whose descended group is affine. -/
def AffineGroupSchemeFiniteGaloisObjectDescentStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L],
    let p : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k L))
    ∀ (H : GroupScheme (Spec (CommRingCat.of L))),
      IsAffineHom H.X.hom →
      ∀ datum : Descent.Datum p H,
        ∃ solution : Descent.Solution datum, IsAffineHom solution.obj.X.hom

/-- Every actual homomorphism between the base changes of two affine groups,
compatible with their canonical Čech data, descends to a unique homomorphism. -/
def AffineGroupSchemeFiniteGaloisHomDescentStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L],
    let p : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k L))
    ∀ (C D : GroupScheme (Spec (CommRingCat.of k))),
      IsAffineHom C.X.hom → IsAffineHom D.X.hom →
      ∀ f : (baseChange p).obj C ⟶ (baseChange p).obj D,
        Descent.Compatible (Descent.canonicalDatum p C) (Descent.canonicalDatum p D) f →
          ∃! g : C ⟶ D, (baseChange p).map g = f

/-- Finite-Galois effective descent for arbitrary affine group schemes:
existence of affine solutions for all actual Čech data and unique descent of
homomorphisms compatible with the canonical data. -/
def AffineGroupSchemeFiniteGaloisDescentStatement : Prop :=
  AffineGroupSchemeFiniteGaloisObjectDescentStatement.{u} ∧
    AffineGroupSchemeFiniteGaloisHomDescentStatement.{u}

end Langlands.GroupScheme

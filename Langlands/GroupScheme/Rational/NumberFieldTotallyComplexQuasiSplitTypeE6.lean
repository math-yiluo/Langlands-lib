import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.SimplyConnected.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Cohomology of quasi-split E6 over totally complex number fields -/

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

/-- Every cocycle of a maximal torus in type E6 over a characteristic-zero
field has a trivial power with exponent supported on 2 and 3. -/
def TypeE6MaximalTorusCocycleOrderStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6), IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G), IsMaximalTorus i →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
        (τ : Cocycle T.toGrp (GaloisCocycle.cover F L)),
        ∃ a b : ℕ, (τ.map (CommGroupScheme.groupHom ((2 ^ a * 3 ^ b : ℕ) • 𝟙 T))).IsTrivial

/-- Quasi-split simply connected E6 groups over totally complex number fields
have trivial cocycles on every Galois cover of degree two or three. -/
def NumberFieldTotallyComplexQuasiSplitTypeE6PrimeCoverStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
      (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6), IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) → IsQuasiSplit G →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
        (Module.finrank F L = 2 ∨ Module.finrank F L = 3) →
        ∀ (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.IsTrivial

/-- Every cocycle of a quasi-split simply connected E6 group over a totally
complex number field is trivial on its finite Galois cover. -/
def NumberFieldTotallyComplexQuasiSplitTypeE6VanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
      (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6), IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) → IsQuasiSplit G →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
        (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.IsTrivial

end Langlands.GroupScheme

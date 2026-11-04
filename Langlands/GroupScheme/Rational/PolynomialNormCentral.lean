import Langlands.GroupScheme.Rational.PolynomialNormHom
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Full centrality of descended polynomial norms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A flat surjective change of test scheme detects full-center membership. -/
theorem mem_center_of_flat_surjective {S : Scheme.{u}} {G : GroupScheme S}
    {T U : Over S} (q : U ⟶ T) [Flat q.left] [Surjective q.left]
    {x : T ⟶ G.X} (hx : q ≫ x ∈ (center G).carrier U) :
    x ∈ (center G).carrier T := by
  intro T' a y
  let V : Over S := Over.mk (pullback.fst a.left q.left ≫ T'.hom)
  let p : V ⟶ T' := Over.homMk (pullback.fst a.left q.left) rfl
  let r : V ⟶ U := Over.homMk (pullback.snd a.left q.left) (by
    dsimp [V]
    rw [← Over.w q, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w a])
  have hp : Epi p.left := by
    change Epi (pullback.fst a.left q.left)
    exact Flat.epi_of_flat_of_surjective _
  have hr : r ≫ q = p ≫ a := by
    apply Over.OverMorphism.ext
    exact pullback.condition.symm
  have hc := (hx V r (p ≫ y)).eq
  have h : p ≫ ((a ≫ x) * y) = p ≫ (y * (a ≫ x)) := by
    simpa only [MonObj.comp_mul, ← Category.assoc, hr] using hc
  change (a ≫ x) * y = y * (a ≫ x)
  apply Over.OverMorphism.ext
  apply (cancel_epi p.left).mp
  exact congrArg (fun z => z.left) h

namespace PolynomialPoint

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- Extending polynomial coefficients along a field extension is faithfully flat. -/
theorem polynomialCoefficients_faithfullyFlat (I : Type) :
    (MvPolynomial.map (algebraMap k L) :
      MvPolynomial I k →+* MvPolynomial I L).FaithfullyFlat := by
  let : Algebra (MvPolynomial I k) (MvPolynomial I L) := MvPolynomial.algebraMvPolynomial
  have hfield : (algebraMap k L).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  exact RingHom.FaithfullyFlat.isStableUnderBaseChange k L
    (MvPolynomial I k) (MvPolynomial I L) hfield

variable (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Extending polynomial coefficients detects membership in the full center. -/
theorem mem_center_of_mapCoefficients (I : Type)
    {p : Lie.AffinePoints G (MvPolynomial I k)}
    (hp : Lie.affineMap G (MvPolynomial.mapAlgHom (Algebra.ofId k L)) p ∈
      (center G).carrier ((algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of k (MvPolynomial I L))))) :
    p ∈ (center G).carrier ((algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of k (MvPolynomial I k)))) := by
  let q := (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (MvPolynomial.mapAlgHom (Algebra.ofId k L) :
      MvPolynomial I k →ₐ[k] MvPolynomial I L)).op
  have hq : Flat q.left ∧ Surjective q.left := by
    apply (flat_and_surjective_SpecMap_iff _).2
    exact polynomialCoefficients_faithfullyFlat k L I
  let : Flat q.left := hq.1
  let : Surjective q.left := hq.2
  exact mem_center_of_flat_surjective q hp

variable [IsAffine G.X.left] [FiniteDimensional k L] [IsGalois k L]

/-- The descended norm polynomial point belongs to the full center. -/
theorem centralNormPoint_mem_center {n : ℕ}
    (x : centralAffinePoints k G (MvPolynomial (Fin n) L)) :
    centralNormPoint k G L x ∈ (center G).carrier
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k (MvPolynomial (Fin n) k)))) := by
  apply mem_center_of_mapCoefficients k L G (Fin n)
  rw [mapCoefficients_centralNormPoint]
  exact (centralConjugateProduct k G L (Fin n) x).property

/-- The descended norm as an actual point of the full center over the base field. -/
def centralNorm {n : ℕ}
    (x : centralAffinePoints k G (MvPolynomial (Fin n) L)) :
    centralAffinePoints k G (MvPolynomial (Fin n) k) :=
  ⟨centralNormPoint k G L x, centralNormPoint_mem_center k L G x⟩

@[simp] theorem centralNorm_val {n : ℕ}
    (x : centralAffinePoints k G (MvPolynomial (Fin n) L)) :
    (centralNorm k L G x).val = centralNormPoint k G L x := rfl

/-- The actual descended norm homomorphism lands in the full center on every test scheme. -/
theorem centralNormHom_isCentral {n : ℕ}
    (x : centralAffinePoints k G (MvPolynomial (Fin n) L))
    (hx : x ∈ centralAdditivePoints k G L n) : IsCentral (centralNormHom k G L x hx) := by
  intro T v
  change v ≫ (homOfAdditive _ _).hom.hom ∈ _
  rw [homOfAdditive_hom]
  exact (center G).comp_mem v (centralNormPoint_mem_center k L G x)

end PolynomialPoint
end Langlands.GroupScheme

import Langlands.GroupScheme.Rational.MaximalTorusParameterDescent
import Langlands.GroupScheme.Rational.MaximalTorusParameterUnirationalStatement
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Generic conjugators of a maximal torus over rational function fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of k))}

/-- `j₀` has a generic conjugator over a rational function field: for some finite `n`, a scheme
`X` with a flat, surjective, quasi-compact morphism `π` to the spectrum of the rational function
field of `𝔸(n; Spec k)`, and a point `g : X ⟶ G.X` with dense image whose conjugate torus
descends along `π`. -/
def HasGenericTorusConjugator (j₀ : T₀.toGrp ⟶ G) : Prop :=
  ∃ (n : Type u) (_ : Finite n) (X : Over (Spec (CommRingCat.of k)))
    (π : X ⟶ rationalFunctionFieldOver k n) (g : X ⟶ G.X),
    Flat π.left ∧ Surjective π.left ∧ QuasiCompact π.left ∧
      TorusConjugateDescends j₀ π g ∧ DenseRange g.left

variable {j₀ : T₀.toGrp ⟶ G}

/-- A generic conjugator makes every actual parameter scheme unirational. -/
theorem HasGenericTorusConjugator.isUnirational (h : HasGenericTorusConjugator j₀)
    {Q : Over (Spec (CommRingCat.of k))} {q : G.X ⟶ Q} (hq : IsMaximalTorusParameter j₀ q) :
    IsUnirational k Q := by
  obtain ⟨n, hn, X, π, g, hflat, hsurj, hqc, hg, hdense⟩ := h
  exact hq.isUnirational_of_torusConjugateDescends π g hg hdense

/-- If every point of `G` over every test scheme normalizes the torus, then the projection
from the base change of `G` to a rational function field is a generic conjugator. -/
theorem hasGenericTorusConjugator_of_normalizer_eq_top
    (hN : ∀ (U : Over (Spec (CommRingCat.of k))) (g : U ⟶ G.X),
      g ∈ (torusNormalizer j₀).carrier U) [Flat G.X.hom] [QuasiCompact G.X.hom] :
    HasGenericTorusConjugator j₀ := by
  let R := rationalFunctionFieldOver k PEmpty.{u + 1}
  let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := 1
  have hsec : e.left ≫ G.X.hom = 𝟙 _ := by
    simp
  have : Surjective G.X.hom := by
    have : Surjective (e.left ≫ G.X.hom) := by
      rw [hsec]
      infer_instance
    exact Surjective.of_comp e.left G.X.hom
  have : Nonempty R.left :=
    inferInstanceAs (Nonempty (PrimeSpectrum (𝔸(PEmpty.{u + 1}; Spec (CommRingCat.of k))).functionField))
  have : Surjective R.hom := ⟨fun s => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  let X : Over (Spec (CommRingCat.of k)) := Over.mk (pullback.snd G.X.hom R.hom ≫ R.hom)
  let π : X ⟶ R := Over.homMk (pullback.snd G.X.hom R.hom) rfl
  let g : X ⟶ G.X := Over.homMk (pullback.fst G.X.hom R.hom) pullback.condition
  refine ⟨PEmpty.{u + 1}, inferInstance, X, π, g, ?_, ?_, ?_, ?_, ?_⟩
  · change Flat (pullback.snd G.X.hom R.hom)
    infer_instance
  · change Surjective (pullback.snd G.X.hom R.hom)
    rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_snd, range_eq_univ,
      Set.preimage_univ]
  · change QuasiCompact (pullback.snd G.X.hom R.hom)
    infer_instance
  · intro U a₁ a₂ _
    exact hN U _
  · have : Set.range (pullback.fst G.X.hom R.hom) = Set.univ := by
      rw [Scheme.Pullback.range_fst, range_eq_univ, Set.preimage_univ]
    change DenseRange (pullback.fst G.X.hom R.hom)
    rw [DenseRange, this]
    exact dense_univ

/-- Every maximal torus of a smooth connected affine group over a field has a generic
conjugator over a rational function field. -/
def MaximalTorusGenericConjugatorStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j₀ : T₀.toGrp ⟶ G),
    IsMaximalTorus j₀ → HasGenericTorusConjugator j₀

/-- The generic conjugator statement implies unirationality of every actual parameter
scheme. -/
theorem maximalTorusParameterUnirational_of_genericConjugator
    (h : MaximalTorusGenericConjugatorStatement.{u}) :
    MaximalTorusParameterUnirationalStatement.{u} :=
  fun k _ G _ _ _ T₀ j₀ hj₀ _ _ hq => (h k G T₀ j₀ hj₀).isUnirational hq

end Langlands.GroupScheme

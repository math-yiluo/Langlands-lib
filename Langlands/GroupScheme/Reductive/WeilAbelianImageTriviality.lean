import Langlands.GroupScheme.Reductive.WeilAbelianImageSplit
import Langlands.GroupScheme.Reductive.WeilAbelianImageCover
import Langlands.Algebra.FiniteEtaleSplitCover

/-! # Homomorphisms with commutative image from a semisimple Weil restriction are trivial -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Langlands.GroupScheme.WeilAbelianImage

open WeilFactor Langlands.Algebra.GraphIdempotent AffineCoverSeparation

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B] [Algebra.Etale A B]

/-- `exists_split_cover`, with the splitting algebra as an object of `CommAlgCat`. -/
theorem exists_split_cover' (p : PrimeSpectrum A) :
    ∃ P : CommAlgCat.{u} (CommRingCat.of A), (algebraMap A P).Flat ∧
      (algebraMap A P).FinitePresentation ∧
      (∃ q : PrimeSpectrum P, PrimeSpectrum.comap (algebraMap A P) q = p) ∧
      ∃ n : ℕ, Nonempty (P ⊗[A] B ≃ₐ[P] (Fin n → P)) := by
  obtain ⟨P, _, _, hflat, hfp, hsurj, hsplit⟩ :=
    Langlands.Algebra.FiniteEtaleSplitCover.exists_split_cover (B := B) p
  exact ⟨CommAlgCat.of (CommRingCat.of A) P, RingHom.flat_algebraMap_iff.2 hflat,
    RingHom.finitePresentation_algebraMap.2 hfp, hsurj, hsplit⟩

variable (G' : GroupScheme (Spec (CommRingCat.of B))) [IsAffine G'.X.left]
  [LocallyOfFiniteType G'.X.hom]
  {M : GroupScheme (Spec (CommRingCat.of A))} {T : CommAlgCat.{u} (CommRingCat.of A)}
  (c : Under.forget T ⋙ (AffineWeil.groupScheme A B G').affinePointFunctor ⟶
    Under.forget T ⋙ M.affinePointFunctor)
  (hc : ∀ (X : Under T)
    (x y : (Under.forget T ⋙ (AffineWeil.groupScheme A B G').affinePointFunctor).obj X),
    Commute (c.app X x) (c.app X y))
  (hred : IsReductive G') (hss : ∀ s, IsSemisimple (geometricFiber G' s))

/-- `X ⊗[A] P`, as a `T`-algebra. -/
abbrev coverUnder (X : Under T) (P : CommAlgCat.{u} (CommRingCat.of A)) : Under T :=
  Under.mk (X.hom ≫ inclLeft X.right P)

include hc hred hss in
/-- Over `X ⊗[A] P`, where `P ⊗[A] B` is split, `c` is trivial. -/
theorem app_coverUnder_eq_one (X : Under T) (P : CommAlgCat.{u} (CommRingCat.of A)) {n : ℕ}
    (σ : P ⊗[A] B ≃ₐ[P] (Fin n → P))
    (y : (AffineWeil.groupScheme A B G').affinePoints (coverUnder X P).right) :
    c.app (coverUnder X P) y = 1 := by
  obtain ⟨φ, e, he, horth, hsum⟩ := Langlands.Algebra.FiniteEtaleSplitCover.exists_graph_family σ
  let ρ : P →ₐ[A] X.right ⊗[A] P := Algebra.TensorProduct.includeRight
  refine app_eq_one_of_split G' c hc hred hss (coverUnder X P) (fun i => ρ.comp (φ i))
    (fun i => Algebra.TensorProduct.map (AlgHom.id A B) ρ (e i)) (fun i => (he i).map ρ)
    (fun i j hij => ?_) ?_ y
  · have h : Algebra.TensorProduct.map (AlgHom.id A B) ρ (e i) *
        Algebra.TensorProduct.map (AlgHom.id A B) ρ (e j) = 0 := by
      rw [← map_mul, horth i j hij, map_zero]
    exact h
  · have h : ∑ i, Algebra.TensorProduct.map (AlgHom.id A B) ρ (e i) = 1 := by
      rw [← map_sum, hsum, map_one]
    exact h

include hc hred hss in
/-- **The homomorphism `c` is trivial.** -/
theorem app_eq_one (X : Under T) (x : (AffineWeil.groupScheme A B G').affinePoints X.right) :
    c.app X x = 1 := by
  choose Q hQ using fun p : PrimeSpectrum A => exists_split_cover' (B := B) p
  apply affinePoint_eq_of_cover Q (fun p => (hQ p).1) (fun p => (hQ p).2.1)
    (fun p => ⟨p, (hQ p).2.2.1⟩) M X.right
  intro p
  obtain ⟨n, ⟨σ⟩⟩ := (hQ p).2.2.2
  have hnat : c.app (coverUnder X (Q p))
      ((AffineWeil.groupScheme A B G').affinePointMap (inclLeft X.right (Q p)) x) =
      M.affinePointMap (inclLeft X.right (Q p)) (c.app X x) :=
    congrArg (fun k => GrpCat.Hom.hom k x)
      (c.naturality (Under.homMk (inclLeft X.right (Q p)) rfl : X ⟶ coverUnder X (Q p)))
  rw [map_one, ← hnat]
  exact app_coverUnder_eq_one G' c hc hred hss X (Q p) σ _

end Langlands.GroupScheme.WeilAbelianImage


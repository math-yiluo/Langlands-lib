import Langlands.GroupScheme.Lie.SmoothFibreRanks
import Langlands.GroupScheme.Descent.Data
import Mathlib.Data.Set.Finite.Lattice

/-! # Uniform bounds for fibre Lie dimensions over affine bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Lie

local instance uniformBound_affine_baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    (G : GroupScheme S) [IsAffineHom G.X.hom] :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

/-- The Lie dimensions of all field-valued fibres of a smooth affine group
are uniformly bounded over the spectrum of an arbitrary ring. -/
theorem exists_uniform_dimension_bound_of_spec
    (R : CommRingCat.{u}) (G : GroupScheme (Spec R))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    ∃ n : ℕ, ∀ (K : Type u) [Field K]
      (b : Spec (CommRingCat.of K) ⟶ Spec R),
      dimension ((baseChange b).obj G) ≤ n := by
  obtain ⟨n, hn⟩ := (isLocallyConstant_lieRank G).range_finite.bddAbove
  refine ⟨n, ?_⟩
  intro K _ b
  let : Algebra R K := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap R K = b := Spec.map_preimage b
  rw [← hb, dimension_baseChange_eq_rankAtStalk G K]
  exact hn (Set.mem_range_self _)

/-- Over an arbitrary affine base the Lie dimensions at all field-valued
points have a common finite bound. Local ranks may vary with the point. -/
theorem exists_uniform_dimension_bound
    {S : Scheme.{u}} [IsAffine S] (G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    ∃ n : ℕ, ∀ (K : Type u) [Field K]
      (b : Spec (CommRingCat.of K) ⟶ S),
      dimension ((baseChange b).obj G) ≤ n := by
  let H := (baseChange S.isoSpec.inv).obj G
  let : Smooth H.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom S.isoSpec.inv))
  let : IsAffineHom H.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom S.isoSpec.inv))
  obtain ⟨n, hn⟩ := exists_uniform_dimension_bound_of_spec Γ(S, ⊤) H
  refine ⟨n, ?_⟩
  intro K _ b
  have hcomp : (b ≫ S.isoSpec.hom) ≫ S.isoSpec.inv = b := by simp
  let e := Descent.pullbackComparison S.isoSpec.inv
    (b ≫ S.isoSpec.hom) b hcomp G
  rw [← dimension_eq_of_iso e]
  exact hn K (b ≫ S.isoSpec.hom)

/-- Geometric fibres in particular admit a uniform Lie-dimension bound. -/
theorem exists_uniform_geometric_dimension_bound
    {S : Scheme.{u}} [IsAffine S] (G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    ∃ n : ℕ, ∀ s : S, dimension (geometricFiber G s) ≤ n := by
  obtain ⟨n, hn⟩ := exists_uniform_dimension_bound G
  exact ⟨n, fun s => hn (AlgebraicClosure (S.residueField s)) (geometricPoint S s)⟩

/-- A chosen common bound, packaged with its validity for every field-valued
fibre of the given smooth affine group. -/
def uniformDimensionBound
    {S : Scheme.{u}} [IsAffine S] (G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    {n : ℕ // ∀ (K : Type u) [Field K]
      (b : Spec (CommRingCat.of K) ⟶ S),
      dimension ((baseChange b).obj G) ≤ n} :=
  ⟨Classical.choose (exists_uniform_dimension_bound G),
    Classical.choose_spec (exists_uniform_dimension_bound G)⟩

end Langlands.GroupScheme.Lie

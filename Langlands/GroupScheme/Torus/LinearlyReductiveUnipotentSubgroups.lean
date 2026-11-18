import Langlands.GroupScheme.MatrixRepresentation.NilpotentTangentObstruction
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Lie.UnipotentTangent
import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Lie.ZeroTangentTriviality

/-! # Connected unipotent subgroups of linearly reductive groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A faithful restricted representation of an unipotent subgroup has trivial
actual tangent kernel inside a positive-characteristic linearly reductive group. -/
theorem subsingleton_lieKernel_of_unipotent_of_linearlyReductive
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (hLR : ∀ d (ρ : MatrixRepresentation G (Fin d)), ρ.IsSemisimple)
    (i : H ⟶ G) (hH : IsUnipotent H) {n : ℕ}
    (ρ : MatrixRepresentation G (Fin n)) [Mono (ρ.restrict i).hom.hom] :
    Subsingleton (lieKernel H k) := by
  have hzero (X : lieKernel H k) : (ρ.restrict i).tangentMatrix k X = 0 := by
    have hN := (ρ.restrict i).isNilpotent_tangentMatrix_of_isUnipotent hH k X
    rw [tangentMatrix_restrict] at hN ⊢
    exact tangentMatrix_eq_zero_of_isNilpotent_of_linearlyReductive p hp hLR ρ
      (Lie.targetMap i k X) hN
  have hone (X : lieKernel H k) : X = 1 := by
    apply lieKernelHom_injective (ρ.restrict i)
    apply (GeneralLinear.DualNumber.pointKernelEquiv
      (n := Fin n) (R := CommRingCat.of k) (S := k)).symm.injective
    change (ρ.restrict i).tangentMatrix k X = (ρ.restrict i).tangentMatrix k 1
    rw [hzero, tangentMatrix_one]
  exact ⟨fun X Y => (hone X).trans (hone Y).symm⟩

/-- Every connected closed unipotent subgroup functor is trivial. No smoothness
or normality hypothesis is part of this predicate. -/
def HasTrivialConnectedUnipotentSubgroups
    (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
    IsClosedSubgroup i → IsUnipotent H → ConnectedSpace H.X.left →
      SubgroupFunctor.range i = ⊥

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Every closed unipotent subgroup has trivial tangent kernel. This includes
nonsmooth and nonnormal subgroups. -/
theorem subsingleton_lieKernel_closed_unipotent_of_linearlyReductive
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (hLR : ∀ d (ρ : MatrixRepresentation G (Fin d)), ρ.IsSemisimple)
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : IsUnipotent H) :
    Subsingleton (lieKernel H k) := by
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono ρ.hom.hom := Over.mono_of_mono_left _
  have : Mono (ρ.restrict i).hom.hom := by
    change Mono (i.hom.hom ≫ ρ.hom.hom)
    infer_instance
  exact subsingleton_lieKernel_of_unipotent_of_linearlyReductive p hp hLR i hH ρ

/-- The actual structure morphism of every connected closed unipotent subgroup
of a positive-characteristic linearly reductive affine algebraic group is an
isomorphism. -/
theorem isIso_structure_closed_connected_unipotent_of_linearlyReductive
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (hLR : ∀ d (ρ : MatrixRepresentation G (Fin d)), ρ.IsSemisimple)
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : IsUnipotent H)
    [ConnectedSpace H.X.left] : IsIso H.X.hom := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : LocallyOfFiniteType H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : Subsingleton (lieKernel H k) :=
    subsingleton_lieKernel_closed_unipotent_of_linearlyReductive p hp hLR i hi hH
  exact Lie.isIso_structure_of_subsingleton_lieKernel H

/-- Every scheme-test point of such a connected unipotent subgroup is the
identity, including points over nonreduced algebras. -/
theorem points_eq_one_closed_connected_unipotent_of_linearlyReductive
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (hLR : ∀ d (ρ : MatrixRepresentation G (Fin d)), ρ.IsSemisimple)
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : IsUnipotent H)
    [ConnectedSpace H.X.left]
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ H.X) : x = 1 := by
  have := isIso_structure_closed_connected_unipotent_of_linearlyReductive p hp hLR i hi hH
  apply Over.OverMorphism.ext
  apply (cancel_mono H.X.hom).mp
  simp only [Over.w]

/-- A positive-characteristic linearly reductive affine algebraic group has no
nontrivial connected closed unipotent subgroup functor. -/
theorem range_eq_bot_closed_connected_unipotent_of_linearlyReductive
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (hLR : ∀ d (ρ : MatrixRepresentation G (Fin d)), ρ.IsSemisimple)
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : IsUnipotent H)
    [ConnectedSpace H.X.left] : SubgroupFunctor.range i = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  change (SubgroupFunctor.range i).carrier T = (⊥ : Subgroup (T ⟶ G.X))
  apply eq_bot_iff.mpr
  rintro x ⟨y, rfl⟩
  erw [Subgroup.mem_bot]
  have hy := points_eq_one_closed_connected_unipotent_of_linearlyReductive
    p hp hLR i hi hH T y
  change y ≫ i.hom.hom = 1
  rw [hy]
  exact map_one (((pointsMap i).app (op T)).hom)

/-- Positive-characteristic linear reductivity excludes all connected closed
unipotent subgroup schemes. -/
theorem hasTrivialConnectedUnipotentSubgroups_of_linearlyReductive
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (hLR : ∀ d (ρ : MatrixRepresentation G (Fin d)), ρ.IsSemisimple) :
    HasTrivialConnectedUnipotentSubgroups G := by
  intro H i hi hH hc
  let : ConnectedSpace H.X.left := hc
  exact range_eq_bot_closed_connected_unipotent_of_linearlyReductive p hp hLR i hi hH

end Langlands.GroupScheme

import Langlands.GroupScheme.Torus.MultiplicativeTypeTorusEmbeddingStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeAtlasEmbedding
import Langlands.GroupScheme.Torus.FppfRelativeTorusDescent

/-! # Groups of multiplicative type are closed subgroups of tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open RelativeMultiplicativeType

namespace RelativeMultiplicativeType.DiagonalizableAtlas

variable {S : Scheme.{u}} {H : GroupScheme S}

/-- The diagonalizable atlas given by an fppf cover over whose members `H` is diagonalizable,
with chosen character groups and trivializations. -/
def ofCover (𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S)
    (h𝒰 : ∀ i : 𝒰.I₀, IsDiagonalizable ((GroupScheme.baseChange (𝒰.f i)).obj H)) :
    DiagonalizableAtlas H where
  I := 𝒰.I₀
  Z := 𝒰.X
  f := 𝒰.f
  Λ i := (h𝒰 i).choose
  addCommGroup i := (h𝒰 i).choose_spec.choose
  fg i := (h𝒰 i).choose_spec.choose_spec.choose
  e i := (h𝒰 i).choose_spec.choose_spec.choose_spec.some

variable (𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S)
  (h𝒰 : ∀ i : 𝒰.I₀, IsDiagonalizable ((GroupScheme.baseChange (𝒰.f i)).obj H))

instance ofCover_flat : Flat (ofCover 𝒰 h𝒰).projection := by
  have : ∀ i, Flat (𝒰.f i) := fun i => (𝒰.map_prop i).1
  exact (inferInstance : Flat (Sigma.desc 𝒰.f))

instance ofCover_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (ofCover 𝒰 h𝒰).projection :=
  IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation)
    fun i => (𝒰.map_prop i).2

instance ofCover_surjective : Surjective (ofCover 𝒰 h𝒰).projection :=
  Surjective.sigmaDesc_of_union_range_eq_univ 𝒰.iUnion_range

end RelativeMultiplicativeType.DiagonalizableAtlas

/-- **Groups of multiplicative type are closed subgroups of tori** (Conrad, *Reductive group
schemes* (2014), Proposition B.3.8). -/
theorem multiplicativeTypeTorusEmbedding : MultiplicativeTypeTorusEmbeddingStatement.{u} := by
  intro S H ⟨𝒰, h𝒰⟩
  let A := DiagonalizableAtlas.ofCover 𝒰 h𝒰
  refine ⟨A.torus, A.torusEmbedding, ?_, A.isClosedSubgroup_torusEmbedding⟩
  exact RelativeTorus.IsTorus.of_fppfCover 𝒰 fun i =>
    RelativeTorus.IsTorus.of_isSplitTorus (A.isSplitTorus_baseChange_torus i)

end Langlands.GroupScheme

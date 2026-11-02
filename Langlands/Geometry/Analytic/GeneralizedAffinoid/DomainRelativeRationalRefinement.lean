import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCovering

/-! # Finite domain covers refined over the containing domain algebra -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} {U : Domain K A}

/-- A finite rational cover over the actual containing algebra, together with
its chosen actual restrictions through the original finite cover. -/
structure RelativeRationalRefinement (c : FiniteCover U) where
  size : ℕ
  chart : Fin size → RationalChart K U.algebra
  index : Fin size → Fin c.size
  map : ∀ i, U.extend (chart i).toDomain ⟶ c.obj (index i)
  covers : ∀ x : BanachSpectrum U.algebra, ∃ i, x ∈ (chart i).locus

namespace RelativeRationalRefinement

variable {c : FiniteCover U} (r : RelativeRationalRefinement c)

/-- Both routes to the containing domain are the same actual bounded arrow. -/
theorem map_comp (i : Fin r.size) :
    r.map i ≫ c.map (r.index i) = U.extendInclusion (r.chart i).toDomain :=
  @Subsingleton.elim (Inclusion (U.extend (r.chart i).toDomain) U) inferInstance _ _

/-- On algebras, the composite restriction is the rational structural map. -/
theorem restriction_comp (i : Fin r.size) :
    (r.map i).restriction.comp (c.map (r.index i)).restriction =
      (r.chart i).baseMap :=
  congrArg Inclusion.restriction (r.map_comp i)

/-- The extended rational family covers the original represented locus. -/
theorem covers_ambient :
    ∀ x ∈ U.locus, ∃ i, x ∈ (U.extend (r.chart i).toDomain).locus := by
  intro x hx
  obtain ⟨y, hy⟩ := U.represents.2.1.symm ▸ hx
  obtain ⟨i, hi⟩ := r.covers y
  exact ⟨i, y, hi, hy⟩

/-- The refined finite cover keeps each actual rational quotient algebra. -/
def toFiniteCover : FiniteCover U where
  size := r.size
  obj i := U.extend (r.chart i).toDomain
  map i := U.extendInclusion (r.chart i).toDomain
  covers := r.covers_ambient

/-- Chosen component maps exhibit an actual refinement of the original cover. -/
def toRefinement : Refinement r.toFiniteCover c where
  index := r.index
  map := r.map

end RelativeRationalRefinement

/-- Every finite full-domain cover refines by rational charts over the actual
algebra of its target, without changing the stored algebras or restrictions. -/
def relativeRationalRefinement (c : FiniteCover U) :
    RelativeRationalRefinement c := by
  classical
  let d : ∀ i : Fin c.size, FiniteRationalCover (U.relative (c.obj i) (c.map i)) :=
    fun i => finiteRationalCoverData (U.relative (c.obj i) (c.map i))
  let I := (i : Fin c.size) × Fin (d i).size
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine {
    size := Fintype.card I
    chart := fun j => (d (e j).1).chart (e j).2
    index := fun j => (e j).1
    map := fun j => ?_
    covers := ?_ }
  · let i := (e j).1
    let k := (e j).2
    let f := (d i).map k
    refine ⟨f.restriction, ?_⟩
    change f.restriction.comp (c.obj i).baseMap =
      ((d i).chart k).baseMap.comp U.baseMap
    apply BoundedAlgHom.ext
    intro a
    have hi := congrArg (fun q => f.restriction (q a)) (c.map i).comp_baseMap
    have hf := congrArg (fun q => q (U.baseMap a)) f.comp_baseMap
    exact hi.symm.trans hf
  · intro x
    obtain ⟨i, hi⟩ := c.covers (U.spectrumMap x) (U.represents.hasImageIn x)
    have hx : x ∈ (U.relative (c.obj i) (c.map i)).locus := by
      rw [U.relative_locus_eq_preimage]
      exact hi
    obtain ⟨k, hk⟩ := (d i).covers x hx
    refine ⟨e.symm ⟨i, k⟩, ?_⟩
    change x ∈ ((fun ij : I => (d ij.1).chart ij.2) (e (e.symm ⟨i, k⟩))).locus
    rw [Equiv.apply_symm_apply]
    exact hk

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Transport of actual unipotence and split series between representatives -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Points

variable {B : Scheme.{u}} {H H' K : GroupScheme B}

private theorem iso_left (e : H ≅ H') : IsIso e.hom.hom.hom.left := by
  exact (inferInstance :
    IsIso (((Grp.forget (Over B)) ⋙ Over.forget B).map e.hom))

/-- Composing an inclusion with an isomorphism transports its range by the
inverse isomorphism on every test scheme. -/
theorem SubgroupFunctor.range_comp_iso (j : K ⟶ H) (e : H ≅ H') :
    range (j ≫ e.hom) = (range j).comap e.inv := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [mem_comap, mem_range, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp only [Category.assoc, ← Grp.comp_hom_hom,
      e.hom_inv_id, Category.comp_id]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hy, Category.assoc,
      ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

end Points

section Field

variable {k : Type u} [Field k]
    {H H' : GroupScheme (Spec (CommRingCat.of k))}

/-- Unipotence in the actual coefficient-representation sense is invariant
under group-scheme isomorphism. -/
theorem IsUnipotent.of_iso (e : H ≅ H') (h : IsUnipotent H') : IsUnipotent H := by
  intro n _ _ _ ρ
  obtain ⟨v, hv, hfix⟩ := h n (ρ.restrict e.inv)
  refine ⟨v, hv, ?_⟩
  intro T g
  have hg := hfix T (g ≫ e.hom.hom.hom)
  simpa only [MatrixRepresentation.pointMatrix_restrict, Category.assoc,
    ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using hg

end Field

namespace RelativeRoot

variable {B : Scheme.{u}} {H H' Q : GroupScheme B}

/-- Transport all-test vector coordinates through a group-scheme isomorphism. -/
def vectorCoordinatesOfIso (e : H ≅ H') {n : ℕ}
    (c : ∀ T : Over B, (T ⟶ H.X) ≃*
      Multiplicative (Fin n → Γ(T.left, ⊤))) :
    ∀ T : Over B, (T ⟶ H'.X) ≃*
      Multiplicative (Fin n → Γ(T.left, ⊤)) :=
  fun T => (isoPointsEquiv e.symm T).trans (c T)

@[simp] theorem vectorCoordinatesOfIso_apply (e : H ≅ H') {n : ℕ}
    (c : ∀ T : Over B, (T ⟶ H.X) ≃*
      Multiplicative (Fin n → Γ(T.left, ⊤)))
    (T : Over B) (x : T ⟶ H'.X) :
    vectorCoordinatesOfIso e c T x = c T (x ≫ e.inv.hom.hom) := rfl

/-- Naturality of vector coordinates is preserved by transport. -/
theorem IsVectorGroupOfDimension.of_iso (e : H ≅ H') {n : ℕ}
    (h : IsVectorGroupOfDimension H n) : IsVectorGroupOfDimension H' n := by
  obtain ⟨c, hc⟩ := h
  refine ⟨vectorCoordinatesOfIso e c, ?_⟩
  intro T V b x
  simpa only [vectorCoordinatesOfIso_apply, Category.assoc] using
    hc T V b (x ≫ e.inv.hom.hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pulling back the source of an fppf quotient along an isomorphism preserves
the cover and the exact all-test kernel. -/
theorem IsFppfQuotient.comapIso (e : H ≅ H') {N : SubgroupFunctor H}
    {q : H ⟶ Q} (h : IsFppfQuotient N q) :
    IsFppfQuotient (N.comap e.inv) (e.inv ≫ q) := by
  obtain ⟨hflat, hsurj, hfp, hker⟩ := h
  have : IsIso e.inv.hom.hom.left := iso_left e.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Flat (e.inv.hom.hom.left ≫ q.hom.hom.left)
    exact (MorphismProperty.cancel_left_of_respectsIso @Flat
      e.inv.hom.hom.left q.hom.hom.left).mpr hflat
  · change Surjective (e.inv.hom.hom.left ≫ q.hom.hom.left)
    exact (MorphismProperty.cancel_left_of_respectsIso @Surjective
      e.inv.hom.hom.left q.hom.hom.left).mpr hsurj
  · change LocallyOfFinitePresentation (e.inv.hom.hom.left ≫ q.hom.hom.left)
    exact (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFinitePresentation
      e.inv.hom.hom.left q.hom.hom.left).mpr hfp
  · apply SubgroupFunctor.ext
    intro T
    ext x
    rw [mem_range_kernelι_iff, SubgroupFunctor.mem_comap,
      ← hker, mem_range_kernelι_iff, Grp.comp_hom_hom,
      Category.assoc]

/-- A finite normal Ga-series transports without changing its length. -/
theorem HasSplitSeries.of_iso (e : H ≅ H') {n : ℕ}
    (h : HasSplitSeries n H) : HasSplitSeries n H' := by
  cases n with
  | zero =>
    apply SubgroupFunctor.ext
    intro T
    ext x
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
    constructor
    · intro _
      have hx : x ≫ e.inv.hom.hom ∈ (SubgroupFunctor.range (𝟙 H)).carrier T :=
        SubgroupFunctor.mem_range.mpr
          ⟨x ≫ e.inv.hom.hom, by
            change (x ≫ e.inv.hom.hom) ≫ 𝟙 H.X = _
            exact Category.comp_id _⟩
      rw [h, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
      apply (isoPointsEquiv e.symm T).injective
      simpa only [isoPointsEquiv_apply, Iso.symm_hom, MonObj.one_comp] using hx
    · rintro rfl
      exact Subgroup.one_mem _
  | succ n =>
    obtain ⟨K, V, j, q, hj, hsmooth, hconn, hnormal, hquot, hvector, hseries⟩ := h
    refine ⟨K, V, j ≫ e.hom, e.inv ≫ q, ?_, hsmooth, hconn, ?_, ?_,
      hvector, hseries⟩
    · have := iso_left e
      have : IsClosedImmersion j.hom.hom.left := hj
      change IsClosedImmersion (j.hom.hom.left ≫ e.hom.hom.hom.left)
      infer_instance
    · rw [SubgroupFunctor.range_comp_iso]
      exact hnormal.comap e.inv
    · rw [SubgroupFunctor.range_comp_iso]
      exact hquot.comapIso e

/-- Split unipotence by a finite Ga-series is invariant under isomorphism. -/
theorem IsSplitUnipotent.of_iso (e : H ≅ H') (h : IsSplitUnipotent H) :
    IsSplitUnipotent H' := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.of_iso e⟩

/-- A unipotent split representative supplies the same properties for every
representative of the very same all-test subgroup functor. -/
theorem unipotent_and_split_of_representatives
    {k : Type u} [Field k] {G H H' : GroupScheme (Spec (CommRingCat.of k))}
    {F : SubgroupFunctor G} {j : H ⟶ G} {j' : H' ⟶ G}
    (hj : F.IsRepresentedBy j) (hj' : F.IsRepresentedBy j')
    (hu : IsUnipotent H) (hs : IsSplitUnipotent H) :
    IsUnipotent H' ∧ IsSplitUnipotent H' := by
  let e := hj.isoOfIsRepresentedBy hj'
  exact ⟨hu.of_iso e.symm, hs.of_iso e⟩

end RelativeRoot
end Langlands.GroupScheme

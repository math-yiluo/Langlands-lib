import Langlands.GroupScheme.Derived.EpiProductDetection
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.Reductive.Semisimple

/-! # Full-centre comparison under a central product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H Z D : GroupScheme S}

/-- Pulling the ambient centre back along a monomorphism lands in the source centre. -/
theorem center_comap_le_of_mono (d : D ⟶ G) [Mono d.hom.hom] :
    (center G).comap d ≤ center D := by
  intro T x hx U a y
  change x ≫ d.hom.hom ∈ (center G).carrier T at hx
  apply (commute_iff_eq _ _).mpr
  apply (cancel_mono d.hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp]
  simpa only [Category.assoc] using (hx U a (y ≫ d.hom.hom)).eq

namespace SubgroupFunctor

/-- Every central point centralizes every subgroup functor. -/
theorem center_le_centralizer (F : SubgroupFunctor G) : center G ≤ F.centralizer :=
  fun _ _ hx U a y _ => hx U a y

/-- Centralization of two subgroup functors is symmetric on all test schemes. -/
theorem le_centralizer_iff {F K : SubgroupFunctor G} :
    F ≤ K.centralizer ↔ K ≤ F.centralizer := by
  suffices h : ∀ {F K : SubgroupFunctor G}, F ≤ K.centralizer → K ≤ F.centralizer from
    ⟨h, h⟩
  intro F K h T x hx U a y hy
  have hc := h U hy U (𝟙 U) (a ≫ x) (K.comp_mem a hx)
  simpa only [Category.id_comp] using hc.symm

/-- Every subgroup functor lies in its double centralizer. -/
theorem le_doubleCentralizer (F : SubgroupFunctor G) : F ≤ F.centralizer.centralizer :=
  le_centralizer_iff.mp le_rfl

/-- Centralizing all points is the full scheme-theoretic centre. -/
theorem centralizer_top : (⊤ : SubgroupFunctor G).centralizer = center G := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · intro hx U a y
    exact hx U a y (Subgroup.mem_top _)
  · intro hx U a y _
    exact hx U a y

end SubgroupFunctor

section Field

variable {k : Type u} [Field k]
  {G Z D : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]

/-- Under a central product epimorphism, the centralizer of the second factor is the centre. -/
theorem centralizer_range_eq_center_of_epi_subgroupProductMap
    (i : Z ⟶ G) (hi : IsCentral i) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    [Epi (subgroupProductMap i d)] :
    (SubgroupFunctor.range d).centralizer = center G := by
  obtain ⟨C, c, hcc, hc⟩ :=
    (hasClosedRepresentative_normalizer_centralizer_range d hd).2
  have hdc : SubgroupFunctor.range d ≤ (SubgroupFunctor.range c).centralizer := by
    rw [hc.2]
    exact SubgroupFunctor.le_doubleCentralizer _
  have hic : SubgroupFunctor.range i ≤ (SubgroupFunctor.range c).centralizer := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.center_le_centralizer _ T (hi T y)
  have htop : (SubgroupFunctor.range c).centralizer = ⊤ :=
    SubgroupFunctor.eq_top_of_hasClosedRepresentative_of_epi_subgroupProductMap
      (hasClosedRepresentative_normalizer_centralizer_range c hcc).2 i d hic hdc
  apply le_antisymm
  · rw [← hc.2]
    have h := SubgroupFunctor.le_doubleCentralizer (SubgroupFunctor.range c)
    rw [htop, SubgroupFunctor.centralizer_top] at h
    exact h
  · exact SubgroupFunctor.center_le_centralizer _

/-- A central point of the second factor maps into the ambient full centre. -/
theorem center_le_comap_of_epi_subgroupProductMap
    (i : Z ⟶ G) (hi : IsCentral i) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    [Epi (subgroupProductMap i d)] : center D ≤ (center G).comap d := by
  intro T x hx
  change x ≫ d.hom.hom ∈ (center G).carrier T
  rw [← centralizer_range_eq_center_of_epi_subgroupProductMap i hi d hd]
  intro U a y hy
  obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hy
  apply (commute_iff_eq _ _).mpr
  have hc := congrArg (fun w : U ⟶ D.X => w ≫ d.hom.hom) (hx U a z).eq
  simpa only [MonObj.mul_comp, Category.assoc] using hc

/-- The centre of the second factor is the inverse image of the ambient full centre. -/
theorem center_eq_comap_of_epi_subgroupProductMap
    (i : Z ⟶ G) (hi : IsCentral i) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    [Epi (subgroupProductMap i d)] : center D = (center G).comap d := by
  have : IsClosedImmersion d.hom.hom.left := hd
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  exact le_antisymm (center_le_comap_of_epi_subgroupProductMap i hi d hd)
    (center_comap_le_of_mono d)

/-- A closed representative of the ambient-centre preimage represents the full source centre. -/
theorem isSchemeTheoreticCenter_of_center_preimage_of_epi_subgroupProductMap
    (i : Z ⟶ G) (hi : IsCentral i) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    [Epi (subgroupProductMap i d)] {C : GroupScheme (Spec (CommRingCat.of k))} (c : C ⟶ D)
    (hcc : IsClosedSubgroup c) (hc : SubgroupFunctor.range c = (center G).comap d) :
    IsSchemeTheoreticCenter c := by
  refine ⟨hcc, ?_⟩
  rw [hc, center_eq_comap_of_epi_subgroupProductMap i hi d hd]

/-- Points of a centre-preimage representative are exactly the full source-centre points. -/
def centerPreimagePointsEquiv
    (i : Z ⟶ G) (hi : IsCentral i) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    [Epi (subgroupProductMap i d)] {C : GroupScheme (Spec (CommRingCat.of k))} (c : C ⟶ D)
    (hcc : IsClosedSubgroup c) (hc : SubgroupFunctor.range c = (center G).comap d)
    (T : Over (Spec (CommRingCat.of k))) : (T ⟶ C.X) ≃* (center D).carrier T :=
  (isSchemeTheoreticCenter_of_center_preimage_of_epi_subgroupProductMap
    i hi d hd c hcc hc).isRepresentedBy.pointsEquiv T

/-- The centre-point equivalence is the given subgroup inclusion on underlying points. -/
theorem centerPreimagePointsEquiv_apply_coe
    (i : Z ⟶ G) (hi : IsCentral i) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    [Epi (subgroupProductMap i d)] {C : GroupScheme (Spec (CommRingCat.of k))} (c : C ⟶ D)
    (hcc : IsClosedSubgroup c) (hc : SubgroupFunctor.range c = (center G).comap d)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ C.X) :
    (centerPreimagePointsEquiv i hi d hd c hcc hc T x : T ⟶ D.X) = x ≫ c.hom.hom :=
  rfl

/-- A finite representative of the ambient-centre preimage is the finite full centre. -/
theorem hasFiniteCenter_of_finite_center_preimage_of_epi_subgroupProductMap
    (i : Z ⟶ G) (hi : IsCentral i) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    [Epi (subgroupProductMap i d)] (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ D)
    (hcc : IsClosedSubgroup c) (hc : SubgroupFunctor.range c = (center G).comap d)
    (hfin : IsFinite C.X.hom) : HasFiniteCenter D := by
  exact ⟨C, c, isSchemeTheoreticCenter_of_center_preimage_of_epi_subgroupProductMap
    i hi d hd c hcc hc, hfin⟩

end Field

end Langlands.GroupScheme

import Langlands.GroupScheme.RelativeLevi.SplitBorelHeightChart
import Langlands.GroupScheme.RelativeUnipotent.RootHeightSeries

/-! # Assembly of split Borel structure from positive-root chart inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open LocalSplitCell

/-- Transport an affine vector-quotient series through an actual group-scheme
isomorphism, preserving its length. -/
theorem HasAffineVectorSeries.of_iso {R : CommRingCat.{u}}
    {H H' : GroupScheme (Spec R)} (e : H ≅ H') {n : ℕ}
    (h : HasAffineVectorSeries n H) : HasAffineVectorSeries n H' := by
  cases n with
  | zero =>
    exact RelativeUnipotent.HasVectorBundleSeries.of_iso e (n := 0) h
  | succ n =>
    obtain ⟨K, V, j, q, hj, hq, hV, hK⟩ := h
    refine ⟨K, V, j ≫ e.hom, e.inv ≫ q, ?_, ?_, hV, hK⟩
    · have : IsIso e.hom.hom.hom.left :=
        (inferInstance : IsIso (((Grp.forget (Over (Spec R))) ⋙ Over.forget (Spec R)).map e.hom))
      have : IsClosedImmersion j.hom.hom.left := hj
      change IsClosedImmersion (j.hom.hom.left ≫ e.hom.hom.hom.left)
      infer_instance
    · rw [SubgroupFunctor.range_comp_iso]
      exact hq.comapIso e

namespace RelativeUnipotent.RootHeightChart

variable {R : Type u} [CommRing R]
    {U : GroupScheme (Spec (CommRingCat.of R))} (C : RootHeightChart U)

/-- The actual standard vector quotients of a bounded root-height chart give
an affine vector-quotient series of that length. -/
theorem hasAffineVectorSeries_of_bound (n : ℕ) (hn : ∀ k, C.height k < n + 1) :
    HasAffineVectorSeries n U := by
  have hsegment : ∀ n d : ℕ, 0 < d →
      SubgroupFunctor.range (𝟙 (C.groupScheme (d + n))) = ⊥ →
      HasAffineVectorSeries n (C.groupScheme d) := by
    intro m
    induction m with
    | zero =>
      intro d _ hterminal
      exact hterminal
    | succ m ih =>
      intro d hd hterminal
      refine ⟨C.groupScheme (d + 1),
        VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (C.exactSupport d)),
        C.step d, C.quotientMap d hd, C.isClosedSubgroup_step d,
        C.isFppfQuotient_quotientMap d hd, ?_, ?_⟩
      · exact ⟨_, VectorGroup.coordinates _ _, (fun _ _ f v => VectorGroup.coordinates_comp f v)⟩
      · apply ih (d + 1) (by omega)
        have he : d + 1 + m = d + (m + 1) := by omega
        rw [he]
        exact hterminal
  have hterm : SubgroupFunctor.range (𝟙 (C.groupScheme (1 + n))) = ⊥ :=
    C.range_id_eq_bot (by simpa only [Nat.add_comm 1 n] using hn)
  exact (hsegment n 1 (by omega) hterm).of_iso C.heightOneIso

include C in
/-- A supplied positive root-height chart gives a finite series with actual
finite-dimensional vector groups as its represented fppf quotients. -/
theorem hasFiniteAffineVectorSeries : ∃ n : ℕ, HasAffineVectorSeries n U :=
  ⟨C.heightBound, C.hasAffineVectorSeries_of_bound C.heightBound
    (fun k => Nat.lt_succ_of_le (C.height_le_heightBound k))⟩

end RelativeUnipotent.RootHeightChart

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- A series on the contracting group in an actual positive chart gives the
specified split Borel structure. -/
theorem hasSplitBorelVectorSeries_of_positiveChart
    (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (c : SplitBorelPositiveChart i P)
    (hseries : ∃ l : ℕ, HasAffineVectorSeries l
      (AffineRegularBorel.contractingGroup i c.cocharacter)) :
    HasSplitBorelVectorSeries i := by
  exact AffineRegularBorel.hasSplitBorelVectorSeries_of_contractingSeries
    i c.cocharacter P hP c.regular hG hi hmax hseries

/-- Supplied actual root parametrizations and a series construction on their
positive-chart package suffice for the full split Borel structure. -/
theorem hasSplitBorelVectorSeries_of_rootParametrizations_and_chartSeries
    (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (fam : J → (Ga R ⟶ G))
    (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))
    (hseries : ∀ c : SplitBorelPositiveChart i P,
      ∃ l : ℕ, HasAffineVectorSeries l
        (AffineRegularBorel.contractingGroup i c.cocharacter)) :
    HasSplitBorelVectorSeries i := by
  obtain ⟨c⟩ := nonempty_splitBorelPositiveChart hG hmax hP fam hfam
  exact hasSplitBorelVectorSeries_of_positiveChart hG hi hmax hP c (hseries c)

end Langlands.GroupScheme

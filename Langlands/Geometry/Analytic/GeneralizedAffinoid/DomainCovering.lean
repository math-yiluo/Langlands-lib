import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalCoverProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalNeighborhoodCover
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalIntersection
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverRefinement
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Data.Fintype.Sigma

/-! # Finite coverings of all full represented affinoid domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- Actual point coverage in the fixed ambient affinoid spectrum. -/
def FamilyCovers {I : Type u} (U : Domain K A) (D : I → Domain K A) : Prop :=
  ∀ x ∈ U.locus, ∃ i, x ∈ (D i).locus

/-- A covering sieve contains finitely many actual bounded restrictions
whose represented loci cover its target. The finite index may be empty. -/
def IsFiniteCovering {U : Domain K A} (S : Sieve U) : Prop :=
  ∃ (I : Type u) (_ : Finite I) (D : I → Domain K A)
    (f : ∀ i, D i ⟶ U), (∀ i, S (f i)) ∧ FamilyCovers U D

private theorem hom_unique {U V : Domain K A} (f g : U ⟶ V) : f = g :=
  @Subsingleton.elim (Inclusion U V) inferInstance f g

/-- Choose an actual finite ambient rational cover from the published
unconditional finite rational-cover theorem. -/
def finiteRationalCoverData (U : Domain K A) : FiniteRationalCover U := by
  apply Classical.choice
  obtain ⟨n, D, f, h⟩ := finiteRationalCover K A U
  exact ⟨⟨n, D, f, h⟩⟩

/-- Every finite covering sieve already contains a finite covering by rational
charts over the original ambient algebra, with their actual bounded arrows. -/
theorem IsFiniteCovering.rationalRefinement {U : Domain K A} {S : Sieve U}
    (hS : IsFiniteCovering S) :
    ∃ (I : Type u) (_ : Finite I) (D : I → RationalChart K A)
      (f : ∀ i, (D i).toDomain ⟶ U),
      (∀ i, S (f i)) ∧ (∀ x ∈ U.locus, ∃ i, x ∈ (D i).locus) := by
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  let c : ∀ i, FiniteRationalCover (D i) := fun i => finiteRationalCoverData (D i)
  let : Finite I := hI
  refine ⟨(i : I) × Fin (c i).size, inferInstance,
    fun ij => (c ij.1).chart ij.2,
    fun ij => (c ij.1).map ij.2 ≫ f ij.1, ?_, ?_⟩
  · intro ij
    exact S.downward_closed (hf ij.1) ((c ij.1).map ij.2)
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    obtain ⟨j, hj⟩ := (c i).covers x hi
    exact ⟨⟨i, j⟩, hj⟩

/-- A rational covering family in a sieve also witnesses finite full-domain
coverage. This is an exact basis characterization of covering sieves. -/
theorem isFiniteCovering_iff_rational {U : Domain K A} (S : Sieve U) :
    IsFiniteCovering S ↔
      ∃ (I : Type u) (_ : Finite I) (D : I → RationalChart K A)
        (f : ∀ i, (D i).toDomain ⟶ U),
        (∀ i, S (f i)) ∧ (∀ x ∈ U.locus, ∃ i, x ∈ (D i).locus) := by
  constructor
  · exact IsFiniteCovering.rationalRefinement
  · rintro ⟨I, hI, D, f, hf, hcover⟩
    exact ⟨I, hI, fun i => (D i).toDomain, f, hf, hcover⟩

/-- The actual singleton identity family covers every represented locus. -/
theorem isFiniteCovering_top (U : Domain K A) :
    IsFiniteCovering (⊤ : Sieve U) := by
  refine ⟨PUnit.{u + 1}, inferInstance, fun _ => U, fun _ => 𝟙 U,
    fun _ => trivial, ?_⟩
  exact fun _ hx => ⟨PUnit.unit, hx⟩

/-- Refine by ambient rational charts and intersect them with the source.
The two actual bounded projections prove pullback stability without assuming
existence of arbitrary full-domain intersections. -/
theorem IsFiniteCovering.pullback {U V : Domain K A} {S : Sieve V}
    (hS : IsFiniteCovering S) (f : U ⟶ V) :
    IsFiniteCovering (S.pullback f) := by
  obtain ⟨I, hI, D, g, hg, hcover⟩ := hS.rationalRefinement
  refine ⟨I, hI, fun i => U.rationalInter (D i),
    fun i => U.rationalInterLeft (D i), ?_, ?_⟩
  · intro i
    change S (U.rationalInterLeft (D i) ≫ f)
    rw [hom_unique (U.rationalInterLeft (D i) ≫ f)
      (U.rationalInterRight (D i) ≫ g i)]
    exact S.downward_closed (hg i) (U.rationalInterRight (D i))
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x (f.subset hx)
    exact ⟨i, hx, hi⟩

/-- A finite dependent composite of covering families again covers. -/
theorem IsFiniteCovering.transitive {U : Domain K A} {S : Sieve U}
    (hS : IsFiniteCovering S) (R : Sieve U)
    (hR : ∀ ⦃V⦄ ⦃f : V ⟶ U⦄, S f → IsFiniteCovering (R.pullback f)) :
    IsFiniteCovering R := by
  classical
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  choose J hJ E g hg hcover' using fun i => hR (hf i)
  let : Finite I := hI
  let (i : I) : Finite (J i) := hJ i
  refine ⟨(i : I) × J i, inferInstance, fun ij => E ij.1 ij.2,
    fun ij => g ij.1 ij.2 ≫ f ij.1, fun ij => hg ij.1 ij.2, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  obtain ⟨j, hj⟩ := hcover' i x hi
  exact ⟨⟨i, j⟩, hj⟩

/-- The finite point-covering topology on all actual full represented domains
over a fixed positive-polyradius presented affinoid algebra. -/
def finiteDomainTopology (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (A : PresentedAffinoidAlgebra K) :
    GrothendieckTopology (Domain K A) where
  sieves _ := {S | IsFiniteCovering S}
  top_mem' := isFiniteCovering_top
  pullback_stable' := by
    intro U V S f hS
    exact hS.pullback f
  transitive' := by
    intro U S hS R hR
    exact hS.transitive R hR

@[simp]
theorem mem_finiteDomainTopology {U : Domain K A} (S : Sieve U) :
    S ∈ finiteDomainTopology K A U ↔ IsFiniteCovering S :=
  Iff.rfl

/-- The sieve generated by a finite family covers precisely when the original
represented loci cover, with the given actual bounded restrictions. -/
theorem ofArrows_mem_finiteDomainTopology_iff {I : Type u} [Finite I]
    {U : Domain K A} (D : I → Domain K A) (f : ∀ i, D i ⟶ U) :
    Sieve.ofArrows D f ∈ finiteDomainTopology K A U ↔ FamilyCovers U D := by
  constructor
  · rintro ⟨J, _, E, g, hg, hcover⟩ x hx
    obtain ⟨j, hj⟩ := hcover x hx
    obtain ⟨i, a, _⟩ := (Sieve.mem_ofArrows_iff D f (g j)).mp (hg j)
    exact ⟨i, a.subset hj⟩
  · intro hcover
    exact ⟨I, inferInstance, D, f, Sieve.ofArrows_mk D f, hcover⟩

/-- Every existing concrete finite cover generates a covering sieve. -/
theorem FiniteCover.ofArrows_mem_finiteDomainTopology {U : Domain K A}
    (c : FiniteCover U) :
    Sieve.ofArrows c.obj c.map ∈ finiteDomainTopology K A U := by
  refine ⟨ULift.{u} (Fin c.size), inferInstance,
    fun i => c.obj i.down, fun i => c.map i.down,
    fun i => Sieve.ofArrows_mk c.obj c.map i.down, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := c.covers x hx
  exact ⟨ULift.up i, hi⟩

/-- A sieve covers exactly when it contains an existing concrete finite cover. -/
theorem isFiniteCovering_iff_finiteCover {U : Domain K A} (S : Sieve U) :
    IsFiniteCovering S ↔ ∃ c : FiniteCover U, ∀ i, S (c.map i) := by
  constructor
  · rintro ⟨I, hI, D, f, hf, hcover⟩
    let := Fintype.ofFinite I
    let c := FiniteCover.ofFintype D f hcover
    exact ⟨c, fun i => hf ((Fintype.equivFin I).symm i)⟩
  · rintro ⟨c, hc⟩
    refine ⟨ULift.{u} (Fin c.size), inferInstance,
      fun i => c.obj i.down, fun i => c.map i.down, fun i => hc i.down, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := c.covers x hx
    exact ⟨ULift.up i, hi⟩

/-- The empty sieve covers exactly the empty represented loci. -/
theorem bot_mem_finiteDomainTopology_iff (U : Domain K A) :
    (⊥ : Sieve U) ∈ finiteDomainTopology K A U ↔ U.locus = ∅ := by
  constructor
  · rintro ⟨I, _, D, f, hf, hcover⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i, _⟩ := hcover x hx
    exact hf i
  · intro hempty
    refine ⟨PEmpty.{u + 1}, inferInstance, PEmpty.elim, fun i => PEmpty.elim i,
      fun i => PEmpty.elim i, ?_⟩
    intro x hx
    rw [hempty] at hx
    exact hx.elim

/-- The same criterion uses the actual quotient spectrum; no nonempty-spectrum
or nonzero-algebra assumption is imposed. -/
theorem bot_mem_finiteDomainTopology_iff_isEmpty (U : Domain K A) :
    (⊥ : Sieve U) ∈ finiteDomainTopology K A U ↔
      IsEmpty (BanachSpectrum U.algebra) := by
  rw [bot_mem_finiteDomainTopology_iff]
  constructor
  · intro h
    refine ⟨fun x => ?_⟩
    have hx := U.represents.hasImageIn x
    rw [h] at hx
    exact hx.elim
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨y, _⟩ := U.spectrumToLocus_surjective ⟨x, hx⟩
    exact h.false y

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain

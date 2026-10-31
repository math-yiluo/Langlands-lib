import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartIntersection
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Data.Fintype.Sigma

/-! # Finite point coverings of actual positive-radius rational charts -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- A family covers the actual points of the target rational locus. -/
def FamilyCovers {I : Type u} (d : RationalChart K A) (D : I → RationalChart K A) : Prop :=
  ∀ x ∈ d.locus, ∃ i, x ∈ (D i).locus

/-- A covering sieve contains a finite family of actual restrictions whose loci cover
the target. The index type is allowed to be empty. -/
def IsFiniteCovering {d : RationalChart K A} (S : Sieve d) : Prop :=
  ∃ (I : Type u) (_ : Finite I) (D : I → RationalChart K A)
    (f : ∀ i, D i ⟶ d), (∀ i, S (f i)) ∧ FamilyCovers d D

omit [CompleteSpace K] in
/-- For actual restrictions, locus coverage is equivalent to joint surjectivity
of their constructed maps on multiplicative seminorm spectra. -/
theorem familyCovers_iff_jointlySurjective {I : Type u}
    {d : RationalChart K A} (D : I → RationalChart K A) (f : ∀ i, D i ⟶ d) :
    FamilyCovers d D ↔
      ∀ y : BanachSpectrum d.algebra,
        ∃ (i : I) (z : BanachSpectrum (D i).algebra), (f i).spectrumMap z = y := by
  constructor
  · intro h y
    obtain ⟨i, hi⟩ := h _ (d.locusHomeomorph y).property
    let z := (D i).locusHomeomorph.symm ⟨d.spectrumMap y, hi⟩
    refine ⟨i, z, ?_⟩
    apply d.locusHomeomorph.injective
    apply Subtype.ext
    change d.spectrumMap ((f i).spectrumMap z) = d.spectrumMap y
    rw [(f i).spectrumMap_over_base]
    exact congrArg Subtype.val ((D i).locusHomeomorph.apply_symm_apply _)
  · intro h x hx
    let y := d.locusHomeomorph.symm ⟨x, hx⟩
    obtain ⟨i, z, hz⟩ := h y
    refine ⟨i, ?_⟩
    have hid : (D i).spectrumMap z = x := by
      calc
        (D i).spectrumMap z = d.spectrumMap ((f i).spectrumMap z) :=
          ((f i).spectrumMap_over_base z).symm
        _ = d.spectrumMap y := congrArg d.spectrumMap hz
        _ = x := congrArg Subtype.val (d.locusHomeomorph.apply_symm_apply _)
    have hmem := ((D i).locusHomeomorph z).property
    change (D i).spectrumMap z ∈ (D i).locus at hmem
    rwa [hid] at hmem

omit [CompleteSpace K] in
private theorem hom_unique {d e : RationalChart K A} (f g : d ⟶ e) : f = g :=
  @Subsingleton.elim (Restriction d e) inferInstance f g

omit [CompleteSpace K] in
/-- The singleton identity family covers every rational locus. -/
theorem isFiniteCovering_top (d : RationalChart K A) :
    IsFiniteCovering (⊤ : Sieve d) := by
  refine ⟨PUnit.{u + 1}, inferInstance, fun _ => d, fun _ => 𝟙 d,
    fun _ => trivial, ?_⟩
  exact fun _ hx => ⟨PUnit.unit, hx⟩

/-- Intersecting the covering loci with the source of an actual restriction constructs
a finite covering of its source. -/
theorem IsFiniteCovering.pullback {c d : RationalChart K A} {S : Sieve d}
    (hS : IsFiniteCovering S) (f : c ⟶ d) :
    IsFiniteCovering (S.pullback f) := by
  obtain ⟨I, hI, D, g, hg, hcover⟩ := hS
  refine ⟨I, hI, fun i => c.inter (D i), fun i => interLeft c (D i), ?_, ?_⟩
  · intro i
    change S (interLeft c (D i) ≫ f)
    rw [hom_unique (interLeft c (D i) ≫ f) (interRight c (D i) ≫ g i)]
    exact S.downward_closed (hg i) (interRight c (D i))
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x (f.subset hx)
    exact ⟨i, by rw [locus_inter]; exact ⟨hx, hi⟩⟩

omit [CompleteSpace K] in
/-- Composing finite covers constructs a finite cover indexed by a dependent
sum of the original finite index types. -/
theorem IsFiniteCovering.transitive {d : RationalChart K A} {S : Sieve d}
    (hS : IsFiniteCovering S) (R : Sieve d)
    (hR : ∀ ⦃e⦄ ⦃f : e ⟶ d⦄, S f → IsFiniteCovering (R.pullback f)) :
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

/-- The topology of finite point-covering families of chosen positive-radius
rational charts over a fixed presented affinoid. -/
def finiteRationalTopology (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (A : PresentedAffinoidAlgebra K) :
    GrothendieckTopology (RationalChart K A) where
  sieves _ := {S | IsFiniteCovering S}
  top_mem' := isFiniteCovering_top
  pullback_stable' := by
    intro c d S f hS
    exact hS.pullback f
  transitive' := by
    intro d S hS R hR
    exact hS.transitive R hR

@[simp]
theorem mem_finiteRationalTopology {d : RationalChart K A} (S : Sieve d) :
    S ∈ finiteRationalTopology K A d ↔ IsFiniteCovering S :=
  Iff.rfl

/-- A finite family generates a covering sieve exactly when its loci cover
the target locus. -/
theorem ofArrows_mem_finiteRationalTopology_iff {I : Type u} [Finite I]
    {d : RationalChart K A} (D : I → RationalChart K A) (f : ∀ i, D i ⟶ d) :
    Sieve.ofArrows D f ∈ finiteRationalTopology K A d ↔ FamilyCovers d D := by
  constructor
  · rintro ⟨J, _, E, g, hg, hcover⟩ x hx
    obtain ⟨j, hj⟩ := hcover x hx
    obtain ⟨i, a, _⟩ := (Sieve.mem_ofArrows_iff D f (g j)).mp (hg j)
    exact ⟨i, a.subset hj⟩
  · intro hcover
    exact ⟨I, inferInstance, D, f, Sieve.ofArrows_mk D f, hcover⟩

/-- The empty sieve covers exactly the empty rational loci. -/
theorem bot_mem_finiteRationalTopology_iff (d : RationalChart K A) :
    (⊥ : Sieve d) ∈ finiteRationalTopology K A d ↔ d.locus = ∅ := by
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

/-- The empty sieve covers exactly when the actual quotient spectrum is empty. -/
theorem bot_mem_finiteRationalTopology_iff_isEmpty (d : RationalChart K A) :
    (⊥ : Sieve d) ∈ finiteRationalTopology K A d ↔
      IsEmpty (BanachSpectrum d.algebra) := by
  rw [bot_mem_finiteRationalTopology_iff]
  constructor
  · intro h
    refine ⟨fun x => ?_⟩
    have hx := (d.locusHomeomorph x).property
    change d.spectrumMap x ∈ d.locus at hx
    rw [h] at hx
    exact hx.elim
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact h.false (d.locusHomeomorph.symm ⟨x, hx⟩)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

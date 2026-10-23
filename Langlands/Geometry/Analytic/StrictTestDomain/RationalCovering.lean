import Langlands.Geometry.Analytic.StrictTestDomain.RationalLimits
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Data.Fintype.Sigma

/-! # Finite rational coverings over a fixed strict affinoid base -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalData

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- A family covers the actual points of the target rational locus. -/
def FamilyCovers {I : Type u} (d : RationalData K P) (D : I → RationalData K P) : Prop :=
  ∀ x ∈ d.locus, ∃ i, x ∈ (D i).locus

/-- A covering sieve contains a finite family of inclusions whose loci cover
the target. The index type is allowed to be empty. -/
def IsFiniteCovering {d : RationalData K P} (S : Sieve d) : Prop :=
  ∃ (I : Type u) (_ : Finite I) (D : I → RationalData K P)
    (f : ∀ i, D i ⟶ d), (∀ i, S (f i)) ∧ FamilyCovers d D

omit [CompleteSpace K] in
private theorem hom_unique {d e : RationalData K P} (f g : d ⟶ e) : f = g :=
  (inferInstance : Subsingleton (Inclusion d e)).elim f g

omit [CompleteSpace K] in
/-- The singleton identity family covers every rational locus. -/
theorem isFiniteCovering_top (d : RationalData K P) :
    IsFiniteCovering (⊤ : Sieve d) := by
  refine ⟨PUnit.{u + 1}, inferInstance, fun _ => d, fun _ => 𝟙 d,
    fun _ => trivial, ?_⟩
  exact fun _ hx => ⟨PUnit.unit, hx⟩

/-- Intersecting the covering loci with the source of an inclusion constructs
a finite covering of its source. -/
theorem IsFiniteCovering.pullback {c d : RationalData K P} {S : Sieve d}
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
theorem IsFiniteCovering.transitive {d : RationalData K P} {S : Sieve d}
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

/-- The topology of finite point-covering families of chosen unit-radius
rational subdomains of a fixed presented strict affinoid. -/
def finiteRationalTopology (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (P : PresentedStrictAffinoidAlgebra K) :
    GrothendieckTopology (RationalData K P) where
  sieves _ := {S | IsFiniteCovering S}
  top_mem' := isFiniteCovering_top
  pullback_stable' := by
    intro c d S f hS
    exact hS.pullback f
  transitive' := by
    intro d S hS R hR
    exact hS.transitive R hR

@[simp]
theorem mem_finiteRationalTopology {d : RationalData K P} (S : Sieve d) :
    S ∈ finiteRationalTopology K P d ↔ IsFiniteCovering S :=
  Iff.rfl

/-- A finite family generates a covering sieve exactly when its loci cover
the target locus. -/
theorem ofArrows_mem_finiteRationalTopology_iff {I : Type u} [Finite I]
    {d : RationalData K P} (D : I → RationalData K P) (f : ∀ i, D i ⟶ d) :
    Sieve.ofArrows D f ∈ finiteRationalTopology K P d ↔ FamilyCovers d D := by
  constructor
  · rintro ⟨J, _, E, g, hg, hcover⟩ x hx
    obtain ⟨j, hj⟩ := hcover x hx
    obtain ⟨i, a, _⟩ := (Sieve.mem_ofArrows_iff D f (g j)).mp (hg j)
    exact ⟨i, a.subset hj⟩
  · intro hcover
    exact ⟨I, inferInstance, D, f, Sieve.ofArrows_mk D f, hcover⟩

/-- The empty sieve covers exactly the empty rational loci. -/
theorem bot_mem_finiteRationalTopology_iff (d : RationalData K P) :
    (⊥ : Sieve d) ∈ finiteRationalTopology K P d ↔ d.locus = ∅ := by
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

end Langlands.Analytic.StrictTestDomain.RationalData

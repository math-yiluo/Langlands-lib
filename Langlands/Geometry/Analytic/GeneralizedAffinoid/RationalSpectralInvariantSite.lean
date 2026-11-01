import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralInvariantActions
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartLimits
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCovering

/-! # Finite sites of spectral-invariant positive-radius rational charts -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits DomainAutomorphism

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G A)

/-- An ambient bounded automorphism preserving both loci preserves their
actual weighted rational intersection. -/
theorem mem_spectralLocusOpenSubgroup_inter {d e : RationalChart K A} {g : G}
    (hd : g ∈ ρ.locusOpenSubgroup d.toDomain)
    (he : g ∈ ρ.locusOpenSubgroup e.toDomain) :
    g ∈ ρ.locusOpenSubgroup (d.inter e).toDomain := by
  rw [DomainSpectralAction.mem_locusOpenSubgroup] at hd he ⊢
  change (fun x : BanachSpectrum A => ρ.toMonoidHom g • x) '' d.locus = d.locus at hd
  change (fun x : BanachSpectrum A => ρ.toMonoidHom g • x) '' e.locus = e.locus at he
  change (fun x : BanachSpectrum A => ρ.toMonoidHom g • x) '' (d.inter e).locus =
    (d.inter e).locus
  rw [locus_inter, Set.image_inter (MulAction.injective (ρ.toMonoidHom g)), hd, he]

namespace SpectralInvariantChart

variable (H : OpenSubgroup G)

private theorem hom_unique {d e : SpectralInvariantChart ρ H} (f g : d ⟶ e) :
    f = g := by
  apply ObjectProperty.hom_ext
  exact @Subsingleton.elim (Restriction d.obj e.obj) inferInstance _ _

/-- The original empty-numerator whole chart is invariant under the subgroup. -/
def whole : SpectralInvariantChart ρ H :=
  ⟨RationalChart.whole K A, fun g _ => by
    rw [DomainSpectralAction.mem_locusOpenSubgroup]
    change (fun x : BanachSpectrum A => ρ.toMonoidHom g • x) ''
      (RationalChart.whole K A).locus = (RationalChart.whole K A).locus
    rw [RationalChart.locus_whole]
    exact Set.image_univ_of_surjective (MulAction.surjective (ρ.toMonoidHom g))⟩

@[simp]
theorem locus_whole : (whole ρ H).obj.locus = Set.univ :=
  RationalChart.locus_whole K A

/-- Retain the actual bounded restriction from the whole-chart quotient. -/
def toWhole (d : SpectralInvariantChart ρ H) : d ⟶ whole ρ H :=
  ObjectProperty.homMk (RationalChart.toWhole K A d.obj)

/-- The unchanged whole quotient is terminal in the invariant chart category. -/
def wholeIsTerminal : IsTerminal (whole ρ H) :=
  IsTerminal.ofUniqueHom (toWhole ρ H) (fun _ _ => hom_unique ρ H _ _)

/-- The original product-radius intersection quotient has proved invariance. -/
def inter (d e : SpectralInvariantChart ρ H) : SpectralInvariantChart ρ H :=
  ⟨d.obj.inter e.obj, fun _ hg =>
    mem_spectralLocusOpenSubgroup_inter ρ (d.property hg) (e.property hg)⟩

@[simp]
theorem inter_obj (d e : SpectralInvariantChart ρ H) :
    (inter ρ H d e).obj = d.obj.inter e.obj := rfl

@[simp]
theorem locus_inter (d e : SpectralInvariantChart ρ H) :
    (inter ρ H d e).obj.locus = d.obj.locus ∩ e.obj.locus :=
  RationalChart.locus_inter d.obj e.obj

/-- Keep the first original bounded intersection restriction. -/
def interLeft (d e : SpectralInvariantChart ρ H) : inter ρ H d e ⟶ d :=
  ObjectProperty.homMk (RationalChart.interLeft d.obj e.obj)

/-- Keep the second original bounded intersection restriction. -/
def interRight (d e : SpectralInvariantChart ρ H) : inter ρ H d e ⟶ e :=
  ObjectProperty.homMk (RationalChart.interRight d.obj e.obj)

/-- The bounded quotient pushout constructs every simultaneous restriction. -/
def interLift {c d e : SpectralInvariantChart ρ H} (f : c ⟶ d) (g : c ⟶ e) :
    c ⟶ inter ρ H d e :=
  ObjectProperty.homMk (RationalChart.interLift f.hom g.hom)

/-- The actual invariant intersection gives a cone over any common target. -/
def pullbackCone {d e t : SpectralInvariantChart ρ H} (f : d ⟶ t) (g : e ⟶ t) :
    PullbackCone f g :=
  PullbackCone.mk (interLeft ρ H d e) (interRight ρ H d e)
    (hom_unique ρ H _ _)

/-- The existing bounded lift and restriction uniqueness prove the universal property. -/
def pullbackConeIsLimit {d e t : SpectralInvariantChart ρ H}
    (f : d ⟶ t) (g : e ⟶ t) : IsLimit (pullbackCone ρ H f g) :=
  PullbackCone.IsLimit.mk _ (fun s => interLift ρ H s.fst s.snd)
    (fun _ => hom_unique ρ H _ _) (fun _ => hom_unique ρ H _ _)
    (fun _ _ _ _ => hom_unique ρ H _ _)

instance hasTerminal : HasTerminal (SpectralInvariantChart ρ H) :=
  (wholeIsTerminal ρ H).hasTerminal

instance hasLimit_cospan {d e t : SpectralInvariantChart ρ H} (f : d ⟶ t) (g : e ⟶ t) :
    HasLimit (cospan f g) :=
  ⟨⟨pullbackCone ρ H f g, pullbackConeIsLimit ρ H f g⟩⟩

instance hasPullbacks : HasPullbacks (SpectralInvariantChart ρ H) :=
  hasPullbacks_of_hasLimit_cospan (SpectralInvariantChart ρ H)

/-- All finite limits follow from the constructed whole chart and pullbacks. -/
instance hasFiniteLimits : HasFiniteLimits (SpectralInvariantChart ρ H) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- A covering sieve contains a finite family of invariant actual charts
whose original loci cover its target. The index type may be empty. -/
def IsFiniteCovering {d : SpectralInvariantChart ρ H} (S : Sieve d) : Prop :=
  ∃ (I : Type u) (_ : Finite I) (D : I → SpectralInvariantChart ρ H)
    (f : ∀ i, D i ⟶ d), (∀ i, S (f i)) ∧
      FamilyCovers d.obj (fun i => (D i).obj)

/-- The original identity chart restriction is a singleton point cover. -/
theorem isFiniteCovering_top (d : SpectralInvariantChart ρ H) :
    IsFiniteCovering ρ H (⊤ : Sieve d) := by
  refine ⟨PUnit.{u + 1}, inferInstance, fun _ => d, fun _ => 𝟙 d,
    fun _ => trivial, ?_⟩
  exact fun _ hx => ⟨PUnit.unit, hx⟩

/-- Actual invariant intersections construct the pullback finite point cover. -/
theorem IsFiniteCovering.pullback {c d : SpectralInvariantChart ρ H} {S : Sieve d}
    (hS : IsFiniteCovering ρ H S) (f : c ⟶ d) :
    IsFiniteCovering ρ H (S.pullback f) := by
  obtain ⟨I, hI, D, g, hg, hcover⟩ := hS
  refine ⟨I, hI, fun i => inter ρ H c (D i),
    fun i => interLeft ρ H c (D i), ?_, ?_⟩
  · intro i
    change S (interLeft ρ H c (D i) ≫ f)
    rw [hom_unique ρ H (interLeft ρ H c (D i) ≫ f)
      (interRight ρ H c (D i) ≫ g i)]
    exact S.downward_closed (hg i) (interRight ρ H c (D i))
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x (f.hom.subset hx)
    exact ⟨i, by rw [locus_inter]; exact ⟨hx, hi⟩⟩

/-- A dependent sum of the finite indexing types constructs composite covers. -/
theorem IsFiniteCovering.transitive {d : SpectralInvariantChart ρ H} {S : Sieve d}
    (hS : IsFiniteCovering ρ H S) (R : Sieve d)
    (hR : ∀ ⦃e⦄ ⦃f : e ⟶ d⦄, S f → IsFiniteCovering ρ H (R.pullback f)) :
    IsFiniteCovering ρ H R := by
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

/-- The finite point-covering Grothendieck topology on the invariant charts. -/
def finiteRationalTopology : GrothendieckTopology (SpectralInvariantChart ρ H) where
  sieves _ := {S | IsFiniteCovering ρ H S}
  top_mem' := isFiniteCovering_top ρ H
  pullback_stable' := by
    intro c d S f hS
    exact hS.pullback ρ H f
  transitive' := by
    intro d S hS R hR
    exact hS.transitive ρ H R hR

@[simp]
theorem mem_finiteRationalTopology {d : SpectralInvariantChart ρ H} (S : Sieve d) :
    S ∈ finiteRationalTopology ρ H d ↔ IsFiniteCovering ρ H S := Iff.rfl

/-- A finite family generates a covering sieve exactly when its original loci cover. -/
theorem ofArrows_mem_finiteRationalTopology_iff {I : Type u} [Finite I]
    {d : SpectralInvariantChart ρ H} (D : I → SpectralInvariantChart ρ H)
    (f : ∀ i, D i ⟶ d) :
    Sieve.ofArrows D f ∈ finiteRationalTopology ρ H d ↔
      FamilyCovers d.obj (fun i => (D i).obj) := by
  constructor
  · rintro ⟨J, _, E, g, hg, hcover⟩ x hx
    obtain ⟨j, hj⟩ := hcover x hx
    obtain ⟨i, a, _⟩ := (Sieve.mem_ofArrows_iff D f (g j)).mp (hg j)
    exact ⟨i, a.hom.subset hj⟩
  · intro hcover
    exact ⟨I, inferInstance, D, f, Sieve.ofArrows_mk D f, hcover⟩

/-- Empty sieves cover precisely the invariant charts with empty actual locus. -/
theorem bot_mem_finiteRationalTopology_iff (d : SpectralInvariantChart ρ H) :
    (⊥ : Sieve d) ∈ finiteRationalTopology ρ H d ↔ d.obj.locus = ∅ := by
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

/-- Covers are exactly joint surjectivity of the original continuous
equivariant quotient-spectrum restriction maps. -/
theorem familyCovers_iff_jointlySurjective {I : Type u}
    {d : SpectralInvariantChart ρ H} (D : I → SpectralInvariantChart ρ H)
    (f : ∀ i, D i ⟶ d) :
    FamilyCovers d.obj (fun i => (D i).obj) ↔
      ∀ x : BanachSpectrum d.obj.algebra,
        ∃ (i : I) (y : BanachSpectrum (D i).obj.algebra),
          ((spectralInvariantSpectrumFunctor ρ H).map (f i)).hom.hom y = x :=
  RationalChart.familyCovers_iff_jointlySurjective (fun i => (D i).obj)
    (fun i => (f i).hom)

end SpectralInvariantChart

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

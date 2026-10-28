import Langlands.Geometry.Analytic.StrictTestDomain.OpenSubgroupTransport
import Langlands.Geometry.Analytic.StrictTestDomain.RationalTransportCovering

/-! # Finite coverings with varying open operator subgroups -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

/-- Actual labelled point images cover the target rational locus. -/
def FamilyCovers {I : Type u} {V : ρ.OpenSubgroupTransport}
    (D : I → ρ.OpenSubgroupTransport) (f : ∀ i, D i ⟶ V) : Prop :=
  ∀ x ∈ V.domain.obj.locus,
    ∃ i, ∃ y ∈ (D i).domain.obj.locus, ρ.toMonoidHom (f i).label • y = x

/-- A finite family of actual subgroup-labelled arrows witnesses covering.
The finite index type may be empty. -/
def IsFiniteCovering {V : ρ.OpenSubgroupTransport} (S : Sieve V) : Prop :=
  ∃ (I : Type u) (_ : Finite I) (D : I → ρ.OpenSubgroupTransport)
    (f : ∀ i, D i ⟶ V), (∀ i, S (f i)) ∧ FamilyCovers D f

theorem isFiniteCovering_top (V : ρ.OpenSubgroupTransport) :
    IsFiniteCovering (⊤ : Sieve V) := by
  refine ⟨PUnit.{u + 1}, inferInstance, fun _ => V, fun _ => 𝟙 V,
    fun _ => True.intro, ?_⟩
  exact fun x hx => ⟨PUnit.unit, x, hx, by simp⟩

/-- The open subgroup supporting the translated rational intersection. -/
def refinementSubgroup {U V W : ρ.OpenSubgroupTransport} (f : V ⟶ W) (g : U ⟶ W) :
    OpenSubgroup G :=
  V.subgroup ⊓ conjugateOpenSubgroup U.subgroup (f.label⁻¹ * g.label)

/-- An actual rational intersection with the common conjugate open subgroup. -/
def refinement {U V W : ρ.OpenSubgroupTransport} (f : V ⟶ W) (g : U ⟶ W) :
    ρ.OpenSubgroupTransport where
  subgroup := refinementSubgroup f g
  domain :=
    ⟨V.domain.obj.inter (ρ.toMonoidHom (f.label⁻¹ * g.label) • U.domain.obj),
      fun k hk => ρ.mem_locusOpenSubgroup_inter
        (V.domain.property hk.1)
        ((ρ.mem_locusOpenSubgroup_smul_iff (f.label⁻¹ * g.label) k U.domain.obj).mpr
          (U.domain.property
            ((mem_conjugateOpenSubgroup U.subgroup (f.label⁻¹ * g.label) k).mp hk.2)))⟩

/-- The first refinement arrow has identity label and subgroup inclusion. -/
def refinementLeft {U V W : ρ.OpenSubgroupTransport} (f : V ⟶ W) (g : U ⟶ W) :
    refinement f g ⟶ V :=
  ⟨1, by
    intro k hk
    change k ∈ conjugateOpenSubgroup (refinementSubgroup f g) 1 at hk
    have hk' : k ∈ refinementSubgroup f g := by simpa using hk
    exact hk'.1, by
    intro x hx
    change x ∈
      (V.domain.obj.inter (ρ.toMonoidHom (f.label⁻¹ * g.label) • U.domain.obj)).locus at hx
    rw [RationalData.locus_inter] at hx
    simpa using hx.1⟩

/-- The second arrow undoes relative translation, including its subgroup. -/
def refinementRight {U V W : ρ.OpenSubgroupTransport} (f : V ⟶ W) (g : U ⟶ W) :
    refinement f g ⟶ U :=
  ⟨g.label⁻¹ * f.label, by
    intro k hk
    have hk' :
        (g.label⁻¹ * f.label)⁻¹ * k * (g.label⁻¹ * f.label) ∈
          V.subgroup ⊓ conjugateOpenSubgroup U.subgroup (f.label⁻¹ * g.label) :=
      (mem_conjugateOpenSubgroup _ _ _).mp hk
    have h := (mem_conjugateOpenSubgroup _ _ _).mp hk'.2
    simpa [mul_assoc] using h, by
    intro x hx
    change x ∈
      (V.domain.obj.inter (ρ.toMonoidHom (f.label⁻¹ * g.label) • U.domain.obj)).locus at hx
    rw [RationalData.locus_inter] at hx
    have h := (smul_mem_smul_locus_iff
      (ρ.toMonoidHom (f.label⁻¹ * g.label)) U.domain.obj
      ((ρ.toMonoidHom (f.label⁻¹ * g.label))⁻¹ • x)).mp (by
        simpa only [smul_inv_smul] using hx.2)
    simpa only [map_mul, map_inv, mul_inv_rev, inv_inv] using h⟩

/-- The square commutes as actual labelled arrows. -/
theorem refinement_comm {U V W : ρ.OpenSubgroupTransport} (f : V ⟶ W) (g : U ⟶ W) :
    refinementLeft f g ≫ f = refinementRight f g ≫ g := by
  apply Hom.ext
  change f.label * 1 = g.label * (g.label⁻¹ * f.label)
  simp

/-- Translated rational intersections at their common open subgroups refine
every finite cover along every labelled arrow. -/
theorem IsFiniteCovering.pullback {V W : ρ.OpenSubgroupTransport} {S : Sieve W}
    (hS : IsFiniteCovering S) (f : V ⟶ W) :
    IsFiniteCovering (S.pullback f) := by
  obtain ⟨I, hI, D, g, hg, hcover⟩ := hS
  refine ⟨I, hI, fun i => refinement f (g i), fun i => refinementLeft f (g i), ?_, ?_⟩
  · intro i
    change S (refinementLeft f (g i) ≫ f)
    rw [refinement_comm]
    exact S.downward_closed (hg i) (refinementRight f (g i))
  · intro x hx
    obtain ⟨i, y, hy, heq⟩ := hcover (ρ.toMonoidHom f.label • x) (f.mapsTo x hx)
    refine ⟨i, x, ?_, by simp [refinementLeft]⟩
    change x ∈
      (V.domain.obj.inter (ρ.toMonoidHom (f.label⁻¹ * (g i).label) •
        (D i).domain.obj)).locus
    rw [RationalData.locus_inter, locus_smul]
    refine ⟨hx, y, hy, ?_⟩
    simp only [map_mul, map_inv, mul_smul, heq, inv_smul_smul]

/-- Finite dependent sums compose actual point-image covering families. -/
theorem IsFiniteCovering.transitive {V : ρ.OpenSubgroupTransport} {S : Sieve V}
    (hS : IsFiniteCovering S) (R : Sieve V)
    (hR : ∀ ⦃U⦄ ⦃f : U ⟶ V⦄, S f → IsFiniteCovering (R.pullback f)) :
    IsFiniteCovering R := by
  classical
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  choose J hJ E g hg hcover' using fun i => hR (hf i)
  let : Finite I := hI
  let (i : I) : Finite (J i) := hJ i
  refine ⟨(i : I) × J i, inferInstance, fun ij => E ij.1 ij.2,
    fun ij => g ij.1 ij.2 ≫ f ij.1, fun ij => hg ij.1 ij.2, ?_⟩
  intro x hx
  obtain ⟨i, y, hy, heq⟩ := hcover x hx
  obtain ⟨j, z, hz, heq'⟩ := hcover' i y hy
  refine ⟨⟨i, j⟩, z, hz, ?_⟩
  simpa only [comp_label, map_mul, mul_smul, heq'] using heq

/-- The finite point-image covering topology with varying open subgroups. -/
def finiteTopology (ρ : RationalSpectralAction G P) :
    GrothendieckTopology (ρ.OpenSubgroupTransport) where
  sieves _ := {S | IsFiniteCovering S}
  top_mem' := isFiniteCovering_top
  pullback_stable' := by
    intro V W S f hS
    exact hS.pullback f
  transitive' := by
    intro V S hS R hR
    exact hS.transitive R hR

@[simp]
theorem mem_finiteTopology {V : ρ.OpenSubgroupTransport} (S : Sieve V) :
    S ∈ finiteTopology ρ V ↔ IsFiniteCovering S := Iff.rfl

/-- A finite family generates a covering sieve exactly when its images cover. -/
theorem ofArrows_mem_finiteTopology_iff {I : Type u} [Finite I]
    {V : ρ.OpenSubgroupTransport} (D : I → ρ.OpenSubgroupTransport) (f : ∀ i, D i ⟶ V) :
    Sieve.ofArrows D f ∈ finiteTopology ρ V ↔ FamilyCovers D f := by
  constructor
  · rintro ⟨J, _, E, g, hg, hcover⟩ x hx
    obtain ⟨j, y, hy, heq⟩ := hcover x hx
    obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff D f (g j)).mp (hg j)
    refine ⟨i, ρ.toMonoidHom a.label • y, a.mapsTo y hy, ?_⟩
    rw [ha, comp_label, map_mul, mul_smul] at heq
    exact heq
  · intro hcover
    exact ⟨I, inferInstance, D, f, Sieve.ofArrows_mk D f, hcover⟩

/-- The empty sieve covers precisely the objects with empty actual locus. -/
theorem bot_mem_finiteTopology_iff (V : ρ.OpenSubgroupTransport) :
    (⊥ : Sieve V) ∈ finiteTopology ρ V ↔ V.domain.obj.locus = ∅ := by
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

/-- Forgetting the subgroups retains exactly the actual point-image condition. -/
theorem familyCovers_forget_iff {I : Type u} {V : ρ.OpenSubgroupTransport}
    (D : I → ρ.OpenSubgroupTransport) (f : ∀ i, D i ⟶ V) :
    RationalTransport.FamilyCovers (fun i => toRationalTransport.obj (D i))
        (fun i => toRationalTransport.map (f i)) ↔ FamilyCovers D f :=
  Iff.rfl

/-- The actual forgetful functor preserves finite covering sieves. -/
theorem toRationalTransport_coverPreserving :
    CoverPreserving (finiteTopology ρ) (RationalTransport.finiteTopology K P)
      toRationalTransport := by
  constructor
  intro V S hS
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  refine ⟨I, hI, fun i => toRationalTransport.obj (D i),
    fun i => toRationalTransport.map (f i), ?_, hcover⟩
  intro i
  exact Sieve.image_mem_functorPushforward toRationalTransport S (hf i)

/-- Factoring a cover of the image sieve through its original arrows recovers
a finite covering family in the subgroup-labelled category. -/
theorem isFiniteCovering_of_forget_pushforward {V : ρ.OpenSubgroupTransport}
    {S : Sieve V}
    (hS : RationalTransport.IsFiniteCovering (S.functorPushforward toRationalTransport)) :
    IsFiniteCovering S := by
  classical
  obtain ⟨I, hI, E, g, hg, hcover⟩ := hS
  choose D f a hf heq using hg
  refine ⟨I, hI, D, f, hf, ?_⟩
  intro x hx
  obtain ⟨i, y, hy, hxy⟩ := hcover x hx
  refine ⟨i, (a i).label • y, (a i).mapsTo y hy, ?_⟩
  rw [heq i, RationalTransport.comp_label, mul_smul] at hxy
  exact hxy

/-- Forgetting subgroups preserves and reflects covering of image sieves. -/
theorem forget_pushforward_mem_iff {V : ρ.OpenSubgroupTransport} (S : Sieve V) :
    S.functorPushforward toRationalTransport ∈
        RationalTransport.finiteTopology K P (toRationalTransport.obj V) ↔
      S ∈ finiteTopology ρ V :=
  ⟨isFiniteCovering_of_forget_pushforward,
    fun hS => toRationalTransport_coverPreserving.cover_preserve hS⟩

/-- Fixed-subgroup inclusions have identity label, so the original loci cover
exactly when the associated labelled point images cover. -/
theorem familyCovers_inclusion_iff (U : OpenSubgroup G) {I : Type u}
    {d : ρ.InvariantRationalDomain U} (D : I → ρ.InvariantRationalDomain U)
    (f : ∀ i, D i ⟶ d) :
    FamilyCovers (fun i => (inclusion U).obj (D i))
        (fun i => (inclusion U).map (f i)) ↔
      RationalData.FamilyCovers d.obj (fun i => (D i).obj) := by
  constructor
  · intro h x hx
    obtain ⟨i, y, hy, heq⟩ := h x hx
    change ρ.toMonoidHom 1 • y = x at heq
    simp only [map_one, one_smul] at heq
    exact ⟨i, heq ▸ hy⟩
  · intro h x hx
    obtain ⟨i, hi⟩ := h x hx
    exact ⟨i, x, hi, by change ρ.toMonoidHom 1 • x = x; simp⟩

/-- Every fixed-subgroup rational inclusion functor preserves finite covers. -/
theorem inclusion_coverPreserving (U : OpenSubgroup G) :
    CoverPreserving (InvariantRationalDomain.finiteRationalTopology ρ U)
      (finiteTopology ρ) (inclusion U) := by
  constructor
  intro d S hS
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  refine ⟨I, hI, fun i => (inclusion U).obj (D i),
    fun i => (inclusion U).map (f i), ?_,
      (familyCovers_inclusion_iff U D f).mpr hcover⟩
  intro i
  exact Sieve.image_mem_functorPushforward (inclusion U) S (hf i)

/-- The covering condition is exactly joint surjectivity of the constructed
continuous equivariant maps between actual quotient spectra. -/
theorem familyCovers_iff_jointly_surjective {I : Type u} {V : ρ.OpenSubgroupTransport}
    (D : I → ρ.OpenSubgroupTransport) (f : ∀ i, D i ⟶ V) :
    FamilyCovers D f ↔
      ∀ x : BanachSpectrum V.domain.obj.algebra,
        ∃ (i : I) (y : BanachSpectrum (D i).domain.obj.algebra),
          (f i).equivariantSpectrumMap.hom.hom y = x := by
  constructor
  · intro hcover x
    obtain ⟨i, y, hy, heq⟩ := hcover _ (V.domain.obj.baseMap_hasImageIn x)
    rw [← (rationalRepresentation K P (D i).domain.obj).2.1] at hy
    obtain ⟨z, hz⟩ := hy
    change (D i).domain.obj.spectrumMap z = y at hz
    refine ⟨i, z, ?_⟩
    apply RationalLocalization.comap_baseMap_injective K P V.domain.obj.arity
      V.domain.obj.denominator V.domain.obj.numerator V.domain.obj.generatesUnitIdeal
    change V.domain.obj.spectrumMap
      (BanachSpectrum.comap (f i).restriction.toBoundedRingHom z) =
        V.domain.obj.spectrumMap x
    rw [(f i).spectrumMap_restriction, hz]
    exact heq
  · intro hsurj x hx
    rw [← (rationalRepresentation K P V.domain.obj).2.1] at hx
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨i, y, hy⟩ := hsurj z
    refine ⟨i, (D i).domain.obj.spectrumMap y,
      (D i).domain.obj.baseMap_hasImageIn y, ?_⟩
    have htriangle := (f i).spectrumMap_restriction y
    change V.domain.obj.spectrumMap ((f i).equivariantSpectrumMap.hom.hom y) =
      ρ.toMonoidHom (f i).label • (D i).domain.obj.spectrumMap y at htriangle
    rw [hy] at htriangle
    exact htriangle.symm

/-- Restricting only the operator subgroup gives a singleton cover with
unchanged quotient algebra and identity point map. -/
theorem subgroupRestriction_familyCovers {U V : OpenSubgroup G} (h : V ≤ U)
    (d : ρ.InvariantRationalDomain U) :
    FamilyCovers
      (fun _ : PUnit.{u + 1} =>
        (inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d))
      (fun _ => subgroupRestriction h d) := by
  intro x hx
  exact ⟨PUnit.unit, x, hx, by
    change ρ.toMonoidHom 1 • x = x
    simp⟩

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

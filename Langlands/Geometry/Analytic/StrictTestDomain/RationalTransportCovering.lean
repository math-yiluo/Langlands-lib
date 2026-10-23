import Langlands.Geometry.Analytic.StrictTestDomain.RationalTransport

/-! # Finite point-image coverings in the rational transport category -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalTransport

open CategoryTheory RationalAutomorphism

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- A family covers when its labelled point images cover the target locus. -/
def FamilyCovers {I : Type u} {V : RationalTransport K P}
    (D : I → RationalTransport K P) (f : ∀ i, D i ⟶ V) : Prop :=
  ∀ x ∈ V.data.locus, ∃ i, ∃ y ∈ (D i).data.locus, (f i).label • y = x

/-- A covering sieve contains a finite jointly point-surjective family.
The index type can be empty. -/
def IsFiniteCovering {V : RationalTransport K P} (S : Sieve V) : Prop :=
  ∃ (I : Type u) (_ : Finite I) (D : I → RationalTransport K P)
    (f : ∀ i, D i ⟶ V), (∀ i, S (f i)) ∧ FamilyCovers D f

/-- The singleton identity family covers. -/
theorem isFiniteCovering_top (V : RationalTransport K P) :
    IsFiniteCovering (⊤ : Sieve V) := by
  refine ⟨PUnit.{u + 1}, inferInstance, fun _ => V, fun _ => 𝟙 V,
    fun _ => trivial, ?_⟩
  exact fun x hx => ⟨PUnit.unit, x, hx, one_smul _ x⟩

variable [CompleteSpace K]

/-- The actual rational intersection used to refine a labelled arrow along
another labelled arrow with the same target. -/
def refinement {U V W : RationalTransport K P} (f : V ⟶ W) (g : U ⟶ W) :
    RationalTransport K P :=
  ⟨V.data.inter ((f.label⁻¹ * g.label) • U.data)⟩

/-- The refinement embeds in the source of the base-change arrow. -/
def refinementLeft {U V W : RationalTransport K P} (f : V ⟶ W) (g : U ⟶ W) :
    refinement f g ⟶ V :=
  ⟨1, by
    intro x hx
    change x ∈ (V.data.inter ((f.label⁻¹ * g.label) • U.data)).locus at hx
    rw [RationalData.locus_inter] at hx
    simpa using hx.1⟩

/-- The second map undoes the relative translation of the covering source. -/
def refinementRight {U V W : RationalTransport K P} (f : V ⟶ W) (g : U ⟶ W) :
    refinement f g ⟶ U :=
  ⟨g.label⁻¹ * f.label, by
    intro x hx
    change x ∈ (V.data.inter ((f.label⁻¹ * g.label) • U.data)).locus at hx
    rw [RationalData.locus_inter] at hx
    have h := (smul_mem_smul_locus_iff (f.label⁻¹ * g.label) U.data
      ((f.label⁻¹ * g.label)⁻¹ • x)).mp (by
        simpa only [smul_inv_smul] using hx.2)
    simpa only [mul_inv_rev, inv_inv] using h⟩

/-- The refinement square commutes with the retained automorphism labels. -/
theorem refinement_comm {U V W : RationalTransport K P} (f : V ⟶ W) (g : U ⟶ W) :
    refinementLeft f g ≫ f = refinementRight f g ≫ g := by
  apply Hom.ext
  change f.label * 1 = g.label * (g.label⁻¹ * f.label)
  simp

/-- Translated rational intersections produce a finite covering of the source
of any transport arrow. -/
theorem IsFiniteCovering.pullback {V W : RationalTransport K P} {S : Sieve W}
    (hS : IsFiniteCovering S) (f : V ⟶ W) :
    IsFiniteCovering (S.pullback f) := by
  obtain ⟨I, hI, D, g, hg, hcover⟩ := hS
  refine ⟨I, hI, fun i => refinement f (g i), fun i => refinementLeft f (g i), ?_, ?_⟩
  · intro i
    change S (refinementLeft f (g i) ≫ f)
    rw [refinement_comm]
    exact S.downward_closed (hg i) (refinementRight f (g i))
  · intro x hx
    obtain ⟨i, y, hy, heq⟩ := hcover (f.label • x) (f.mapsTo x hx)
    refine ⟨i, x, ?_, one_smul _ x⟩
    change x ∈ (V.data.inter ((f.label⁻¹ * (g i).label) • (D i).data)).locus
    rw [RationalData.locus_inter, locus_smul]
    refine ⟨hx, y, hy, ?_⟩
    simp only [mul_smul, heq, inv_smul_smul]

omit [CompleteSpace K] in
/-- Finite dependent sums of composite families prove transitivity. -/
theorem IsFiniteCovering.transitive {V : RationalTransport K P} {S : Sieve V}
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
  simpa only [comp_label, mul_smul, heq'] using heq

/-- The constructed finite covering topology on chosen rational presentations
and bounded-automorphism-labelled arrows. -/
def finiteTopology (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (P : PresentedStrictAffinoidAlgebra K) :
    GrothendieckTopology (RationalTransport K P) where
  sieves _ := {S | IsFiniteCovering S}
  top_mem' := isFiniteCovering_top
  pullback_stable' := by
    intro V W S f hS
    exact hS.pullback f
  transitive' := by
    intro V S hS R hR
    exact hS.transitive R hR

@[simp] theorem mem_finiteTopology {V : RationalTransport K P} (S : Sieve V) :
    S ∈ finiteTopology K P V ↔ IsFiniteCovering S := Iff.rfl

/-- A finite family generates a covering sieve exactly when its actual
labelled images cover. -/
theorem ofArrows_mem_finiteTopology_iff {I : Type u} [Finite I]
    {V : RationalTransport K P} (D : I → RationalTransport K P) (f : ∀ i, D i ⟶ V) :
    Sieve.ofArrows D f ∈ finiteTopology K P V ↔ FamilyCovers D f := by
  constructor
  · rintro ⟨J, _, E, g, hg, hcover⟩ x hx
    obtain ⟨j, y, hy, heq⟩ := hcover x hx
    obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff D f (g j)).mp (hg j)
    refine ⟨i, a.label • y, a.mapsTo y hy, ?_⟩
    rw [ha, comp_label, mul_smul] at heq
    exact heq
  · intro hcover
    exact ⟨I, inferInstance, D, f, Sieve.ofArrows_mk D f, hcover⟩

/-- The empty sieve covers precisely the empty loci. -/
theorem bot_mem_finiteTopology_iff (V : RationalTransport K P) :
    (⊥ : Sieve V) ∈ finiteTopology K P V ↔ V.data.locus = ∅ := by
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

omit [CompleteSpace K] in
/-- Ordinary rational inclusions cover in the transport category exactly
when their original loci cover. -/
theorem familyCovers_inclusion_iff {I : Type u} {d : RationalData K P}
    (D : I → RationalData K P) (f : ∀ i, D i ⟶ d) :
    FamilyCovers (fun i => inclusion.obj (D i)) (fun i => inclusion.map (f i)) ↔
      RationalData.FamilyCovers d D := by
  constructor
  · intro h x hx
    obtain ⟨i, y, hy, heq⟩ := h x hx
    change (1 : Aut P) • y = x at heq
    simp only [one_smul] at heq
    exact ⟨i, heq ▸ hy⟩
  · intro h x hx
    obtain ⟨i, hi⟩ := h x hx
    exact ⟨i, x, hi, one_smul _ x⟩

/-- The inclusion of the ordinary rational site preserves finite covers. -/
theorem inclusion_coverPreserving :
    CoverPreserving (RationalData.finiteRationalTopology K P) (finiteTopology K P)
      inclusion := by
  constructor
  intro d S hS
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  refine ⟨I, hI, fun i => inclusion.obj (D i), fun i => inclusion.map (f i), ?_,
    (familyCovers_inclusion_iff D f).mpr hcover⟩
  intro i
  exact Sieve.image_mem_functorPushforward inclusion S (hf i)

end Langlands.Analytic.StrictTestDomain.RationalTransport

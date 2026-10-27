import Langlands.Geometry.Analytic.StrictTestDomain.SpectralOverBase
import Langlands.Geometry.Analytic.StrictTestDomain.RationalCovering

/-! # Finite coverings of invariant rational quotient domains -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : RationalSpectralAction G P)

/-- The setwise stabilizers of two rational loci stabilize their constructed
intersection, since the ambient spectrum operators are bijections. -/
theorem mem_locusOpenSubgroup_inter {d e : RationalData K P} {g : G}
    (hd : g ∈ ρ.locusOpenSubgroup d) (he : g ∈ ρ.locusOpenSubgroup e) :
    g ∈ ρ.locusOpenSubgroup (d.inter e) := by
  rw [mem_locusOpenSubgroup] at hd he ⊢
  rw [RationalData.locus_inter, Set.image_inter (MulAction.injective (ρ.toMonoidHom g)),
    hd, he]

namespace InvariantRationalDomain

variable (U : OpenSubgroup G)

private theorem hom_unique {d e : ρ.InvariantRationalDomain U} (f g : d ⟶ e) :
    f = g := by
  apply ObjectProperty.hom_ext
  exact (inferInstance : Subsingleton (RationalData.Inclusion d.obj e.obj)).elim _ _

/-- The existing empty-numerator quotient presents an invariant whole locus. -/
def whole : ρ.InvariantRationalDomain U :=
  ⟨RationalData.whole K P, fun _ _ => ρ.mem_wholeLocusOpenSubgroup _⟩

@[simp]
theorem locus_whole : (whole ρ U).obj.locus = Set.univ :=
  RationalData.locus_whole

/-- Every invariant rational domain includes into the invariant whole locus. -/
def toWhole (d : ρ.InvariantRationalDomain U) : d ⟶ whole ρ U :=
  ObjectProperty.homMk d.obj.toWhole

/-- The constructed whole rational quotient is terminal in the invariant category. -/
def wholeIsTerminal : IsTerminal (whole ρ U) :=
  IsTerminal.ofUniqueHom (toWhole ρ U) (fun _ _ => hom_unique ρ U _ _)

/-- The existing product-denominator rational quotient is invariant under U. -/
def inter (d e : ρ.InvariantRationalDomain U) : ρ.InvariantRationalDomain U :=
  ⟨d.obj.inter e.obj, fun _ hg =>
    ρ.mem_locusOpenSubgroup_inter (d.property hg) (e.property hg)⟩

@[simp]
theorem inter_obj (d e : ρ.InvariantRationalDomain U) :
    (inter ρ U d e).obj = d.obj.inter e.obj := rfl

@[simp]
theorem locus_inter (d e : ρ.InvariantRationalDomain U) :
    (inter ρ U d e).obj.locus = d.obj.locus ∩ e.obj.locus :=
  RationalData.locus_inter _ _

/-- The first actual rational intersection inclusion. -/
def interLeft (d e : ρ.InvariantRationalDomain U) : inter ρ U d e ⟶ d :=
  ObjectProperty.homMk (RationalData.interLeft d.obj e.obj)

/-- The second actual rational intersection inclusion. -/
def interRight (d e : ρ.InvariantRationalDomain U) : inter ρ U d e ⟶ e :=
  ObjectProperty.homMk (RationalData.interRight d.obj e.obj)

/-- Simultaneous inclusion gives inclusion into the constructed intersection. -/
def interLift {c d e : ρ.InvariantRationalDomain U} (f : c ⟶ d) (g : c ⟶ e) :
    c ⟶ inter ρ U d e :=
  ObjectProperty.homMk (RationalData.interLift f.hom g.hom)

/-- The constructed invariant intersection is a pullback cone over inclusions. -/
def pullbackCone {d e t : ρ.InvariantRationalDomain U} (f : d ⟶ t) (g : e ⟶ t) :
    PullbackCone f g :=
  PullbackCone.mk (interLeft ρ U d e) (interRight ρ U d e) (hom_unique ρ U _ _)

/-- The intersection cone has the universal property in the invariant category. -/
def pullbackConeIsLimit {d e t : ρ.InvariantRationalDomain U}
    (f : d ⟶ t) (g : e ⟶ t) : IsLimit (pullbackCone ρ U f g) :=
  PullbackCone.IsLimit.mk _ (fun s => interLift ρ U s.fst s.snd)
    (fun _ => hom_unique ρ U _ _) (fun _ => hom_unique ρ U _ _)
    (fun _ _ _ _ => hom_unique ρ U _ _)

/-- A sieve contains a finite point-covering family of invariant rational
quotients. The finite index type may be empty. -/
def IsFiniteCovering {d : ρ.InvariantRationalDomain U} (S : Sieve d) : Prop :=
  ∃ (I : Type u) (_ : Finite I) (D : I → ρ.InvariantRationalDomain U)
    (f : ∀ i, D i ⟶ d), (∀ i, S (f i)) ∧
      RationalData.FamilyCovers d.obj (fun i => (D i).obj)

/-- The identity family covers every invariant rational locus. -/
theorem isFiniteCovering_top (d : ρ.InvariantRationalDomain U) :
    IsFiniteCovering ρ U (⊤ : Sieve d) := by
  refine ⟨PUnit.{u + 1}, inferInstance, fun _ => d, fun _ => 𝟙 d,
    fun _ => True.intro, ?_⟩
  exact fun _ hx => ⟨PUnit.unit, hx⟩

/-- The actual invariant intersections construct pullbacks of finite covers. -/
theorem IsFiniteCovering.pullback {c d : ρ.InvariantRationalDomain U} {S : Sieve d}
    (hS : IsFiniteCovering ρ U S) (f : c ⟶ d) :
    IsFiniteCovering ρ U (S.pullback f) := by
  obtain ⟨I, hI, D, g, hg, hcover⟩ := hS
  refine ⟨I, hI, fun i => inter ρ U c (D i),
    fun i => interLeft ρ U c (D i), ?_, ?_⟩
  · intro i
    change S (interLeft ρ U c (D i) ≫ f)
    rw [hom_unique ρ U (interLeft ρ U c (D i) ≫ f)
      (interRight ρ U c (D i) ≫ g i)]
    exact S.downward_closed (hg i) (interRight ρ U c (D i))
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x (f.hom.subset hx)
    exact ⟨i, by rw [locus_inter]; exact ⟨hx, hi⟩⟩

/-- Dependent sums of finite index types construct composites of finite covers. -/
theorem IsFiniteCovering.transitive {d : ρ.InvariantRationalDomain U} {S : Sieve d}
    (hS : IsFiniteCovering ρ U S) (R : Sieve d)
    (hR : ∀ ⦃e⦄ ⦃f : e ⟶ d⦄, S f → IsFiniteCovering ρ U (R.pullback f)) :
    IsFiniteCovering ρ U R := by
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

/-- The finite point-covering topology on actual U-invariant rational quotients. -/
def finiteRationalTopology : GrothendieckTopology (ρ.InvariantRationalDomain U) where
  sieves _ := {S | IsFiniteCovering ρ U S}
  top_mem' := isFiniteCovering_top ρ U
  pullback_stable' := by
    intro c d S f hS
    exact hS.pullback ρ U f
  transitive' := by
    intro d S hS R hR
    exact hS.transitive ρ U R hR

@[simp]
theorem mem_finiteRationalTopology {d : ρ.InvariantRationalDomain U} (S : Sieve d) :
    S ∈ finiteRationalTopology ρ U d ↔ IsFiniteCovering ρ U S :=
  Iff.rfl

/-- A finite invariant family generates a cover exactly when its actual loci cover. -/
theorem ofArrows_mem_finiteRationalTopology_iff {I : Type u} [Finite I]
    {d : ρ.InvariantRationalDomain U} (D : I → ρ.InvariantRationalDomain U)
    (f : ∀ i, D i ⟶ d) :
    Sieve.ofArrows D f ∈ finiteRationalTopology ρ U d ↔
      RationalData.FamilyCovers d.obj (fun i => (D i).obj) := by
  constructor
  · rintro ⟨J, _, E, g, hg, hcover⟩ x hx
    obtain ⟨j, hj⟩ := hcover x hx
    obtain ⟨i, a, _⟩ := (Sieve.mem_ofArrows_iff D f (g j)).mp (hg j)
    exact ⟨i, a.hom.subset hj⟩
  · intro hcover
    exact ⟨I, inferInstance, D, f, Sieve.ofArrows_mk D f, hcover⟩

/-- The empty sieve covers exactly the invariant domains with empty actual locus. -/
theorem bot_mem_finiteRationalTopology_iff (d : ρ.InvariantRationalDomain U) :
    (⊥ : Sieve d) ∈ finiteRationalTopology ρ U d ↔ d.obj.locus = ∅ := by
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

/-- Locus coverings are exactly joint surjectivity of the actual continuous
equivariant spectrum maps supplied by the existing spectrum diagram. -/
theorem familyCovers_iff_jointly_surjective {I : Type u}
    {d : ρ.InvariantRationalDomain U} (D : I → ρ.InvariantRationalDomain U)
    (f : ∀ i, D i ⟶ d) :
    RationalData.FamilyCovers d.obj (fun i => (D i).obj) ↔
      ∀ x : BanachSpectrum d.obj.algebra,
        ∃ (i : I) (y : BanachSpectrum (D i).obj.algebra),
          ((ρ.invariantSpectrumFunctor U).map (f i)).hom.hom y = x := by
  constructor
  · intro hcover x
    obtain ⟨i, hi⟩ := hcover _ (d.obj.baseMap_hasImageIn x)
    rw [← (rationalRepresentation K P (D i).obj).2.1] at hi
    obtain ⟨y, hy⟩ := hi
    refine ⟨i, y, ?_⟩
    apply RationalLocalization.comap_baseMap_injective K P d.obj.arity
      d.obj.denominator d.obj.numerator d.obj.generatesUnitIdeal
    change d.obj.spectrumMap
      (BanachSpectrum.comap (f i).hom.restriction.toBoundedRingHom y) =
        d.obj.spectrumMap x
    rw [(f i).hom.spectrumMap_restriction]
    exact hy
  · intro hsurj x hx
    rw [← (rationalRepresentation K P d.obj).2.1] at hx
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨i, y, hy⟩ := hsurj z
    refine ⟨i, ?_⟩
    have htriangle := (f i).hom.spectrumMap_restriction y
    change d.obj.spectrumMap
      (((ρ.invariantSpectrumFunctor U).map (f i)).hom.hom y) =
        (D i).obj.spectrumMap y at htriangle
    rw [hy] at htriangle
    change d.obj.spectrumMap z ∈ (D i).obj.locus
    rw [htriangle]
    exact (D i).obj.baseMap_hasImageIn y

end InvariantRationalDomain

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

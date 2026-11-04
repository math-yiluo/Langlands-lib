import Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceStatement
import Langlands.GroupScheme.SimplyConnected.SplitCriterionReduction
import Langlands.GroupScheme.CentralIsogeny.SplitMaximalTorusLiftProof
import Langlands.GroupScheme.CentralIsogeny.PerfectComposition
import Langlands.GroupScheme.Derived.SemisimplePerfectStatement
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanReduction
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity

/-! # Simply connected central covers from a minimal coweight lattice -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G : GroupScheme (Spec (CommRingCat.of k))} {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A **split central cover candidate** of a group `G` with a torus `i : T ⟶ G`: a semisimple
group `C` with a central isogeny `π : C ⟶ G`, a split maximal torus `j : S ⟶ C` and a
homomorphism `t : S ⟶ T` with `j ≫ π = t ≫ i`. -/
structure SplitCentralCoverCandidate (i : T.toGrp ⟶ G) where
  /-- The covering group. -/
  C : GroupScheme (Spec (CommRingCat.of k))
  /-- The covering map. -/
  π : C ⟶ G
  isSemisimple : IsSemisimple C
  isCentralIsogeny : IsCentralIsogeny π
  /-- The split maximal torus of the covering group. -/
  S : CommGroupScheme (Spec (CommRingCat.of k))
  /-- The inclusion of the split maximal torus. -/
  j : S.toGrp ⟶ C
  isSplitTorus : IsSplitTorus S.toGrp
  isMaximalTorus : IsMaximalTorus j
  /-- The map of tori lying over `π`. -/
  t : S ⟶ T
  comm : j ≫ π = CommGroupScheme.groupHom t ≫ i

namespace SplitCentralCoverCandidate

variable {i : T.toGrp ⟶ G}

/-- The coweight image `{ν ≫ t | ν ∈ X_*(S)}` of a candidate in the cocharacter lattice of `T`. -/
def coweightImage (c : SplitCentralCoverCandidate i) : AddSubgroup (cocharacterLattice T) :=
  (Preadditive.rightComp (Gm (Spec (CommRingCat.of k))) c.t).range

theorem mem_coweightImage {c : SplitCentralCoverCandidate i} {μ : cocharacterLattice T} :
    μ ∈ c.coweightImage ↔ ∃ ν : cocharacterLattice c.S, ν ≫ c.t = μ :=
  Iff.rfl

/-- The identity of `G` is a candidate. -/
def refl (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i) :
    SplitCentralCoverCandidate i where
  C := G
  π := 𝟙 G
  isSemisimple := hG
  isCentralIsogeny := isCentralIsogeny_id G
  S := T
  j := i
  isSplitTorus := hT
  isMaximalTorus := hi
  t := 𝟙 T
  comm := (Category.comp_id i).trans (Category.id_comp i).symm

/-- A central isogeny `f : H ⟶ C` out of a perfect semisimple group, with a split maximal torus
`j' : S' ⟶ H` over the torus of a candidate `c`, gives the candidate `f ≫ π`. -/
def comp (c : SplitCentralCoverCandidate i) {H : GroupScheme (Spec (CommRingCat.of k))}
    (f : H ⟶ c.C) (hH : IsSemisimple H) (hf : IsCentralIsogeny f)
    (hperf : derivedSubgroup H = ⊤) {S' : CommGroupScheme (Spec (CommRingCat.of k))}
    (j' : S'.toGrp ⟶ H) (hS' : IsSplitTorus S'.toGrp) (hj' : IsMaximalTorus j') (t' : S' ⟶ c.S)
    (h : j' ≫ f = CommGroupScheme.groupHom t' ≫ c.j) : SplitCentralCoverCandidate i where
  C := H
  π := f ≫ c.π
  isSemisimple := hH
  isCentralIsogeny := IsCentralIsogeny.comp_of_derivedSubgroup_eq_top hperf hf c.isCentralIsogeny
  S := S'
  j := j'
  isSplitTorus := hS'
  isMaximalTorus := hj'
  t := t' ≫ c.t
  comm := by
    rw [← Category.assoc, h, Category.assoc, c.comm, ← Category.assoc]
    rfl

theorem coweightImage_comp_le (c : SplitCentralCoverCandidate i)
    {H : GroupScheme (Spec (CommRingCat.of k))} (f : H ⟶ c.C) (hH : IsSemisimple H)
    (hf : IsCentralIsogeny f) (hperf : derivedSubgroup H = ⊤)
    {S' : CommGroupScheme (Spec (CommRingCat.of k))} (j' : S'.toGrp ⟶ H)
    (hS' : IsSplitTorus S'.toGrp) (hj' : IsMaximalTorus j') (t' : S' ⟶ c.S)
    (h : j' ≫ f = CommGroupScheme.groupHom t' ≫ c.j) :
    (c.comp f hH hf hperf j' hS' hj' t' h).coweightImage ≤ c.coweightImage := by
  intro μ hμ
  obtain ⟨ν, rfl⟩ : ∃ ν : cocharacterLattice S', ν ≫ (t' ≫ c.t) = μ := hμ
  exact mem_coweightImage.mpr ⟨ν ≫ t', Category.assoc _ _ _⟩

/-- Given root data, the coroots of `i` lie in the coweight image of every candidate: they are
the images of the coroots of the candidate's torus under the coweight map of the root-datum
morphism defined by `π`. -/
theorem corootSpan_le_coweightImage (hRD : RootDatumExistenceStatement.{u})
    (hHom : CentralIsogenyRootDatumHomStatement.{u}) (hG : IsSemisimple G)
    (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i) {J : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : haveI := hG.isConnectedReductive.isAffineHom; IsRootDatumOf i P)
    (c : SplitCentralCoverCandidate i) :
    (P.corootSpan ℤ).toAddSubgroup ≤ c.coweightImage := by
  obtain ⟨J₀, -, P₀, hP₀, -⟩ := hRD k c.C c.isSemisimple.isConnectedReductive c.S c.isSplitTorus
    c.j c.isMaximalTorus
  obtain ⟨g, -, hg, -, -, -⟩ := hHom k c.C G c.isSemisimple.isConnectedReductive
    hG.isConnectedReductive c.S T c.isSplitTorus hT c.j i c.isMaximalTorus hi c.π c.t
    c.isCentralIsogeny c.comm J₀ J P₀ P hP₀ hP
  intro x hx
  refine (Submodule.span_le.mpr ?_ : P.corootSpan ℤ ≤ c.coweightImage.toIntSubmodule) hx
  rintro _ ⟨r, rfl⟩
  show P.coroot r ∈ c.coweightImage
  refine mem_coweightImage.mpr ⟨P₀.coroot (g.indexEquiv r), ?_⟩
  rw [← hg, RootPairing.Hom.coroot_coweightMap_apply, Equiv.symm_apply_apply]

/-- The coroots of a split maximal torus of a semisimple group span a subgroup of finite index
in its cocharacter lattice. -/
theorem corootSpan_index_ne_zero (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : haveI := hG.isConnectedReductive.isAffineHom; IsRootDatumOf i P) :
    (P.corootSpan ℤ).toAddSubgroup.index ≠ 0 := by
  have := hG.isConnectedReductive.isAffineHom
  have : Module.Finite ℤ (characterLattice T) := hT.finite_characterLattice
  have hfin : Finite (cocharacterLattice T ⧸ P.corootSpan ℤ) :=
    P.finite_quotient_rootSpan_iff_corootSpan.mp (hG.finite_quotient_rootSpan hT hi.2.1 hP)
  have : Finite (cocharacterLattice T ⧸ (P.corootSpan ℤ).toAddSubgroup) := hfin
  exact AddSubgroup.index_ne_zero_of_finite

/-- **A candidate with minimal coweight image is simply connected.** If the index of the coroot
span in the coweight image of `c` is minimal among all candidates, then every central isogeny
`f : H ⟶ C` from a semisimple group is an isomorphism: the composite `f ≫ π` is a candidate
(central since `H` is perfect) whose coweight image lies in, hence equals, that of `c`, so the
coweight map of the root-datum morphism of `f` is bijective, and then so is its weight map. -/
theorem isSimplyConnected_of_minimal (hRD : RootDatumExistenceStatement.{u})
    (hHom : CentralIsogenyRootDatumHomStatement.{u}) (hPerf : SemisimplePerfectStatement.{u})
    (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i) {J : Type u}
    [Finite J] {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : haveI := hG.isConnectedReductive.isAffineHom; IsRootDatumOf i P)
    (c : SplitCentralCoverCandidate i)
    (hmin : ∀ c' : SplitCentralCoverCandidate i,
      (P.corootSpan ℤ).toAddSubgroup.relIndex c.coweightImage ≤
        (P.corootSpan ℤ).toAddSubgroup.relIndex c'.coweightImage) :
    IsSimplyConnected c.C := by
  refine ⟨c.isSemisimple, fun H f hH hf => ?_⟩
  obtain ⟨S', j', t', hS', hj', h⟩ := centralIsogenySplitMaximalTorusLift k H c.C
    hH.isConnectedReductive c.isSemisimple.isConnectedReductive f hf c.S c.j c.isSplitTorus
    c.isMaximalTorus
  set c' := c.comp f hH hf (hPerf k H hH) j' hS' hj' t' h with hc'
  set N := (P.corootSpan ℤ).toAddSubgroup
  have hle : c'.coweightImage ≤ c.coweightImage := c.coweightImage_comp_le f hH hf _ j' hS' hj' t' h
  have hN : N ≤ c.coweightImage := corootSpan_le_coweightImage hRD hHom hG hT hi hP c
  have hN' : N ≤ c'.coweightImage := corootSpan_le_coweightImage hRD hHom hG hT hi hP c'
  -- The coweight images agree, by minimality of the index.
  have hge : c.coweightImage ≤ c'.coweightImage := by
    have hmul := AddSubgroup.relIndex_mul_relIndex N c'.coweightImage c.coweightImage hN' hle
    have hne : N.relIndex c.coweightImage ≠ 0 := fun h0 =>
      corootSpan_index_ne_zero hG hT hi hP
        (Nat.eq_zero_of_zero_dvd (h0 ▸ AddSubgroup.relIndex_dvd_index_of_le hN))
    have hmin' := hmin c'
    have hpos : 0 < N.relIndex c'.coweightImage := by omega
    have hone : c'.coweightImage.relIndex c.coweightImage ≤ 1 := by
      refine Nat.le_of_mul_le_mul_left ?_ hpos
      rw [mul_one, hmul]
      exact hmin'
    have hne' : c'.coweightImage.relIndex c.coweightImage ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hmul
      exact hne hmul.symm
    exact AddSubgroup.relIndex_eq_one.mp (by omega)
  -- Root data of the two tori and the root-datum morphisms of `f` and `π`.
  obtain ⟨J₁, -, P₁, hP₁, -⟩ := hRD k H hH.isConnectedReductive S' hS' j' hj'
  obtain ⟨J₀, -, P₀, hP₀, -⟩ := hRD k c.C c.isSemisimple.isConnectedReductive c.S c.isSplitTorus
    c.j c.isMaximalTorus
  obtain ⟨g, -, hgc, hgw, hgcinj, hiso⟩ := hHom k H c.C hH.isConnectedReductive
    c.isSemisimple.isConnectedReductive S' c.S hS' c.isSplitTorus j' c.j hj' c.isMaximalTorus f t'
    hf h J₁ J₀ P₁ P₀ hP₁ hP₀
  obtain ⟨e, -, hec, -, hecinj, -⟩ := hHom k c.C G c.isSemisimple.isConnectedReductive
    hG.isConnectedReductive c.S T c.isSplitTorus hT c.j i c.isMaximalTorus hi c.π c.t
    c.isCentralIsogeny c.comm J₀ J P₀ P hP₀ hP
  have hsurj : Function.Surjective g.coweightMap := by
    intro μ
    obtain ⟨ν, hν⟩ : ∃ ν : cocharacterLattice S', ν ≫ (t' ≫ c.t) = μ ≫ c.t :=
      hge (mem_coweightImage.mpr ⟨μ, rfl⟩)
    refine ⟨ν, hecinj ?_⟩
    rw [hec, hec, hgc]
    exact (Category.assoc _ _ _).trans hν
  exact hiso.mpr ⟨hgw, SplitCorootCriterion.surjective_weightMap g ⟨hgcinj, hsurj⟩⟩

end SplitCentralCoverCandidate

/-- **Simply connected central covers of split semisimple groups, conditionally** (route through
a minimal coweight lattice). The existence of root data for split maximal tori, the root-datum
morphism of a central isogeny, and perfectness of semisimple groups imply
`SplitSimplyConnectedCoverExistenceStatement`: a candidate whose coweight image has minimal index
over the coroot span is simply connected. -/
theorem splitSimplyConnectedCoverExistence_of_minimalLattice
    (hRD : RootDatumExistenceStatement.{u}) (hHom : CentralIsogenyRootDatumHomStatement.{u})
    (hPerf : SemisimplePerfectStatement.{u}) :
    SplitSimplyConnectedCoverExistenceStatement.{u} := by
  intro k _ G T hG hT i hi
  obtain ⟨J, _, P, hP, -⟩ := hRD k G hG.isConnectedReductive T hT i hi
  classical
  let n : SplitCentralCoverCandidate i → ℕ := fun c =>
    (P.corootSpan ℤ).toAddSubgroup.relIndex c.coweightImage
  have hex : ∃ m, ∃ c, n c = m := ⟨_, SplitCentralCoverCandidate.refl hG hT hi, rfl⟩
  obtain ⟨c, hc⟩ := Nat.find_spec hex
  refine ⟨c.C, c.π, ?_, c.isCentralIsogeny⟩
  refine c.isSimplyConnected_of_minimal hRD hHom hPerf hG hT hi hP fun c' => ?_
  change n c ≤ n c'
  rw [hc]
  exact Nat.find_min' hex ⟨c', rfl⟩

end Langlands.GroupScheme

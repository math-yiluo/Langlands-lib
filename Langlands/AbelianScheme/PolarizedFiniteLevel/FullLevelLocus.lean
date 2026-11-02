import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelCriterion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Topology.Clopen

/-! # An open and closed locus for an ordered full-level tuple -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {S : Scheme.{u}} {A : AbelianScheme S} {g n : ℕ}

/-- At a point of the base, the coefficient sections enumerate the whole
underlying torsion fibre without collisions. -/
def fullLevelLocusSet (v : SectionTuple A g n) : Set S :=
  {x | (∀ a b : Fin (2 * g) → ZMod n,
      (torsionSection v a).left x = (torsionSection v b).left x → a = b) ∧
    ∀ y : (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X.left,
      (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X.hom y = x →
        ∃ a : Fin (2 * g) → ZMod n, (torsionSection v a).left x = y}

private theorem torsionSection_comp_apply (v : SectionTuple A g n)
    (a : Fin (2 * g) → ZMod n) (x : S) :
    (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X.hom
        ((torsionSection v a).left x) = x := by
  rw [← Scheme.Hom.comp_apply, (torsionSection v a).w]
  rfl

private theorem torsionSection_isClosedImmersion (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (a : Fin (2 * g) → ZMod n) :
    IsClosedImmersion (torsionSection v a).left := by
  obtain ⟨hfin, _⟩ := torsionFiniteEtale S A n hn hunit
  let X := (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X
  have : IsFinite X.hom := hfin
  have : IsClosedImmersion ((torsionSection v a).left ≫ X.hom) := by
    rw [(torsionSection v a).w]
    change IsClosedImmersion (𝟙 S)
    infer_instance
  exact IsClosedImmersion.of_comp (f := (torsionSection v a).left) (g := X.hom)

private theorem torsionSection_range_isClopen (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (a : Fin (2 * g) → ZMod n) :
    IsClopen (Set.range (torsionSection v a).left) := by
  have := torsionSection_isOpenImmersion v hn hunit a
  have := torsionSection_isClosedImmersion v hn hunit a
  exact ⟨(torsionSection v a).left.isClosedEmbedding.isClosed_range,
    (torsionSection v a).left.isOpenEmbedding.isOpen_range⟩

/-- The underlying enumeration condition is an open and closed condition on the base. -/
theorem fullLevelLocusSet_isClopen (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    IsClopen (fullLevelLocusSet v) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let X := (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X
  obtain ⟨hfin, het⟩ := torsionFiniteEtale S A n hn hunit
  have : IsFinite X.hom := hfin
  have : Etale X.hom := het
  let covered : Set X.left := ⋃ a : Fin (2 * g) → ZMod n,
    Set.range (torsionSection v a).left
  have hc : IsClopen covered :=
    isClopen_iUnion_of_finite (torsionSection_range_isClopen v hn hunit)
  have hsurj : IsClopen ((X.hom '' coveredᶜ)ᶜ) :=
    (show IsClopen (X.hom '' coveredᶜ) from
      ⟨X.hom.isClosedMap _ hc.compl.isClosed, X.hom.isOpenMap _ hc.compl.isOpen⟩).compl
  let collision (a b : Fin (2 * g) → ZMod n) : Set S :=
    (torsionSection v a).left ⁻¹' Set.range (torsionSection v b).left
  have hcollision (a b : Fin (2 * g) → ZMod n) : IsClopen (collision a b) :=
    (torsionSection_range_isClopen v hn hunit b).preimage
      (torsionSection v a).left.continuous
  let distinct : Set S := ⋂ a : Fin (2 * g) → ZMod n,
    ⋂ b : Fin (2 * g) → ZMod n, ⋂ (_ : a ≠ b), (collision a b)ᶜ
  have hdistinct : IsClopen distinct :=
    isClopen_iInter_of_finite fun a => isClopen_iInter_of_finite fun b =>
      isClopen_iInter_of_finite fun _ => (hcollision a b).compl
  convert hdistinct.inter hsurj using 1
  ext x
  simp only [fullLevelLocusSet, Set.mem_ofPred_eq, distinct, Set.mem_inter_iff,
    Set.mem_iInter, Set.mem_compl_iff, Set.mem_image, covered, Set.mem_iUnion,
    Set.mem_range, collision, Set.mem_preimage]
  constructor
  · rintro ⟨hinj, hcov⟩
    constructor
    · intro a b hab ⟨y, hy⟩
      have hyx : y = x := by
        have := congrArg X.hom hy
        simpa only [X, torsionSection_comp_apply] using this
      exact hab (hinj a b (by simpa only [hyx] using hy.symm))
    · rintro ⟨y, hy, hyx⟩
      obtain ⟨a, ha⟩ := hcov y hyx
      exact hy ⟨a, x, ha⟩
  · rintro ⟨hinj, hcov⟩
    constructor
    · intro a b hab
      by_contra hne
      exact hinj a b hne ⟨x, hab.symm⟩
    · intro y hyx
      have hy : ∃ a : Fin (2 * g) → ZMod n, ∃ z : S,
          (torsionSection v a).left z = y := by
        by_contra h
        exact hcov ⟨y, h, hyx⟩
      obtain ⟨a, z, hz⟩ := hy
      have hzx : z = x := by
        have := congrArg X.hom hz
        simpa only [X, torsionSection_comp_apply, hyx] using this
      exact ⟨a, by simpa only [hzx] using hz⟩

/-- The actual open subscheme where coefficient sections enumerate the torsion fibre. -/
def fullLevelLocus (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) : S.Opens :=
  ⟨fullLevelLocusSet v, (fullLevelLocusSet_isClopen v hn hunit).isOpen⟩

/-- A field-valued point in the locus has bijective actual torsion enumeration. -/
theorem torsionSection_fibre_bijective_of_mem_fullLevelLocusSet
    (v : SectionTuple A g n) (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (hs : s default ∈ fullLevelLocusSet v) :
    Function.Bijective (fun a : Fin (2 * g) → ZMod n =>
      (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ torsionSection v a) := by
  let X := (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X
  let w : Spec (CommRingCat.of K) := default
  constructor
  · intro a b hab
    have hmaps : s ≫ (torsionSection v a).left =
        s ≫ (torsionSection v b).left := congrArg Over.Hom.left hab
    exact hs.1 a b (congrArg (fun f : Spec (CommRingCat.of K) ⟶ X.left => f w) hmaps)
  · intro x
    have hx : X.hom (x.left w) = s w := by
      rw [← Scheme.Hom.comp_apply, x.w]
      rfl
    obtain ⟨a, ha⟩ := hs.2 (x.left w) hx
    have : IsOpenImmersion (torsionSection v a).left :=
      torsionSection_isOpenImmersion v hn hunit a
    have hxrange : Set.range x.left ⊆ Set.range (torsionSection v a).left := by
      rintro _ ⟨w', rfl⟩
      refine ⟨s w, ?_⟩
      have hw : w' = w := Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _
      simpa only [hw] using ha
    let l := IsOpenImmersion.lift (torsionSection v a).left x.left hxrange
    have hl : l ≫ (torsionSection v a).left = x.left :=
      IsOpenImmersion.lift_fac _ _ _
    have hls : l = s := by
      calc
        l = (l ≫ (torsionSection v a).left) ≫ X.hom := by
          rw [Category.assoc, (torsionSection v a).w]
          exact (Category.comp_id l).symm
        _ = x.left ≫ X.hom := by rw [hl]
        _ = s := x.w
    refine ⟨a, ?_⟩
    apply Over.OverMorphism.ext
    change s ≫ (torsionSection v a).left = x.left
    simpa only [hls] using hl

/-- On the locus, the original ordered fibre entries are a basis. -/
theorem exists_fibreBasis_of_mem_fullLevelLocusSet
    (v : SectionTuple A g n) (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (hs : s default ∈ fullLevelLocusSet v) :
    ∃ b : Module.Basis (Fin (2 * g)) (ZMod n) (Level A.toGrp (Over.mk s) n),
      ∀ i, b i = fibreTuple v s i := by
  let l := Fintype.linearCombination (ZMod n) (fibreTuple v s)
  have heq (a : Fin (2 * g) → ZMod n) :
      l a = kernelLevelEquiv A.toGrp (Over.mk s) n
        (Additive.ofMul ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫
          torsionSection v a)) := by
    rw [torsionSection_restrict]
    simp only [l, Fintype.linearCombination_apply, enumerateTuple, map_sum,
      ZMod.map_smul, fibreTuple]
  have hbij : Function.Bijective l := by
    simpa only [Function.comp_def, ← heq] using
      (kernelLevelEquiv A.toGrp (Over.mk s) n).bijective.comp
        (Additive.ofMul.bijective.comp
          (torsionSection_fibre_bijective_of_mem_fullLevelLocusSet v hn hunit K s hs))
  let e := LinearEquiv.ofBijective l hbij
  refine ⟨Module.Basis.ofEquivFun e.symm, ?_⟩
  intro i
  rw [Module.Basis.coe_ofEquivFun]
  change l (Pi.single i 1) = fibreTuple v s i
  simp [l]

/-- Fullness is exactly the assertion that every base point belongs to the locus. -/
theorem isFull_iff_fullLevelLocusSet_eq_univ (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    IsFull v ↔ fullLevelLocusSet v = Set.univ := by
  constructor
  · intro h
    let v' : FullLevel A g n := ⟨v, h⟩
    apply Set.eq_univ_of_forall
    intro x
    constructor
    · intro a b hab
      by_contra hne
      exact Set.disjoint_left.mp (v'.torsionSection_pairwise_disjoint hn hunit hne)
        ⟨x, rfl⟩ ⟨x, hab.symm⟩
    · intro y hy
      obtain ⟨a, z, hz⟩ := v'.torsionSection_cover y
      have hzx : z = x := by
        have := congrArg
          (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X.hom hz
        simpa only [torsionSection_comp_apply, hy] using this
      exact ⟨a, by simpa only [hzx] using hz⟩
  · intro h K _ _ s
    exact exists_fibreBasis_of_mem_fullLevelLocusSet v hn hunit K s (by
      rw [h]
      trivial)

/-- A base change whose image lies in the locus carries the prescribed full level. -/
theorem isFull_pullbackTuple_of_range_subset_fullLevelLocusSet
    {S' : Scheme.{u}} (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (b : S' ⟶ S)
    (hb : Set.range b ⊆ fullLevelLocusSet v) :
    IsFull (pullbackTuple b v) := by
  intro K _ _ s
  obtain ⟨bs, hbs⟩ := exists_fibreBasis_of_mem_fullLevelLocusSet v hn hunit K
    (s ≫ b) (hb ⟨s default, rfl⟩)
  refine ⟨bs.map (levelBaseChangeLinear A.toGrp b (Over.mk s) n).symm, ?_⟩
  intro i
  apply (levelBaseChangeLinear A.toGrp b (Over.mk s) n).injective
  change (levelBaseChangeLinear A.toGrp b (Over.mk s) n)
    ((levelBaseChangeLinear A.toGrp b (Over.mk s) n).symm (bs i)) = _
  rw [LinearEquiv.apply_symm_apply, hbs i]
  exact (fibreTuple_pullback b v s i).symm

/-- Restrict the supplied tuple to its actual full-level open subscheme. -/
def fullLevelOnLocus (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    FullLevel ((baseChange (fullLevelLocus v hn hunit).ι).obj A) g n :=
  ⟨pullbackTuple (fullLevelLocus v hn hunit).ι v,
    isFull_pullbackTuple_of_range_subset_fullLevelLocusSet v hn hunit _ (by
      rintro _ ⟨x, rfl⟩
      exact x.2)⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel

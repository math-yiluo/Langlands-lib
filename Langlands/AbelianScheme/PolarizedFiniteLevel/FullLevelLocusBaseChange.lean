import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelLocus
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The universal property of the actual full-level locus -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {S S' : Scheme.{u}} {A : AbelianScheme S} {g n : ℕ}

/-- A basis on the pulled-back geometric fibre is a basis of the original
tuple at the composite point, through the actual torsion comparison. -/
theorem exists_fibreBasis_of_isFull_pullbackTuple
    (v : SectionTuple A g n) (b : S' ⟶ S) (h : IsFull (pullbackTuple b v))
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S') :
    ∃ bs : Module.Basis (Fin (2 * g)) (ZMod n) (Level A.toGrp (Over.mk (s ≫ b)) n),
      ∀ i, bs i = fibreTuple v (s ≫ b) i := by
  obtain ⟨bs, hbs⟩ := h K s
  refine ⟨bs.map (levelBaseChangeLinear A.toGrp b (Over.mk s) n), ?_⟩
  intro i
  change levelBaseChangeLinear A.toGrp b (Over.mk s) n (bs i) = _
  rw [hbs i]
  exact fibreTuple_pullback b v s i

/-- A basis with the prescribed entries gives unique actual kernel coordinates
at that point, without requiring global fullness. -/
theorem existsUnique_torsionSection_of_fibreBasis
    (v : SectionTuple A g n) (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S)
    (hs : ∃ bs : Module.Basis (Fin (2 * g)) (ZMod n) (Level A.toGrp (Over.mk s) n),
      ∀ i, bs i = fibreTuple v s i)
    (x : Over.mk s ⟶ (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X) :
    ∃! a : Fin (2 * g) → ZMod n,
      (Over.homMk s (by simp)) ≫ torsionSection v a = x := by
  obtain ⟨bs, hbs⟩ := hs
  let e := bs.equivFun.symm
  have heq (a : Fin (2 * g) → ZMod n) :
      kernelLevelEquiv A.toGrp (Over.mk s) n
        (Additive.ofMul ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫
          torsionSection v a)) = e a := by
    rw [torsionSection_restrict]
    simp only [enumerateTuple, Fintype.linearCombination_apply, map_sum,
      ZMod.map_smul]
    simp only [e, Module.Basis.equivFun_symm_apply, hbs, fibreTuple]
  let y := kernelLevelEquiv A.toGrp (Over.mk s) n (Additive.ofMul x)
  refine ⟨e.symm y, ?_, ?_⟩
  · apply Additive.ofMul.injective
    apply (kernelLevelEquiv A.toGrp (Over.mk s) n).injective
    rw [heq, LinearEquiv.apply_symm_apply]
  · intro a ha
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, ← heq, ha]

private theorem section_comp_of_range_subset {Y Z : Scheme.{u}} (p : Y ⟶ S)
    (f : S ⟶ Y) [IsOpenImmersion f] (hf : f ≫ p = 𝟙 S) (t : Z ⟶ Y)
    (ht : Set.range t ⊆ Set.range f) :
    (t ≫ p) ≫ f = t := by
  let l := IsOpenImmersion.lift f t ht
  calc
    (t ≫ p) ≫ f = ((l ≫ f) ≫ p) ≫ f := by
      rw [IsOpenImmersion.lift_fac]
    _ = l ≫ f := by rw [Category.assoc l f p, hf, Category.comp_id]
    _ = t := IsOpenImmersion.lift_fac f t ht

/-- A full pulled-back tuple forces every point of its image into the original locus. -/
theorem range_subset_fullLevelLocusSet_of_isFull_pullbackTuple
    (v : SectionTuple A g n) (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (b : S' ⟶ S) (h : IsFull (pullbackTuple b v)) :
    Set.range b ⊆ fullLevelLocusSet v := by
  rintro _ ⟨x, rfl⟩
  let X := (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X
  constructor
  · intro a c hac
    let K := AlgebraicClosure (S'.residueField x)
    let t : Spec (CommRingCat.of K) ⟶ S' :=
      Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) K)) ≫
        S'.fromSpecResidueField x
    let s := t ≫ b
    have ht (w : Spec (CommRingCat.of K)) : t w = x :=
      Scheme.fromSpecResidueField_apply x _
    have : IsOpenImmersion (torsionSection v c).left :=
      torsionSection_isOpenImmersion v hn hunit c
    have hrange : Set.range (s ≫ (torsionSection v a).left) ⊆
        Set.range (torsionSection v c).left := by
      rintro _ ⟨w, rfl⟩
      refine ⟨b x, ?_⟩
      change (torsionSection v c).left (b x) =
        (torsionSection v a).left (b (t w))
      rw [ht w]
      exact hac.symm
    have hcomp : s ≫ (torsionSection v c).left =
        s ≫ (torsionSection v a).left := by
      have heq := section_comp_of_range_subset X.hom (torsionSection v c).left
        (torsionSection v c).w (s ≫ (torsionSection v a).left) hrange
      have hstruct : (s ≫ (torsionSection v a).left) ≫ X.hom = s := by
        change (s ≫ (torsionSection v a).left) ≫
          (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X.hom = s
        rw [Category.assoc, (torsionSection v a).w]
        exact Category.comp_id _
      rw [hstruct] at heq
      exact heq
    have hcoeff : (Over.homMk s (by simp)) ≫ torsionSection v c =
        (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ torsionSection v a := by
      apply Over.OverMorphism.ext
      exact hcomp
    obtain ⟨q, hq, huniq⟩ := existsUnique_torsionSection_of_fibreBasis v K s
      (exists_fibreBasis_of_isFull_pullbackTuple v b h K t)
      ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ torsionSection v a)
    exact ((huniq c hcoeff).trans (huniq a rfl).symm).symm
  · intro y hy
    obtain ⟨z, hzy, hzx⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := X.hom) (g := b) y x hy
    let Y := pullback X.hom b
    let K := AlgebraicClosure (Y.residueField z)
    let t : Spec (CommRingCat.of K) ⟶ Y :=
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField z) K)) ≫
        Y.fromSpecResidueField z
    let s' := t ≫ pullback.snd X.hom b
    let s := s' ≫ b
    let q := t ≫ pullback.fst X.hom b
    have hq : q ≫ X.hom = s := by
      simp only [q, s, s', Category.assoc, pullback.condition]
    obtain ⟨a, ha, _⟩ := existsUnique_torsionSection_of_fibreBasis v K s
      (exists_fibreBasis_of_isFull_pullbackTuple v b h K s') (Over.homMk q hq)
    let w : Spec (CommRingCat.of K) := default
    have htw : t w = z := Scheme.fromSpecResidueField_apply z _
    have hsw : s w = b x := by
      change b ((pullback.snd X.hom b) (t w)) = b x
      rw [htw]
      exact congrArg b hzx
    have hqw : q w = y := by
      change (pullback.fst X.hom b) (t w) = y
      rw [htw]
      exact hzy
    refine ⟨a, ?_⟩
    have hmaps : s ≫ (torsionSection v a).left = q := congrArg Over.Hom.left ha
    have heval := congrArg (fun f : Spec (CommRingCat.of K) ⟶ X.left => f w) hmaps
    change (torsionSection v a).left (s w) = q w at heval
    rw [hsw, hqw] at heval
    exact heval

/-- The full-level locus characterizes exactly all base changes carrying the tuple
to a full level. -/
theorem isFull_pullbackTuple_iff_range_subset_fullLevelLocusSet
    (v : SectionTuple A g n) (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (b : S' ⟶ S) :
    IsFull (pullbackTuple b v) ↔ Set.range b ⊆ fullLevelLocusSet v :=
  ⟨range_subset_fullLevelLocusSet_of_isFull_pullbackTuple v hn hunit b,
    isFull_pullbackTuple_of_range_subset_fullLevelLocusSet v hn hunit b⟩

/-- Factor a base change carrying the prescribed full level through its actual locus. -/
def fullLevelLocusLift (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (b : S' ⟶ S) (h : IsFull (pullbackTuple b v)) :
    S' ⟶ (fullLevelLocus v hn hunit).toScheme :=
  IsOpenImmersion.lift (fullLevelLocus v hn hunit).ι b (by
    rw [Scheme.Opens.range_ι]
    exact range_subset_fullLevelLocusSet_of_isFull_pullbackTuple v hn hunit b h)

@[reassoc (attr := simp)]
theorem fullLevelLocusLift_fac (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (b : S' ⟶ S) (h : IsFull (pullbackTuple b v)) :
    fullLevelLocusLift v hn hunit b h ≫ (fullLevelLocus v hn hunit).ι = b :=
  IsOpenImmersion.lift_fac _ _ _

/-- The factorization through the full-level locus is unique. -/
theorem fullLevelLocusLift_unique (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (b : S' ⟶ S) (h : IsFull (pullbackTuple b v))
    (l : S' ⟶ (fullLevelLocus v hn hunit).toScheme)
    (hl : l ≫ (fullLevelLocus v hn hunit).ι = b) :
    l = fullLevelLocusLift v hn hunit b h := by
  apply (cancel_mono (fullLevelLocus v hn hunit).ι).mp
  rw [hl, fullLevelLocusLift_fac]

/-- Morphisms into the actual locus are precisely base maps on which the
prescribed pulled-back tuple is full. -/
def fullLevelLocusHomEquiv (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (T : Scheme.{u}) :
    (T ⟶ (fullLevelLocus v hn hunit).toScheme) ≃
      {b : T ⟶ S // IsFull (pullbackTuple b v)} where
  toFun l := ⟨l ≫ (fullLevelLocus v hn hunit).ι,
    isFull_pullbackTuple_of_range_subset_fullLevelLocusSet v hn hunit _ (by
      rintro _ ⟨x, rfl⟩
      exact (l x).2)⟩
  invFun b := fullLevelLocusLift v hn hunit b.val b.property
  left_inv l := (fullLevelLocusLift_unique v hn hunit _ _ l rfl).symm
  right_inv b := by
    apply Subtype.ext
    exact fullLevelLocusLift_fac v hn hunit b.val b.property

@[simp]
theorem fullLevelLocusHomEquiv_apply_val (v : SectionTuple A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (T : Scheme.{u})
    (l : T ⟶ (fullLevelLocus v hn hunit).toScheme) :
    (fullLevelLocusHomEquiv v hn hunit T l).val = l ≫ (fullLevelLocus v hn hunit).ι :=
  rfl

end Langlands.AbelianScheme.PolarizedFiniteLevel

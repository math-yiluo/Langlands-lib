/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedAffineCoefficientModel
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.SixFunctors.ProAffineEtaleResidueEqualizer
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! Closed equality-pattern restrictions of a finite family.
(blueprint: lem-sfb-completed-affine-pattern-cover)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem affine_closed_component_restriction
    (T : Scheme.{u}) [IsAffine T] (E : Set T) (hE : IsClosed E)
    (hcomp : ∀ x ∈ E, connectedComponent x ⊆ E) :
    ∃ (V : Scheme.{u}) (f : V ⟶ T), WeaklyEtale f ∧ QuasiCompact f ∧
      Set.range f = E := by
  classical
  let A := Γ(T, ⊤)
  let F : Set (PrimeSpectrum A) := T.isoSpec.inv ⁻¹' E
  have hF : IsClosed F := hE.preimage T.isoSpec.inv.continuous
  have hc : ∀ x ∈ F, connectedComponent x ⊆ F := by
    intro x hx y hy
    exact hcomp (T.isoSpec.inv x) hx
      (T.isoSpec.inv.continuous.image_connectedComponent_subset x ⟨y, hy, rfl⟩)
  let Z : Set (ConnectedComponents (PrimeSpectrum A)) := ConnectedComponents.mk '' F
  have hz : ConnectedComponents.mk ⁻¹' Z = F := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, he⟩
      exact hc y hy (ConnectedComponents.coe_eq_coe'.mp he.symm)
    · exact Set.subset_preimage_image _ _
  have hZ : IsClosed Z := by
    apply ConnectedComponents.isQuotientMap_coe.isClosed_preimage.mp
    rwa [hz]
  let B := WContractification.Restriction Z
  let v : A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  have hv : WeaklyEtale (Spec.map v) := by
    apply (WeaklyEtale.Spec_iff v).mpr
    change (algebraMap A B).WeaklyEtale
    rw [RingHom.weaklyEtale_algebraMap_iff]
    infer_instance
  let f := Spec.map v ≫ T.isoSpec.inv
  refine ⟨Spec (.of B), f, ?_, ?_, ?_⟩
  · have : WeaklyEtale (Spec.map v) := hv
    infer_instance
  · infer_instance
  · have hr : Set.range (PrimeSpectrum.comap (algebraMap A B)) = F :=
      (WContractification.Restriction.range_algebraMap_specComap hZ).trans hz
    change Set.range (T.isoSpec.inv ∘ PrimeSpectrum.comap (algebraMap A B)) = E
    rw [Set.range_comp, hr]
    exact Set.image_preimage_eq _ T.isoSpec.inv.homeomorph.surjective

private theorem finite_closed_component_cover
    (X : Scheme.{u}) (W : X.ProEt) {κ : Type (u + 1)} [Finite κ]
    (E : κ → Set W.left) (hE : ∀ k, IsClosed (E k))
    (hc : ∀ k x, x ∈ E k → connectedComponent x ⊆ E k)
    (hcover : ∀ x, ∃ k, x ∈ E k) :
    ∃ S : Sieve W, S ∈ Scheme.ProEt.topology X W ∧
      ∀ (V : X.ProEt) (f : V ⟶ W), S f → ∃ k, Set.range f.left ⊆ E k := by
  classical
  let S : Sieve W :=
    { arrows := fun V f ↦ ∃ k, Set.range f.left ⊆ E k
      downward_closed := by
        rintro V Y f ⟨k, hk⟩ g
        exact ⟨k, fun _ ⟨y, hy⟩ ↦ hk ⟨g.left y, hy⟩⟩ }
  refine ⟨S, ?_, fun _ _ h ↦ h⟩
  let C := W.left.affineCover
  let V (i : C.I₀) : X.ProEt := Scheme.ProEt.mk (C.f i ≫ W.hom)
  let v (i : C.I₀) : V i ⟶ W := MorphismProperty.Over.homMk (C.f i) rfl
  have hv : Sieve.ofArrows V v ∈ Scheme.ProEt.topology X W :=
    Scheme.ProEt.mem_topology_of_openImmersion (Sieve.ofArrows V v) C.f
      (fun x ↦ ⟨C.idx x, C.covers x⟩) (fun i ↦ Sieve.ofArrows_mk _ _ i)
  apply (Scheme.ProEt.topology X).transitive hv
  intro A a ha
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp ha
  rw [Sieve.pullback_comp]
  apply (Scheme.ProEt.topology X).pullback_stable b
  let F (k : κ) : Set (C.X i) := C.f i ⁻¹' E k
  have hF (k : κ) : IsClosed (F k) := (hE k).preimage (C.f i).continuous
  have hFc (k : κ) : ∀ x ∈ F k, connectedComponent x ⊆ F k := by
    intro x hx y hy
    exact hc k (C.f i x) hx
      ((C.f i).continuous.image_connectedComponent_subset x ⟨y, hy, rfl⟩)
  choose Z f hf hq hr using fun k ↦
    affine_closed_component_restriction (C.X i) (F k) (hF k) (hFc k)
  let Y (k : κ) : X.ProEt := by
    have : WeaklyEtale (f k) := hf k
    exact Scheme.ProEt.mk (f k ≫ (V i).hom)
  let y (k : κ) : Y k ⟶ V i := MorphismProperty.Over.homMk (f k) rfl
  let D : (C.X i).Cover (Scheme.precoverage @WeaklyEtale) :=
    Scheme.Cover.mkOfCovers κ Z f (fun x ↦ by
      obtain ⟨k, hk⟩ := hcover (C.f i x)
      have : x ∈ Set.range (f k) := (hr k).symm ▸ hk
      obtain ⟨y, hy⟩ := this
      exact ⟨k, y, hy⟩) hf
  have : ∀ k, QuasiCompact (D.f k) := hq
  have : Finite D.I₀ := inferInstanceAs (Finite κ)
  have : QuasiCompactCover D.toPreZeroHypercover := inferInstance
  have hD : Presieve.ofArrows Y y ∈ Scheme.ProEt.precoverage X (V i) := by
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact ⟨by
      rw [← Scheme.presieve₀_mem_qcPrecoverage_iff] at this
      exact this, D.mem₀⟩
  apply (Scheme.ProEt.topology X).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck hD)
  rw [Sieve.generate_le_iff]
  rintro B g ⟨k⟩
  refine ⟨k, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (show f k x ∈ F k from (hr k).subset ⟨x, rfl⟩)

open Classical in
/-- Pointwise fiber-class cancellation extends to cancellation on a covering family.
The conclusion records equal arrows and zero coefficient sums, independently of free
modules, sheafification, or dual maps.
Source: `CompletedAffineFreeLocalDual.lean`, the closed-pattern part of the proof of
`completedAffineFree_localDual_detect`; Stacks 097C for the canonical restrictions.
(blueprint: lem-sfb-completed-affine-pattern-cover)

Proof: for each equivalence relation r on the finite index set, take the locus E(r)
where r-related residue-field arrows agree and every r-class coefficient sum vanishes.
The geometric equality loci are intersections of clopen stage equalizers. Each E(r)
is therefore closed and saturated under connected components: continuous functions
into the totally disconnected p-adic integers are constant on a component. At each
point its actual residue-field equality pattern supplies an r for which it lies in E(r).
Thus these finitely many loci cover W; no closure of an exact-pattern stratum is needed.
Cover W by affine opens and realize each pulled-back E(r) using the existing ring
WContractification.Restriction of its closed component subset. Its algebra map is
ind-Zariski, hence weakly etale, and its spectrum has exactly the required image.
These affine, hence quasi-compact, maps form a finite pro-etale cover of each affine
open. The sieve of all arrows whose image is contained in some E(r) is covering by
transitivity. Such an arrow equalizes every r-related pair as scheme maps, using the
open equalizer at each etale stage and the limit universal property. Naturality and
injectivity of M imply that every restricted r-class coefficient sum is zero. This
construction also works for the empty index set and for an empty test scheme. -/
theorem completedAffine_pattern_cover (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (M : CompletedAffineCoefficientModel l X)
    (U : X.ProEtᵒᵖ) (hU : proAffineEtale U.unop.hom) (W : X.ProEt)
    {ι : Type (u + 1)} [Fintype ι]
    (q : ι → (uliftYoneda.{u + 1}.obj U.unop).obj (op W))
    (a : ι → (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj (op W))
    (ha : ∀ (x : W.left) (i : ι),
      (∑ j : ι, if W.left.fromSpecResidueField x ≫ (q j).down.left =
          W.left.fromSpecResidueField x ≫ (q i).down.left
        then M.equiv W (a j) x else 0) = 0) :
    ∃ S : Sieve W, S ∈ Scheme.ProEt.topology X W ∧
      ∀ (V : X.ProEt) (f : V ⟶ W), S f →
        ∃ r : Setoid ι,
          (∀ i j : ι, r.r i j →
            (uliftYoneda.{u + 1}.obj U.unop).map f.op (q i) =
              (uliftYoneda.{u + 1}.obj U.unop).map f.op (q j)) ∧
          (∀ i : ι, (∑ j : ι, if r.r j i then
            (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.map f.op (a j)
              else 0) = 0) := by
  classical
  let R := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
  let b (r : Setoid ι) (i : ι) : R.obj.obj (op W) :=
    ∑ j : ι, if r.r j i then a j else 0
  let EqAt (i j : ι) : Set W.left := {x |
    W.left.fromSpecResidueField x ≫ (q i).down.left =
      W.left.fromSpecResidueField x ≫ (q j).down.left}
  have heq (i j : ι) :=
    proAffineEtale_residue_equalizer X U.unop W hU (q i).down (q j).down
  let E (r : Setoid ι) : Set W.left := {x |
    (∀ i j, r.r i j → x ∈ EqAt i j) ∧ ∀ i, M.equiv W (b r i) x = 0}
  have hclosed (r : Setoid ι) : IsClosed (E r) := by
    simp only [E, Set.ofPred_and, Set.ofPred_forall]
    apply IsClosed.inter
    · apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro j
      apply isClosed_iInter
      intro _
      exact (heq i j).1
    · apply isClosed_iInter
      intro i
      exact isClosed_eq (M.equiv W (b r i)).continuous continuous_const
  have hcomp (r : Setoid ι) (x : W.left) (hx : x ∈ E r) :
      connectedComponent x ⊆ E r := by
    intro y hy
    refine ⟨fun i j hij ↦ (heq i j).2.1 x (hx.1 i j hij) hy, fun i ↦ ?_⟩
    have hval := (M.equiv W (b r i)).continuous.image_eq_of_connectedComponent_eq y x
      (connectedComponent_eq hy).symm
    exact hval.trans (hx.2 i)
  have hcover (x : W.left) : ∃ r, x ∈ E r := by
    let r : Setoid ι := Setoid.ker (fun j ↦
      W.left.fromSpecResidueField x ≫ (q j).down.left)
    refine ⟨r, fun i j hij ↦ hij, fun i ↦ ?_⟩
    change M.equiv W (∑ j : ι, if r.r j i then a j else 0) x = 0
    rw [map_sum, ContinuousMap.sum_apply]
    convert ha x i using 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : r.r j i
    · have hh : W.left.fromSpecResidueField x ≫ (q j).down.left =
          W.left.fromSpecResidueField x ≫ (q i).down.left := h
      simp only [ite_eq_left h, ite_eq_left hh]
    · have hh : W.left.fromSpecResidueField x ≫ (q j).down.left ≠
          W.left.fromSpecResidueField x ≫ (q i).down.left := h
      simp only [ite_eq_right h, ite_eq_right hh, map_zero, ContinuousMap.zero_apply]
  have : Finite (Setoid ι) :=
    Finite.of_injective (fun r : Setoid ι ↦ r.r) (fun r s h ↦ by
      apply Setoid.ext
      intro i j
      exact iff_of_eq (congrFun (congrFun h i) j))
  obtain ⟨S, hS, hlocal⟩ :=
    finite_closed_component_cover X W E hclosed hcomp hcover
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨r, hr⟩ := hlocal V f hf
  refine ⟨r, ?_, ?_⟩
  · intro i j hij
    apply ULift.ext
    exact (heq i j).2.2 V f (fun _ ⟨x, hx⟩ ↦ hx ▸ (hr ⟨x, rfl⟩).1 i j hij)
  · intro i
    apply (M.equiv V).injective
    apply ContinuousMap.ext
    intro x
    have hz := (hr ⟨x, rfl⟩).2 i
    have hn := congrArg (fun t : C(V.left, ℤ_[l]) ↦ t x) (M.naturality f (b r i))
    change M.equiv V (R.obj.map f.op (b r i)) x = M.equiv W (b r i) (f.left x) at hn
    have hs : (∑ j : ι, if r.r j i then R.obj.map f.op (a j) else 0) =
        R.obj.map f.op (b r i) := by
      simp only [b, map_sum, apply_ite, map_zero]
    change M.equiv V (∑ j : ι, if r.r j i then R.obj.map f.op (a j) else 0) x =
      M.equiv V 0 x
    rw [hs, hn, hz, map_zero, ContinuousMap.zero_apply]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

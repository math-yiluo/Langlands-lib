import Langlands.LinearAlgebra.GMFamilyChamberFaces
import Langlands.LinearAlgebra.GMFamilyDescentVolume
import Langlands.LinearAlgebra.AffineVertexWallCancellation

/-! # Affine vertices and transverse Levi flats -/

noncomputable section

open scoped RealInnerProductSpace
open Classical Module Submodule
open Langlands.LinearAlgebra.AffineVertexWeights Langlands.LinearAlgebra.FiniteHyperplaneSegment

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The complement of the central space in a Levi flat. -/
abbrev noncentral (R : Finset E) (a : Submodule ℝ E) : Submodule ℝ E := a ⊓ (centralSpace R)ᗮ

/-- The Levi flats with nonzero descent coefficient. -/
def transverseLevis (R : Finset E) (a a₁ : Submodule ℝ E) : Finset (Submodule ℝ E) :=
  (leviSpaces R a₁).filter (fun L => dDescent a (centralSpace R) a₁ L ≠ 0)

/-- The nested Levi flats and the general-position hypothesis for their affine slice. -/
structure DescentPosition (R : Finset E) (a a₁ : Submodule ℝ E) (ξ : E) : Prop where
  roots : IsRootSet R
  coarse : IsLeviSpace R a
  fine : IsLeviSpace R a₁
  le_fine : a ≤ a₁
  offset : ξ ∈ a₁ ⊓ aᗮ
  regular : ∀ L ∈ leviSpaces R a₁, dDescent a (centralSpace R) a₁ L ≠ 0 →
    ∀ p, p ∈ noncentral R L → p - ξ ∈ noncentral R a → IsRegular R L p

variable {R : Finset E} {a a₁ : Submodule ℝ E} {ξ : E}

omit [FiniteDimensional ℝ E] in
theorem centralSpace_le_of_levi (ha : IsLeviSpace R a) : centralSpace R ≤ a := by
  obtain ⟨p, rfl⟩ := ha
  exact centralSpace_le_leviSpaceOf p

theorem transverseLevi_isLevi (D : DescentPosition R a a₁ ξ) (L : transverseLevis R a a₁) :
    IsLeviSpace R (L : Submodule ℝ E) := by
  obtain ⟨p, _, hp⟩ := (mem_leviSpaces_iff_exists_point D.roots D.fine).mp (Finset.mem_filter.mp L.prop).1
  exact ⟨p, hp⟩

theorem transverseLevi_le_fine (D : DescentPosition R a a₁ ξ) (L : transverseLevis R a a₁) :
    (L : Submodule ℝ E) ≤ a₁ := by
  obtain ⟨p, hp, he⟩ := (mem_leviSpaces_iff_exists_point D.roots D.fine).mp (Finset.mem_filter.mp L.prop).1
  exact he ▸ leviSpaceOf_le_of_mem D.fine hp

def transversePoint (D : DescentPosition R a a₁ ξ) (L : transverseLevis R a a₁) : E :=
  (existsUnique_descentPoint (centralSpace_le_of_levi D.coarse) D.le_fine
    (centralSpace_le_of_levi (transverseLevi_isLevi D L)) (transverseLevi_le_fine D L)
    (Finset.mem_filter.mp L.prop).2 D.offset).exists.choose

theorem transversePoint_spec (D : DescentPosition R a a₁ ξ) (L : transverseLevis R a a₁) :
    transversePoint D L ∈ noncentral R (L : Submodule ℝ E) ∧
      transversePoint D L - ξ ∈ noncentral R a :=
  (existsUnique_descentPoint (centralSpace_le_of_levi D.coarse) D.le_fine
    (centralSpace_le_of_levi (transverseLevi_isLevi D L)) (transverseLevi_le_fine D L)
    (Finset.mem_filter.mp L.prop).2 D.offset).exists.choose_spec

theorem transversePoint_eq (D : DescentPosition R a a₁ ξ) (L : transverseLevis R a a₁)
    {p : E} (hpL : p ∈ noncentral R (L : Submodule ℝ E)) (hpA : p - ξ ∈ noncentral R a) :
    transversePoint D L = p := by
  obtain ⟨q, _, huniq⟩ := existsUnique_descentPoint
    (centralSpace_le_of_levi D.coarse) D.le_fine (centralSpace_le_of_levi (transverseLevi_isLevi D L))
    (transverseLevi_le_fine D L) (Finset.mem_filter.mp L.prop).2 D.offset
  exact (huniq _ (transversePoint_spec D L)).trans (huniq p ⟨hpL, hpA⟩).symm

theorem transversePoint_regular (D : DescentPosition R a a₁ ξ) (L : transverseLevis R a a₁) :
    IsRegular R (L : Submodule ℝ E) (transversePoint D L) :=
  D.regular _ (Finset.mem_filter.mp L.prop).1 (Finset.mem_filter.mp L.prop).2 _
    (transversePoint_spec D L).1 (transversePoint_spec D L).2

theorem transversePoint_section (D : DescentPosition R a a₁ ξ) (L : transverseLevis R a a₁) :
    descentSection R a (centralSpace R) ξ L = posSet R (transversePoint D L) :=
  descentSection_eq_posSet (centralSpace_le_of_levi D.coarse) D.le_fine
    (centralSpace_le_of_levi (transverseLevi_isLevi D L)) (transverseLevi_le_fine D L)
    (Finset.mem_filter.mp L.prop).2 D.offset (transversePoint_spec D L).1 (transversePoint_spec D L).2

variable (R a a₁)

/-- The projected fine simple roots that appear as normals in the coarse slice. -/
def sliceNormal {P : Finset E} (b : simpleRoots a₁ P) : noncentral R a :=
  (noncentral R a).orthogonalProjectionOnto ((b : a₁) : E)

variable {R a a₁}

/-- The offset term in the inequality for a fine simple root. -/
def sliceOffset {P : Finset E} (ξ : E) (b : simpleRoots a₁ P) : ℝ := ⟪((b : a₁) : E), ξ⟫

theorem sliceNormal_inner {P : Finset E} (b : simpleRoots a₁ P) (p : noncentral R a) :
    ⟪sliceNormal R a a₁ b, p⟫ = ⟪((b : a₁) : E), (p : E)⟫ :=
  inner_orthogonalProjectionOnto_eq_of_mem_right p _

theorem coe_sliceNormal_eq_restrictedRoot {P : Finset E} (D : DescentPosition R a a₁ ξ)
    (hP : P ∈ parabolics R a₁) (b : simpleRoots a₁ P) :
    ((sliceNormal R a a₁ b : noncentral R a) : E) = (restrictedRoot a ((b : a₁) : E) : E) := by
  let y := a.starProjection ((b : a₁) : E)
  have hy : y ∈ a := a.starProjection_apply_mem _
  have hb : ((b : a₁) : E) ∈ (centralSpace R)ᗮ := by
    have hj := subset_span (R := ℝ) (Set.mem_range_self b :
      ((b : a₁) : E) ∈ Set.range (fun i : simpleRoots a₁ P => ((i : a₁) : E)))
    exact ((simpleRoots_basis D.roots D.fine hP).2 ▸ hj).2
  have hyz : y ∈ (centralSpace R)ᗮ := by
    intro z hz
    have he := a.starProjection_inner_eq_zero ((b : a₁) : E) z (centralSpace_le_of_levi D.coarse hz)
    rw [inner_sub_left, sub_eq_zero, real_inner_comm, hb z hz] at he
    exact inner_eq_zero_symm.mp he.symm
  have hA : y ∈ noncentral R a := ⟨hy, hyz⟩
  exact eq_starProjection_of_mem_orthogonal hA
    (orthogonal_le inf_le_left (a.sub_starProjection_mem_orthogonal _))

theorem sliceNormal_eq_zero_iff {P : Finset E} (D : DescentPosition R a a₁ ξ)
    (hP : P ∈ parabolics R a₁) (b : simpleRoots a₁ P) :
    sliceNormal R a a₁ b = 0 ↔ restrictedRoot a ((b : a₁) : E) = 0 := by
  rw [← Submodule.coe_eq_zero, coe_sliceNormal_eq_restrictedRoot D hP, Submodule.coe_eq_zero]

section Basis

variable {P : Finset E}

/-- The span of the selected fine simple roots. -/
def sliceNormalSpan (J : Finset (simpleRoots a₁ P)) : Submodule ℝ E :=
  span ℝ (Set.range fun b : J => (((b : simpleRoots a₁ P) : a₁) : E))

theorem sliceNormalSpan_le_fine (J : Finset (simpleRoots a₁ P)) : sliceNormalSpan J ≤ a₁ := by
  apply span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact ((j.val : a₁)).prop

theorem sliceNormalSpan_eq_span_image (J : Finset (simpleRoots a₁ P)) :
    sliceNormalSpan J = span ℝ ((fun b : simpleRoots a₁ P => ((b : a₁) : E)) ''
      (↑J : Set (simpleRoots a₁ P))) := by
  rw [sliceNormalSpan]
  congr 1
  ext x
  exact ⟨fun ⟨j, hj⟩ => ⟨j.val, j.prop, hj⟩,
    fun ⟨j, hj, he⟩ => ⟨⟨j, hj⟩, he⟩⟩

def sliceSpanBasis (hR : IsRootSet R) (ha₁ : IsLeviSpace R a₁)
    (hP : P ∈ parabolics R a₁) (J : Finset (simpleRoots a₁ P)) :
    Basis J ℝ (sliceNormalSpan J) :=
  Basis.span ((simpleRoots_basis hR ha₁ hP).1.comp Subtype.val Subtype.val_injective)

@[simp]
theorem coe_sliceSpanBasis_apply (hR : IsRootSet R) (ha₁ : IsLeviSpace R a₁)
    (hP : P ∈ parabolics R a₁) (J : Finset (simpleRoots a₁ P)) (i : J) :
    (sliceSpanBasis hR ha₁ hP J i : E) = (((i : simpleRoots a₁ P) : a₁) : E) := by
  have hli : LinearIndependent ℝ (fun j : J => (((j : simpleRoots a₁ P) : a₁) : E)) :=
    (simpleRoots_basis hR ha₁ hP).1.comp Subtype.val Subtype.val_injective
  exact congrArg (fun x : sliceNormalSpan J => (x : E)) (Basis.span_apply hli i)

theorem sliceNormalSpan_mk_levi (D : DescentPosition R a a₁ ξ) {J : Finset (simpleRoots a₁ P)}
    (hP : P ∈ parabolics R a₁) : (a₁ ⊓ (sliceNormalSpan J)ᗮ : Submodule ℝ E) ∈ leviSpaces R a₁ := by
  have hPsub : P ⊆ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
  let r (j : J) : E := (exists_root_of_mem_simpleRoots j.val).choose
  have hr (j : J) : r j ∈ R := hPsub (exists_root_of_mem_simpleRoots j.val).choose_spec.1
  have he : sliceNormalSpan J = span ℝ (Set.range fun j : J => (restrictedRoot a₁ (r j) : E)) := by
    have hf : (fun j : J => (((j : simpleRoots a₁ P) : a₁) : E)) =
        (fun j : J => (restrictedRoot a₁ (r j) : E)) := by
      funext j
      exact congrArg Subtype.val (exists_root_of_mem_simpleRoots j.val).choose_spec.2.symm
    rw [sliceNormalSpan, hf]
  rw [he]
  exact exists_leviSpace_inter_projected_roots D.roots D.fine r hr

/-- The fine normal span selected by a projected basis defines a transverse Levi flat. -/
def basisTransverseLevi (D : DescentPosition R a a₁ ξ) (hP : P ∈ parabolics R a₁)
    (J : BasisIndex (sliceNormal R a a₁ (P := P))) : transverseLevis R a a₁ := by
  let W := sliceNormalSpan J.val
  let L := a₁ ⊓ Wᗮ
  have hL : L ∈ leviSpaces R a₁ := sliceNormalSpan_mk_levi D hP
  have hW : a₁ ⊓ Lᗮ = W := by
    simpa only [L, inf_comm] using orthogonal_inf_orthogonal_inf_of_le (sliceNormalSpan_le_fine J.val)
  refine ⟨L, Finset.mem_filter.mpr ⟨hL, ?_⟩⟩
  have hzL : centralSpace R ≤ L := by
    obtain ⟨p, _, hp⟩ := (mem_leviSpaces_iff_exists_point D.roots D.fine).mp hL
    exact hp ▸ centralSpace_le_leviSpaceOf p
  apply (dDescent_ne_zero_iff (centralSpace_le_of_levi D.coarse) D.le_fine hzL).mpr
  let b : Basis J.val ℝ (a₁ ⊓ Lᗮ : Submodule ℝ E) :=
    (sliceSpanBasis D.roots D.fine hP J.val).map (LinearEquiv.ofEq _ _ hW.symm)
  let f := descentProjection a (centralSpace R) a₁ L
  have hcomp : f ∘ b = fun i : J.val => sliceNormal R a a₁ i.val := by
    funext i
    change (noncentral R a).orthogonalProjectionOnto (b i : E) = _
    congr 1
    change (sliceSpanBasis D.roots D.fine hP J.val i : E) = _
    exact coe_sliceSpanBasis_apply D.roots D.fine hP J.val i
  apply LinearMap.bijective_of_linearIndependent_of_span_eq_top b.span_eq
  · rw [hcomp]
    exact J.prop.1
  · rw [hcomp]
    exact J.prop.1.span_eq_top_of_card_eq_finrank' (by simpa using J.prop.2)

/-- The simple-root inequalities at a transverse basis intersection evaluate to their slacks. -/
theorem basisTransversePoint_inner (D : DescentPosition R a a₁ ξ) (hP : P ∈ parabolics R a₁)
    (J : BasisIndex (sliceNormal R a a₁ (P := P))) (i : simpleRoots a₁ P) :
    ⟪((i : a₁) : E), transversePoint D (basisTransverseLevi D hP J)⟫ =
      J.slack i (sliceOffset ξ) := by
  let L := basisTransverseLevi D hP J
  let p := transversePoint D L
  let x : noncentral R a := ⟨p - ξ, (transversePoint_spec D L).2⟩
  let f : Module.Dual ℝ (noncentral R a) := -((innerₗ _ x))
  have hn : f = J.interpolate (sliceOffset ξ) := by
    apply J.basis.ext
    intro j
    rw [J.basis_apply, J.interpolate_apply_of_mem _ j.prop]
    change -⟪x, sliceNormal R a a₁ j.val⟫ = _
    rw [real_inner_comm (sliceNormal R a a₁ j.val) x, sliceNormal_inner]
    have hb : (((j.val : a₁)) : E) ∈ sliceNormalSpan J.val := subset_span (Set.mem_range_self j)
    have hp : p ∈ (sliceNormalSpan J.val)ᗮ := (transversePoint_spec D L).1.1.2
    have hz := hp _ hb
    change -⟪((j.val : a₁) : E), p - ξ⟫ = _
    simp [sliceOffset, inner_sub_right, hz]
  have hf := congrArg (fun g : Module.Dual ℝ (noncentral R a) => g (sliceNormal R a a₁ i)) hn
  change -⟪x, sliceNormal R a a₁ i⟫ = _ at hf
  rw [real_inner_comm (sliceNormal R a a₁ i) x, sliceNormal_inner, inner_sub_right] at hf
  rw [J.slack_apply, ← hf]
  change ⟪((i : a₁) : E), p⟫ = ⟪((i : a₁) : E), ξ⟫ -
    -(⟪((i : a₁) : E), p⟫ - ⟪((i : a₁) : E), ξ⟫)
  ring

/-- General position of the Levi intersections implies regularity of all affine offsets. -/
theorem sliceOffset_regular (D : DescentPosition R a a₁ ξ) (hP : P ∈ parabolics R a₁) :
    Regular (wallForm (sliceNormal R a a₁ (P := P))) (sliceOffset ξ) := by
  intro A hA
  let L := basisTransverseLevi D hP A.1
  let p := transversePoint D L
  obtain ⟨r, hr, hb⟩ := exists_root_of_mem_simpleRoots A.2.val
  have hRr := (Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1) hr
  have hp : p ∈ a₁ := transverseLevi_le_fine D L (transversePoint_spec D L).1.1
  have hrp : ⟪r, p⟫ = 0 := by
    rw [← inner_restrictedRoot hp, hb, basisTransversePoint_inner D hP]
    exact hA
  have hzero : restrictedRoot (L : Submodule ℝ E) r = 0 := by
    by_contra h
    exact (transversePoint_regular D L).2 r hRr h hrp
  have hmem : (((A.2.val : a₁)) : E) ∈ (L : Submodule ℝ E)ᗮ := by
    intro y hy
    have hz := inner_restrictedRoot (a := (L : Submodule ℝ E)) (x := r) hy
    have hy' : y ∈ a₁ := transverseLevi_le_fine D L hy
    rw [real_inner_comm, ← hb, inner_restrictedRoot hy', ← hz, hzero,
      Submodule.coe_zero, inner_zero_left]
  have hW : a₁ ⊓ (L : Submodule ℝ E)ᗮ = sliceNormalSpan A.1.val := by
    change a₁ ⊓ (a₁ ⊓ (sliceNormalSpan A.1.val)ᗮ)ᗮ = _
    simpa only [inf_comm] using orthogonal_inf_orthogonal_inf_of_le (sliceNormalSpan_le_fine A.1.val)
  have hw : (((A.2.val : a₁)) : E) ∈ sliceNormalSpan A.1.val := hW ▸ ⟨(A.2.val : a₁).prop, hmem⟩
  rw [sliceNormalSpan_eq_span_image] at hw
  exact (simpleRoots_basis D.roots D.fine hP).1.notMem_span_image A.2.prop hw

/-- Index the vanishing normals as a subset of the chamber's normal index type. -/
def activeSliceIndices (a₁ : Submodule ℝ E) (P : Finset E) (p : E) :
    Finset (simpleRoots a₁ P) :=
  Finset.univ.filter (fun i : simpleRoots a₁ P => ⟪((i : a₁) : E), p⟫ = 0)

theorem mem_activeSliceIndices_iff {p : E} {i : simpleRoots a₁ P} :
    i ∈ activeSliceIndices a₁ P p ↔ ⟪((i : a₁) : E), p⟫ = 0 := by
  simp [activeSliceIndices]

def activeSliceEquiv (p : E) :
    activeSliceIndices a₁ P p ≃ vanishingSimpleRoots a₁ P p where
  toFun j := ⟨(j.val : a₁), Finset.mem_filter.mpr ⟨j.val.prop, mem_activeSliceIndices_iff.mp j.prop⟩⟩
  invFun j :=
    ⟨⟨j, (Finset.mem_filter.mp j.prop).1⟩, mem_activeSliceIndices_iff.mpr (Finset.mem_filter.mp j.prop).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem activeSliceIndices_at_basisPoint (D : DescentPosition R a a₁ ξ) (hP : P ∈ parabolics R a₁)
    (J : BasisIndex (sliceNormal R a a₁ (P := P))) :
    activeSliceIndices a₁ P (transversePoint D (basisTransverseLevi D hP J)) = J.val := by
  ext i
  rw [mem_activeSliceIndices_iff, basisTransversePoint_inner D hP]
  exact ⟨fun h => by
    by_contra hn
    exact sliceOffset_regular D hP (⟨J, i, hn⟩ : WallIndex _) h,
    fun hi => J.slack_apply_of_mem hi _⟩

theorem basisFeasible_iff (D : DescentPosition R a a₁ ξ) (hP : P ∈ parabolics R a₁)
    (J : BasisIndex (sliceNormal R a a₁ (P := P))) :
    (∀ i ∉ J.val, 0 < J.slack i (sliceOffset ξ)) ↔
      ∀ r ∈ P, 0 ≤ ⟪r, transversePoint D (basisTransverseLevi D hP J)⟫ := by
  let L := basisTransverseLevi D hP J
  have hp : transversePoint D L ∈ a₁ :=
    transverseLevi_le_fine D L (transversePoint_spec D L).1.1
  rw [chamberClosure_iff_nonneg_simpleRoots D.roots D.fine hP hp]
  change (∀ i ∉ J.val, 0 < J.slack i (sliceOffset ξ)) ↔
    ∀ i : simpleRoots a₁ P, 0 ≤ ⟪((i : a₁) : E), transversePoint D (basisTransverseLevi D hP J)⟫
  constructor
  · intro h i
    rw [basisTransversePoint_inner D hP J]
    by_cases hi : i ∈ J.val
    · rw [J.slack_apply_of_mem hi]
    · exact (h i hi).le
  · intro h i hi
    have hle := h i
    rw [basisTransversePoint_inner D hP J] at hle
    exact lt_of_le_of_ne hle (sliceOffset_regular D hP (⟨J, i, hi⟩ : WallIndex _)).symm

private theorem activeSliceSpan_eq_normal (D : DescentPosition R a a₁ ξ)
    (hP : P ∈ parabolics R a₁) (L : transverseLevis R a a₁)
    (hc : ∀ r ∈ P, 0 ≤ ⟪r, transversePoint D L⟫) :
    sliceNormalSpan (activeSliceIndices a₁ P (transversePoint D L)) =
      a₁ ⊓ (L : Submodule ℝ E)ᗮ := by
  let p := transversePoint D L
  have hpa₁ : p ∈ a₁ := transverseLevi_le_fine D L (transversePoint_spec D L).1.1
  have hL := leviSpaceOf_eq_of_isRegular (transverseLevi_isLevi D L) (transversePoint_regular D L)
  let e := activeSliceEquiv (a₁ := a₁) (P := P) p
  have he : sliceNormalSpan (activeSliceIndices a₁ P p) =
      span ℝ (Set.range fun j : vanishingSimpleRoots a₁ P p => ((j : a₁) : E)) := by
    unfold sliceNormalSpan
    congr 1
    exact e.surjective.range_comp (fun j : vanishingSimpleRoots a₁ P p => ((j : a₁) : E))
  rw [← hL, leviSpaceOf_eq_of_vanishingSimpleRoots D.roots D.fine hP hpa₁ hc, ← he]
  simpa only [inf_comm] using
    (orthogonal_inf_orthogonal_inf_of_le (sliceNormalSpan_le_fine (activeSliceIndices a₁ P p))).symm

/-- For a transverse flat whose slice point lies in the chamber closure, the active normals
    give a basis after projection to the coarse space. -/
def activeSliceBasis (D : DescentPosition R a a₁ ξ) (hP : P ∈ parabolics R a₁)
    (L : transverseLevis R a a₁) (hc : ∀ r ∈ P, 0 ≤ ⟪r, transversePoint D L⟫) :
    BasisIndex (sliceNormal R a a₁ (P := P)) := by
  let J := activeSliceIndices a₁ P (transversePoint D L)
  let W : Submodule ℝ E := a₁ ⊓ (L : Submodule ℝ E)ᗮ
  have he := activeSliceSpan_eq_normal D hP L hc
  let b : Basis J ℝ W := (sliceSpanBasis D.roots D.fine hP J).map (LinearEquiv.ofEq _ _ he)
  let f := descentProjection a (centralSpace R) a₁ (L : Submodule ℝ E)
  have hf := (dDescent_ne_zero_iff (centralSpace_le_of_levi D.coarse) D.le_fine
      (centralSpace_le_of_levi (transverseLevi_isLevi D L))).mp (Finset.mem_filter.mp L.prop).2
  let e : W ≃ₗ[ℝ] noncentral R a := LinearEquiv.ofBijective f hf
  refine ⟨J, ?_, ?_⟩
  · have hcomp : f ∘ b = fun i : J => sliceNormal R a a₁ i.val := by
      funext i
      change (noncentral R a).orthogonalProjectionOnto (b i : E) = _
      congr 1
      exact coe_sliceSpanBasis_apply D.roots D.fine hP J i
    rw [← hcomp]
    exact b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf.1)
  · simpa using (finrank_eq_card_basis b).symm.trans (LinearEquiv.finrank_eq e)

theorem basisTransverseLevi_activeSliceBasis (D : DescentPosition R a a₁ ξ) (hP : P ∈ parabolics R a₁)
    (L : transverseLevis R a a₁) (hc : ∀ r ∈ P, 0 ≤ ⟪r, transversePoint D L⟫) :
    basisTransverseLevi D hP (activeSliceBasis D hP L hc) = L := by
  apply Subtype.ext
  change a₁ ⊓ (sliceNormalSpan (activeSliceIndices a₁ P (transversePoint D L)))ᗮ = _
  rw [activeSliceSpan_eq_normal D hP L hc]
  simpa only [inf_comm] using orthogonal_inf_orthogonal_inf_of_le (transverseLevi_le_fine D L)

theorem activeSliceBasis_basisTransverseLevi (D : DescentPosition R a a₁ ξ)
    (hP : P ∈ parabolics R a₁) (J : BasisIndex (sliceNormal R a a₁ (P := P)))
    (hc : ∀ r ∈ P, 0 ≤ ⟪r, transversePoint D (basisTransverseLevi D hP J)⟫) :
    activeSliceBasis D hP (basisTransverseLevi D hP J) hc = J :=
  Subtype.ext (activeSliceIndices_at_basisPoint D hP J)

end Basis

/-- Evaluate an imaginary parameter as a complex-valued real-linear functional. -/
def imaginaryEval (Λ : StrongDual ℝ a) : a →ₗ[ℝ] ℂ where
  toFun x := Complex.I * (Λ x : ℂ)
  map_add' x y := by simp [mul_add]
  map_smul' t x := by simp [Complex.real_smul, smul_eq_mul]; ring

/-- The coarse parameter on the noncentral slice. -/
def sliceParameter (R : Finset E) (Λ : StrongDual ℝ a) : noncentral R a →ₗ[ℝ] ℂ :=
  (imaginaryEval Λ).comp (Submodule.inclusion inf_le_left)

theorem sliceParameter_apply_normal {P : Finset E} (D : DescentPosition R a a₁ ξ)
    (hP : P ∈ parabolics R a₁) (Λ : StrongDual ℝ a) (i : simpleRoots a₁ P) :
    sliceParameter R Λ (sliceNormal R a a₁ i) =
      Complex.I * (extendParam a a₁ Λ (i : a₁) : ℂ) := by
  have he : Submodule.inclusion inf_le_left (sliceNormal R a a₁ i) =
      restrictedRoot a ((i : a₁) : E) :=
    Subtype.ext (coe_sliceNormal_eq_restrictedRoot D hP i)
  change Complex.I * (Λ (Submodule.inclusion inf_le_left (sliceNormal R a a₁ i)) : ℂ) = _
  rw [he]
  rfl

/-- Algebraic form of the reciprocal denominator, valid also at singular parameters. -/
theorem theta_inv_eq_gram_div (a : Submodule ℝ E) (S : Finset E) (Λ : StrongDual ℝ a) :
    (theta a S Λ)⁻¹ = (gramVolume (fun j : simpleRoots a S => ((j : a) : E)) : ℂ) /
      ∏ j : simpleRoots a S, (Complex.I * (Λ (j : a) : ℂ)) := by
  simp [theta, thetaOf, div_eq_mul_inv, mul_comm]

/-- The affine vertex weight equals the descent coefficient times the relative chamber term. -/
theorem weight_activeSliceBasis {P : Finset E} (D : DescentPosition R a a₁ ξ)
    (hP : P ∈ parabolics R a₁) (L : transverseLevis R a a₁)
    (hc : ∀ r ∈ P, 0 ≤ ⟪r, transversePoint D L⟫) (Λ : StrongDual ℝ a) :
    weight (sliceNormal R a a₁ (P := P)) (sliceParameter R Λ) (activeSliceBasis D hP L hc) =
      (dDescent a (centralSpace R) a₁ L : ℂ) *
        (theta a₁ (P ∩ leviRoots R (posSet R (transversePoint D L))) (extendParam a a₁ Λ))⁻¹ := by
  let p := transversePoint D L
  let S := P ∩ leviRoots R (posSet R p)
  let J := activeSliceIndices a₁ P p
  have hp : p ∈ a₁ := transverseLevi_le_fine D L (transversePoint_spec D L).1.1
  have hPsub : P ⊆ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
  have hs : simpleRoots a₁ S = vanishingSimpleRoots a₁ P p :=
    simpleRoots_inter_leviRoots_of_nonneg D.roots hPsub hp hc
  let e₀ : vanishingSimpleRoots a₁ P p ≃ simpleRoots a₁ S :=
    Equiv.subtypeEquivRight (fun j => by rw [hs])
  let e := (activeSliceEquiv (a₁ := a₁) (P := P) p).trans e₀
  have he (i : J) : (e i : a₁) = (i.val : a₁) := rfl
  let W : Submodule ℝ E := a₁ ⊓ (L : Submodule ℝ E)ᗮ
  let b : Basis J ℝ W :=
    (sliceSpanBasis D.roots D.fine hP J).map (LinearEquiv.ofEq _ _ (activeSliceSpan_eq_normal D hP L hc))
  have hb (i : J) : (b i : E) = ((i.val : a₁) : E) :=
    coe_sliceSpanBasis_apply D.roots D.fine hP J i
  have hvol := dDescent_mul_gramVolume (centralSpace_le_of_levi D.coarse) D.le_fine
    (centralSpace_le_of_levi (transverseLevi_isLevi D L)) (Finset.mem_filter.mp L.prop).2 b
  have hproj : (fun i => descentProjection a (centralSpace R) a₁ L (b i)) =
      (fun i : J => sliceNormal R a a₁ i.val) := by
    funext i
    change (noncentral R a).orthogonalProjectionOnto (b i : E) = _
    rw [hb]
    rfl
  rw [hproj] at hvol
  have hvol' : gramVolume (fun i => (b i : E)) =
      gramVolume (fun j : simpleRoots a₁ S => ((j : a₁) : E)) := by
    rw [← gramVolume_reindex e]
    congr 1
    funext i
    change (b i : E) = ((e i : a₁) : E)
    rw [he, hb]
  have hprod : (∏ i ∈ J, sliceParameter R Λ (sliceNormal R a a₁ i)) =
      ∏ j : simpleRoots a₁ S, (Complex.I * (extendParam a a₁ Λ (j : a₁) : ℂ)) := by
    rw [← Finset.prod_coe_sort]
    apply Fintype.prod_equiv e
    intro i
    rw [he, sliceParameter_apply_normal D hP]
  unfold weight
  change (gramVolume (fun i : J => sliceNormal R a a₁ i.val) : ℂ) /
    (∏ i ∈ J, sliceParameter R Λ (sliceNormal R a a₁ i)) =
    (dDescent a (centralSpace R) a₁ L : ℂ) * (theta a₁ S (extendParam a a₁ Λ))⁻¹
  rw [hprod, ← hvol, hvol', Complex.ofReal_mul, theta_inv_eq_gram_div, mul_div_assoc]

end Langlands.GMFamily

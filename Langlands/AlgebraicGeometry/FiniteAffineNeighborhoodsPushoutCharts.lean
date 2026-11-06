import Langlands.AlgebraicGeometry.FiniteAffineNeighborhoodsPushoutStatement
import Langlands.AlgebraicGeometry.AffineSchemePushoutStatement
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Pushout-side facts for finite-set affine neighborhoods -/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.FinitePinching

/-- The finite-set affine-neighborhood property is invariant under isomorphism. -/
theorem hasFiniteAffineNeighborhoods_of_iso {P₀ P : Scheme.{u}} (e : P₀ ≅ P)
    (h : PointTopology.HasFiniteAffineNeighborhoods P₀) :
    PointTopology.HasFiniteAffineNeighborhoods P := by
  intro S hS
  obtain ⟨W, hW⟩ := h (e.inv '' S) (hS.image _)
  refine ⟨⟨e.inv ⁻¹ᵁ W.1, W.2.preimage_of_isIso e.inv⟩, fun p hp => hW ⟨p, hp, rfl⟩⟩

/-- Finite fibres of `j` and finite-set affine neighborhoods on `X` give the
fibre-neighborhood hypothesis of `IntegralSchemePushoutStatement`. -/
theorem exists_affineOpen_fibre {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) [IsFinite j]
    (hX : PointTopology.HasFiniteAffineNeighborhoods X) (y : Y) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U := by
  obtain ⟨U, hU⟩ := hX (i '' (j ⁻¹' {y})) ((j.finite_preimage_singleton y).image i)
  exact ⟨U.1, U.2, fun z hz => hU ⟨z, hz, rfl⟩⟩

/-- Compatible affine pairs for a span `X ← Z → Y`: finite sets `E ⊆ X`, disjoint
from the range of `i`, and `F ⊆ Y` lie in affine opens `U` of `X` and `V` of `Y`
with the same inverse image in `Z`. -/
def HasCompatibleAffinePairs {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) : Prop :=
  ∀ (E : Set X) (F : Set Y), E.Finite → F.Finite → Disjoint E (Set.range i) →
    ∃ U : X.affineOpens, ∃ V : Y.affineOpens, E ⊆ U.1 ∧ F ⊆ V.1 ∧ i ⁻¹ᵁ U.1 = j ⁻¹ᵁ V.1

/-- Affine charts of a commutative square over compatible affine pairs: every
pair of affine opens `U` of `X` and `V` of `Y` with the same inverse image in `Z`
lies in one affine open `W` of `P`, in the sense `U ≤ a ⁻¹ᵁ W` and
`V ≤ b ⁻¹ᵁ W`. -/
def HasAffineCharts {X Y Z P : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (a : X ⟶ P)
    (b : Y ⟶ P) : Prop :=
  ∀ (U : X.affineOpens) (V : Y.affineOpens), i ⁻¹ᵁ U.1 = j ⁻¹ᵁ V.1 →
    ∃ W : P.affineOpens, U.1 ≤ a ⁻¹ᵁ W.1 ∧ V.1 ≤ b ⁻¹ᵁ W.1

variable {X Y Z P : Scheme.{u}} {i : Z ⟶ X} {j : Z ⟶ Y} {a : X ⟶ P} {b : Y ⟶ P}

/-- Points identified by the two legs of a pullback square come from a point of
the corner. -/
theorem exists_eq_of_isPullback (h : IsPullback i j a b) (x : X) (y : Y) (hxy : a x = b y) :
    ∃ z : Z, i z = x ∧ j z = y := by
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨h.isoPullback.inv w, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hw₁]
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hw₂]

/-- No proper closed subscheme of a scheme pushout receives both legs: the
closures of the images of the two legs cover the pushout. -/
theorem closure_range_union_closure_range_eq_univ (h : IsPushout i j a b)
    [QuasiCompact a] [QuasiCompact b] :
    closure (Set.range a) ∪ closure (Set.range b) = Set.univ := by
  let I : P.IdealSheafData := a.ker * b.ker
  have ha : I ≤ a.ker := fun U => by
    change a.ker.ideal U * b.ker.ideal U ≤ _
    exact Ideal.mul_le_left
  have hb : I ≤ b.ker := fun U => by
    change a.ker.ideal U * b.ker.ideal U ≤ _
    exact Ideal.mul_le_right
  let fa : X ⟶ I.subscheme := a.toImage ≫ Scheme.IdealSheafData.inclusion ha
  let fb : Y ⟶ I.subscheme := b.toImage ≫ Scheme.IdealSheafData.inclusion hb
  have hfa : fa ≫ I.subschemeι = a := by simp [fa]
  have hfb : fb ≫ I.subschemeι = b := by simp [fb]
  have hw : i ≫ fa = j ≫ fb := by
    rw [← cancel_mono I.subschemeι]
    simp [fa, fb, h.w]
  have hs : h.desc fa fb hw ≫ I.subschemeι = 𝟙 P :=
    h.hom_ext (by simp [hfa]) (by simp [hfb])
  refine Set.eq_univ_of_forall fun p => ?_
  have hp : p ∈ Set.range I.subschemeι :=
    ⟨h.desc fa fb hw p, by rw [← Scheme.Hom.comp_apply, hs]; rfl⟩
  rw [Scheme.IdealSheafData.range_subschemeι] at hp
  simpa [I, Scheme.Hom.support_ker] using hp

/-- In a scheme pushout whose legs are quasi-compact closed maps, every point
lies in the image of one of the legs. -/
theorem mem_range_or_mem_range_of_isPushout (h : IsPushout i j a b)
    [QuasiCompact a] [QuasiCompact b] (ha : IsClosedMap a) (hb : IsClosedMap b) (p : P) :
    p ∈ Set.range a ∨ p ∈ Set.range b := by
  have hcov := closure_range_union_closure_range_eq_univ h
  rw [ha.isClosed_range.closure_eq, hb.isClosed_range.closure_eq] at hcov
  have hp : p ∈ Set.range a ∪ Set.range b := by
    rw [hcov]
    exact Set.mem_univ p
  exact hp

/-- Final assembly: joint surjectivity of the legs, compatible affine pairs
around finite sets, and affine charts over compatible affine pairs give
finite-set affine neighborhoods on the pushout corner. -/
theorem hasFiniteAffineNeighborhoods_of_compatibleCharts
    (hw : i ≫ a = j ≫ b)
    (hsurj : ∀ p : P, p ∈ Set.range a ∨ p ∈ Set.range b)
    (hpair : HasCompatibleAffinePairs i j)
    (hchart : HasAffineCharts i j a b) :
    PointTopology.HasFiniteAffineNeighborhoods P := by
  classical
  intro S hS
  have : Finite S := hS.to_subtype
  let fB : {s : S // (s : P) ∈ Set.range b} → Y := fun s => s.2.choose
  let fA : {s : S // (s : P) ∉ Set.range b} → X :=
    fun s => ((hsurj s.1).resolve_right s.2).choose
  have hfB : ∀ s, b (fB s) = s.1 := fun s => s.2.choose_spec
  have hfA : ∀ s, a (fA s) = s.1 := fun s => ((hsurj s.1).resolve_right s.2).choose_spec
  have hEZ : Disjoint (Set.range fA) (Set.range i) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, rfl⟩ ⟨z, hz⟩
    refine s.2 ⟨j z, ?_⟩
    rw [← hfA s, ← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hw]
  obtain ⟨U, V, hEU, hFV, hUV⟩ :=
    hpair _ _ (Set.finite_range fA) (Set.finite_range fB) hEZ
  obtain ⟨W, hUW, hVW⟩ := hchart U V hUV
  refine ⟨W, fun p hp => ?_⟩
  by_cases hpb : p ∈ Set.range b
  · have hmem := hVW (hFV ⟨⟨⟨p, hp⟩, hpb⟩, rfl⟩)
    rwa [Scheme.Hom.mem_preimage, hfB] at hmem
  · have hmem := hUW (hEU ⟨⟨⟨p, hp⟩, hpb⟩, rfl⟩)
    rwa [Scheme.Hom.mem_preimage, hfA] at hmem

/-- Transfer to an arbitrary scheme pushout: one model pushout with an integral
leg, a closed-immersion leg and affine charts over compatible affine pairs makes
every pushout of the same span have finite-set affine neighborhoods. -/
theorem hasFiniteAffineNeighborhoods_of_model
    (hpair : HasCompatibleAffinePairs i j)
    {P₀ : Scheme.{u}} {a₀ : X ⟶ P₀} {b₀ : Y ⟶ P₀} (h₀ : IsPushout i j a₀ b₀)
    [IsIntegralHom a₀] [IsClosedImmersion b₀]
    (hchart : HasAffineCharts i j a₀ b₀)
    (h : IsPushout i j a b) : PointTopology.HasFiniteAffineNeighborhoods P :=
  hasFiniteAffineNeighborhoods_of_iso (h₀.isoIsPushout _ _ h)
    (hasFiniteAffineNeighborhoods_of_compatibleCharts h₀.w
      (mem_range_or_mem_range_of_isPushout h₀ a₀.isClosedMap b₀.isClosedMap) hpair hchart)

/-- A scheme pushout of a closed immersion and a morphism between affine schemes
is affine, given the affine scheme pushout theorem. -/
theorem isAffine_of_isPushout (hA : AffineSchemePushoutStatement.{u})
    (h : IsPushout i j a b) [IsClosedImmersion i] [IsAffine X] [IsAffine Y] : IsAffine P := by
  have : IsAffine Z := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  have hsurj : Function.Surjective i.appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hpb := IsPullback.of_hasPullback i.appTop j.appTop
  have hSpec := hA _ _ _ _ i.appTop j.appTop _ _ hsurj hpb
  have h' : IsPushout i j (X.isoSpec.hom ≫ Spec.map (pullback.fst i.appTop j.appTop))
      (Y.isoSpec.hom ≫ Spec.map (pullback.snd i.appTop j.appTop)) :=
    hSpec.of_iso' Z.isoSpec X.isoSpec Y.isoSpec (Iso.refl _)
      (Scheme.isoSpec_hom_naturality i) (Scheme.isoSpec_hom_naturality j)
      (by simp) (by simp)
  exact .of_isIso (h.isoIsPushout _ _ h').hom

end Langlands.AlgebraicGeometry.FinitePinching

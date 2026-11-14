import Langlands.GroupScheme.Reductive.IsogenyRootFactors
import Langlands.GroupScheme.Reductive.IsogenyTorusRestriction
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Torus.WeightDecomposition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Option

/-! # The actual root-index bijection of a split reductive isogeny -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj DirectSum TensorProduct
open Langlands.LinearAlgebra.RationalSpan

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace IsRootDatumOf

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]
    {J J' : Type u} [Finite J] [Finite J']
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {P' : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')

include hP

omit [Finite J] hP in
/-- Self-centralization identifies the zero adjoint weight with the actual
tangent of the specified torus. -/
theorem zeroWeight_eq_torusTangent
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) :
    weightSpace i 0 = RelativeRoot.tangentSubmodule (SubgroupFunctor.range i) := by
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  ext X
  change X ∈ weightSpace i 0 ↔ X.toMul.val ∈ (SubgroupFunctor.range i).carrier _
  rw [← maximalTorusCentralizer k G hG T i hi]
  exact (Lie.mem_torusCentralizer_iff_mem_weightSpace_zero i X.toMul).symm

/-- The actual Lie dimension equals the dimension of the specified split
maximal torus plus the number of roots in the supplied actual datum. -/
theorem finrank_lie_eq_torus_add_card
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) :
    letI := hT.isAffineHom
    Module.finrank k (Additive (lieKernel G k)) =
      Module.finrank k (Additive (lieKernel T.toGrp k)) + Nat.card J := by
  classical
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  let : Smooth G.X.hom := hG.smooth
  let : Fintype J := Fintype.ofFinite J
  have := Lie.finiteDimensional_lieKernel G
  let f : Option J → characterLattice T := fun a => a.elim 0 (fun r => P.root r)
  let W : Option J → Submodule k (Additive (lieKernel G k)) :=
    fun a => weightSpace i (f a)
  have hf : Function.Injective f := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim (P.ne_zero b h.symm)
    | some a =>
      cases b with
      | none => exact False.elim (P.ne_zero a h)
      | some b => exact congrArg some (P.root.injective h)
  have hI : DirectSum.IsInternal W := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSupIndep.comp hf
    · apply top_unique
      rw [← (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSup_eq_top]
      apply iSup_le
      intro χ
      by_cases hχ : χ = 0
      · subst χ
        exact le_iSup W none
      · by_cases hroot : weightSpace i χ = ⊥
        · rw [hroot]; exact bot_le
        · obtain ⟨a, rfl⟩ := hP.2.1 ▸ (show χ ∈ roots i from ⟨hχ, hroot⟩)
          exact le_iSup W (some a)
  have hzero : Module.finrank k (W none) =
      Module.finrank k (Additive (lieKernel T.toGrp k)) := by
    change Module.finrank k (weightSpace i 0) = _
    rw [zeroWeight_eq_torusTangent hG hT hi]
    let : Mono i.hom.hom := Over.mono_of_mono_left _
    exact RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy
      (SubgroupFunctor.range i) i ⟨inferInstance, rfl⟩
  have hroot (a : J) : Module.finrank k (W (some a)) = 1 := by
    obtain ⟨l⟩ := splitRootLieLine k G hG T hT i hi (P.root a)
      (hP.2.1 ▸ Set.mem_range_self a)
    change Module.finrank k (weightSpace i (P.root a)) = 1
    rw [← l.finrank_eq, Module.finrank_self]
  calc
    Module.finrank k (Additive (lieKernel G k)) =
        Module.finrank k (⨁ a : Option J, W a) :=
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hI).finrank_eq.symm
    _ = ∑ a : Option J, Module.finrank k (W a) := Module.finrank_directSum k _
    _ = Module.finrank k (Additive (lieKernel T.toGrp k)) + Nat.card J := by
      simp [Fintype.sum_option, hzero, hroot, Nat.card_eq_fintype_card]

include hP'

/-- Smooth isogeny dimensions for the groups and their specified maximal
tori give equality of the actual root counts. -/
theorem card_eq_of_isogeny
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (φ : G ⟶ G') (hφ : IsIsogeny φ) (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') :
    Nat.card J = Nat.card J' := by
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let : IsAffineHom T'.toGrp.X.hom := hT'.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : Smooth G'.X.hom := hG'.smooth
  let : Smooth T.toGrp.X.hom := hT.smooth
  let : Smooth T'.toGrp.X.hom := hT'.smooth
  have hd := Lie.finrank_kernel_eq_of_isogeny φ hφ
  have htd := Lie.finrank_kernel_eq_of_isogeny (CommGroupScheme.groupHom t)
    (hφ.isIsogeny_torusRestriction hG hG' hi hi' φ t ht)
  rw [hP.finrank_lie_eq_torus_add_card hG hT hi,
    hP'.finrank_lie_eq_torus_add_card hG' hT' hi', htd] at hd
  omega

omit [Finite J] [Finite J'] hP hP' in
/-- A map of reduced root indices with nonzero positive integer root factors
is injective. -/
theorem rootIndex_injective [P.IsReduced]
    (hT : IsSplitTorus T.toGrp) (t : T ⟶ T') (f : J → J')
    (q : J → ℕ) (hq : ∀ r, q r ≠ 0)
    (heq : ∀ r, t ≫ P'.root (f r) = q r • P.root r) :
    Function.Injective f := by
  let : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice T) :=
    IsAddTorsionFree.of_module_rat _
  let : IsAddTorsionFree (characterLattice T) :=
    hT.character_toRat_injective.isAddTorsionFree toRat
  intro r s hrs
  have h : q r • P.root r = q s • P.root s := by rw [← heq r, ← heq s, hrs]
  have hlin : ¬ LinearIndependent ℤ ![P.root r, P.root s] := by
    intro hlin
    have hz : (q r : ℤ) • P.root r + -(q s : ℤ) • P.root s = 0 := by
      simpa only [neg_smul, ← sub_eq_add_neg, sub_eq_zero, Nat.cast_smul_eq_nsmul] using h
    have hcoeff := (LinearIndependent.pair_iff.mp hlin) _ _ hz
    exact hq r (Int.natCast_eq_zero.mp hcoeff.1)
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) r s hlin with he | he
  · exact P.root.injective he
  · rw [he, smul_neg] at h
    have hz : (-(q r : ℤ)) • P.root s = (q s : ℤ) • P.root s := by
      simpa only [neg_smul, Nat.cast_smul_eq_nsmul] using h
    have hcoeff := smul_left_injective ℤ (P.ne_zero s) hz
    have hr := Nat.pos_of_ne_zero (hq r)
    have hs := Nat.pos_of_ne_zero (hq s)
    omega

/-- The actual root-index equivalence of a split reductive isogeny, oriented
from source indices to target indices. -/
def isogenyRootIndexEquiv [P.IsReduced]
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (φ : G ⟶ G') (hφ : IsIsogeny φ) (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') : J ≃ J' := by
  let : IsFinite φ.hom.hom.left := hφ.1
  let : Smooth G'.X.hom := hG'.smooth
  let a := hP.isogenyRootFactor hP' hG hT hT' hi φ t ht
  let f : J → J' := fun r => (a r).1
  have hinj : Function.Injective f :=
    rootIndex_injective hT t f (fun r => ringExpChar k ^ (a r).2.val)
      (fun _ => pow_ne_zero _ (expChar_ne_zero k (ringExpChar k)))
      (fun r => (a r).2.property)
  exact Equiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hinj, hP.card_eq_of_isogeny hP' hG hG' hT hT' hi hi' φ hφ t ht⟩)

/-- The chosen equivalence retains the exact integral pullback equation. -/
theorem isogenyRootIndexEquiv_spec [P.IsReduced]
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (φ : G ⟶ G') (hφ : IsIsogeny φ) (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') (r : J) :
    ∃ n : ℕ, t ≫ P'.root (hP.isogenyRootIndexEquiv hP' hG hG' hT hT' hi hi' φ hφ t ht r) =
      ringExpChar k ^ n • P.root r := by
  let : IsFinite φ.hom.hom.left := hφ.1
  let : Smooth G'.X.hom := hG'.smooth
  exact ⟨(hP.isogenyRootFactor hP' hG hT hT' hi φ t ht r).2.val,
    (hP.isogenyRootFactor hP' hG hT hT' hi φ t ht r).2.property⟩

end IsRootDatumOf
end Langlands.GroupScheme

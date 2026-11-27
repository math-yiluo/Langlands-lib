import Langlands.Global.ArthurTruncationCutoffCovariance
import Langlands.Global.ArthurTruncationCuspidal
import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.EisensteinConstantTerm.Core

/-! # Rational invariance and the fixed-point criterion for truncation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  AdelicGroupPoints ArthurParabolicSpaces EisensteinConstantTerm

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

section Covariance

variable {P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine U.X.left]

/-- Transport of the normalized subgroup constant term along equality of its subgroup maps. -/
theorem subgroupConstantTerm_congr_hom
    {j j' : U ⟶ G} [IsClosedImmersion j.hom.hom.left]
    [IsClosedImmersion j'.hom.hom.left] (h : j = j') :
    subgroupConstantTerm F j = subgroupConstantTerm F j' := by
  subst j'
  rfl

/-- A rational point of the parabolic preserves the normalized radical integral. -/
theorem subgroupConstantTerm_rational_mul (p : P ⟶ G) (j : U ⟶ P)
    [IsClosedImmersion (j ≫ p).hom.hom.left] (hU : LeviSubgroup.IsGeometricUnipotentRadical j)
    (φ : AdelicGroupPoints F G → ℂ)
    (hφ : ∀ r ∈ rationalSubgroup F G, ∀ x, φ (r * x) = φ x)
    (r : RationalGroupPoints F P) (x : AdelicGroupPoints F G) :
    subgroupConstantTerm F (j ≫ p) φ (map F P G p (rational F P r) * x) =
      subgroupConstantTerm F (j ≫ p) φ x := by
  let V := SubgroupFunctor.range (j ≫ p)
  let A := AdelicSubgroupPoints.adelicPoints F G V
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G V
  let Q := AdelicSubgroupPoints.RationalQuotient F G V
  let : IsClosed (A : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (j ≫ p)
  let : CompactSpace Q := AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent
    F (j ≫ p) hU.1.smooth hU.1.connectedSpace hU.1.isUnipotent
  let : BorelSpace Q := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let w := map F P G p (rational F P r)
  have hw : w ∈ rationalSubgroup F G := rationalImage_le_rationalSubgroup p ⟨r, rfl⟩
  let a := conjAdelic p j hU.1.isNormal (rational F P r⁻¹)
  have ha := conjAdelic_mem_rationalSubgroup_iff p j hU.1.isNormal r⁻¹
  let e := Langlands.QuotientIntegration.quotientAutomorphism Γ a ha
  have he := AdelicSubgroupPoints.measurePreserving_rationalQuotientAutomorphism F G V a ha
  let m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V
  have hinv (y : AdelicGroupPoints F G) (aRat : Γ) (n : A) :
      φ ((((aRat : A) : AdelicGroupPoints F G) * n) * y) =
        φ ((n : AdelicGroupPoints F G) * y) := by
    rw [mul_assoc]
    apply hφ
    exact rationalImage_le_rationalSubgroup (j ≫ p)
      ((mem_rationalSubgroup_range_iff _ _).mp aRat.property)
  let f (y : AdelicGroupPoints F G) :=
    LeftCosetSpace.lift Γ (fun n : A => φ ((n : AdelicGroupPoints F G) * y)) (hinv y)
  have hf (y : AdelicGroupPoints F G) (q : Q) :
      f y q = φ (((q.out : A) : AdelicGroupPoints F G) * y) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hchange : f (w * x) = f x ∘ e := by
    funext q
    obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
    change φ ((n : AdelicGroupPoints F G) * (w * x)) =
      φ ((a n : AdelicGroupPoints F G) * x)
    have hmul : (n : AdelicGroupPoints F G) * (w * x) =
        w * ((a n : AdelicGroupPoints F G) * x) := by
      have hwr : map F P G p (rational F P r⁻¹) = w⁻¹ := by simp only [w, map_inv]
      rw [show (a n : AdelicGroupPoints F G) =
        map F P G p (rational F P r⁻¹) * n * (map F P G p (rational F P r⁻¹))⁻¹
        from conjAdelic_coe p j hU.1.isNormal (rational F P r⁻¹) n, hwr, inv_inv]
      group
    rw [hmul, hφ w hw]
  unfold subgroupConstantTerm
  change (∫ q : Q, _ ∂m) = ∫ q : Q, _ ∂m
  simp only [← hf]
  rw [hchange]
  exact he.integral_comp e.measurableEmbedding _

end Covariance

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

include hG hi hν in
omit [Mono i.hom.hom.left] in
/-- The standard constant term is left invariant under the rational points of its parabolic. -/
theorem constantTerm_parabolicRational_mul {S : Set (characterLattice T)}
    (hS : S ⊆ simpleRelativeRoots i ν)
    (φ : AdelicGroupPoints F G → ℂ)
    (hφ : ∀ r ∈ rationalSubgroup F G, ∀ x, φ (r * x) = φ x)
    {r : AdelicGroupPoints F G}
    (hr : r ∈ parabolicRationalImage (Standard.parabolicHom i ν S))
    (x : AdelicGroupPoints F G) :
    constantTerm F i ν S φ (r * x) = constantTerm F i ν S φ x := by
  let p := Standard.parabolicHom i ν S
  let j := Standard.unipotentToParabolic i ν S
  have hj : j ≫ p = Standard.unipotentHom i ν S := Standard.unipotentToParabolic_comp i ν S
  let : IsClosedImmersion (j ≫ p).hom.hom.left := hj ▸ inferInstanceAs
    (IsClosedImmersion (Standard.unipotentHom i ν S).hom.hom.left)
  have hU := (Standard.parabolicStructure i ν hG hi hν S hS).2.2.1
  rw [mem_parabolicRationalImage_iff, AdelicGroupPoints.mem_rationalImage_iff] at hr
  obtain ⟨r, rfl⟩ := hr
  change subgroupConstantTerm F (Standard.unipotentHom i ν S) φ _ =
    subgroupConstantTerm F (Standard.unipotentHom i ν S) φ _
  rw [← subgroupConstantTerm_congr_hom hj]
  exact
    subgroupConstantTerm_rational_mul p j hU φ hφ r x

include hν in
/-- Each parabolic summand in `Λᵀ` is independent of the left rational representative. -/
theorem truncationKernel_parabolicRational_mul {S : Set (characterLattice T)}
    (hS : S ⊆ simpleRelativeRoots i ν) (Tp : V T)
    (φ : AdelicGroupPoints F G → ℂ)
    (hφ : ∀ r ∈ rationalSubgroup F G, ∀ x, φ (r * x) = φ x)
    {r : AdelicGroupPoints F G}
    (hr : r ∈ parabolicRationalImage (Standard.parabolicHom i ν S))
    (x : AdelicGroupPoints F G) :
    constantTerm F i ν S φ (r * x) *
        (ArthurRelative.tauHat hG hi ν D S (simpleRelativeRoots i ν)
          (height hi hK hρ (r * x) - Tp) : ℂ) =
      constantTerm F i ν S φ x *
        (ArthurRelative.tauHat hG hi ν D S (simpleRelativeRoots i ν)
          (height hi hK hρ x - Tp) : ℂ) := by
  rw [constantTerm_parabolicRational_mul hG hi hν hS φ hφ hr x,
    tauHat_parabolicRational_mul hG hi hν D hK hρ hS hr x Tp]

include hν in
/-- Truncation preserves pointwise left `G(F)`-invariance. -/
theorem truncation_rational_mul (Tp : V T) (φ : AdelicGroupPoints F G → ℂ)
    (hφ : ∀ r ∈ rationalSubgroup F G, ∀ x, φ (r * x) = φ x)
    {r : AdelicGroupPoints F G} (hr : r ∈ rationalSubgroup F G)
    (x : AdelicGroupPoints F G) :
    truncation hG hi D hK hρ Tp φ (r * x) = truncation hG hi D hK hρ Tp φ x := by
  classical
  unfold truncation
  refine Finset.sum_congr rfl fun S hS => congrArg (_ * ·) ?_
  have hroots : (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    fun a ha => (mem_simpleFinset hG hi).mp ((Finset.mem_powerset.mp hS) ha)
  let J := (S : Set (characterLattice T))
  let p := Standard.parabolicHom i ν J
  let A := parabolicRationalImage p
  have hcosets : A.subgroupOf (rationalSubgroup F G) = parabolicRationalSubgroup F p := by
    apply Subgroup.comap_map_eq_self_of_injective
    exact Subtype.val_injective
  let g (y : AdelicGroupPoints F G) :=
    constantTerm F i ν J φ y * (ArthurRelative.tauHat hG hi ν D J (simpleRelativeRoots i ν)
      (height hi hK hρ y - Tp) : ℂ)
  change (∑' c : ParabolicRationalCosets F p, g ((c.out : rationalSubgroup F G).val * (r * x))) =
    ∑' c : ParabolicRationalCosets F p, g ((c.out : rationalSubgroup F G).val * x)
  have h := tsum_out_mul_left (P := A) (g := g) (fun _ hz y =>
    truncationKernel_parabolicRational_mul hG hi hν D hK hρ hroots Tp φ hφ hz y) hr x
  change (∑' c : LeftCosetSpace (A.subgroupOf (rationalSubgroup F G)),
      g ((c.out : rationalSubgroup F G).val * (r * x))) =
    ∑' c : LeftCosetSpace (A.subgroupOf (rationalSubgroup F G)),
      g ((c.out : rationalSubgroup F G).val * x) at h
  rwa [hcosets] at h

include hν in
/-- A rational-invariant function with vanishing constant terms on the active cutoffs
is fixed by truncation. -/
theorem truncation_eq_self_of_constantTerm_vanishing
    (Tp : V T) (φ : AdelicGroupPoints F G → ℂ)
    (hφ : ∀ r ∈ rationalSubgroup F G, ∀ x, φ (r * x) = φ x)
    (hvanish : ∀ S ∈ (simpleFinset ν hG hi).powerset, ∀ x : AdelicGroupPoints F G,
      (∃ β ∈ simpleRelativeRoots i ν, β ∉ (S : Set (characterLattice T)) ∧
        0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β
          (height hi hK hρ x - Tp)) →
      constantTerm F i ν (S : Set (characterLattice T)) φ x = 0) :
    truncation hG hi D hK hρ Tp φ = φ := by
  classical
  let roots := simpleFinset ν hG hi
  have hroots : (roots : Set (characterLattice T)) = simpleRelativeRoots i ν := by
    ext α
    exact mem_simpleFinset hG hi
  funext x
  unfold truncation
  change (∑ S ∈ roots.powerset, _) = φ x
  rw [Finset.sum_eq_single_of_mem roots (Finset.mem_powerset.mpr subset_rfl)]
  · let term (J : Set (characterLattice T)) : ℂ :=
      ∑' c : ParabolicRationalCosets F (Standard.parabolicHom i ν J),
        constantTerm F i ν J φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
          (ArthurRelative.tauHat hG hi ν D J (simpleRelativeRoots i ν)
            (height hi hK hρ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x) -
              Tp) : ℂ)
    change (-1 : ℂ) ^ (roots.card - roots.card) * term roots = φ x
    simp only [Nat.sub_self, pow_zero, one_mul, hroots]
    unfold term
    rw [constantTerm_full_eq]
    have htau (H : V T) : ArthurRelative.tauHat hG hi ν D (simpleRelativeRoots i ν)
        (simpleRelativeRoots i ν) H = 1 := by
      rw [ArthurRelative.tauHat_eq hG hi D _ Set.Subset.rfl]
      simp
    simp only [htau, Int.cast_one, mul_one, hφ _ (Subtype.property _) x]
    let p := Standard.parabolicHom i ν (simpleRelativeRoots i ν)
    let q₀ : ParabolicRationalCosets F p := Quotient.mk _ 1
    change (∑' _ : ParabolicRationalCosets F p, φ x) = φ x
    refine tsum_eq_single (f := fun _ : ParabolicRationalCosets F p => φ x) q₀ (fun q hq => ?_)
    have hsame : q = q₀ := by
      induction q using Quotient.inductionOn with
      | h q =>
        apply Quotient.sound
        change QuotientGroup.rightRel (parabolicRationalSubgroup F p) q 1
        rw [QuotientGroup.rightRel_apply, parabolicRationalSubgroup_full_eq_top hG hi hν]
        trivial
    exact (hq hsame).elim
  · intro S hS hne
    have hsub : S ⊆ roots := Finset.mem_powerset.mp hS
    obtain ⟨β, hβ, hnβ⟩ := Finset.not_subset.mp (fun h => hne (Finset.Subset.antisymm hsub h))
    suffices hzero : ∀ c : ParabolicRationalCosets F
        (Standard.parabolicHom i ν (S : Set (characterLattice T))),
        constantTerm F i ν (S : Set (characterLattice T)) φ
            (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
          (ArthurRelative.tauHat hG hi ν D (S : Set (characterLattice T)) (simpleRelativeRoots i ν)
            (height hi hK hρ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x) -
              Tp) : ℂ) = 0 by simp only [hzero, tsum_zero, mul_zero]
    intro c
    rw [ArthurRelative.tauHat_eq hG hi D _ Set.Subset.rfl]
    split
    · rename_i hpos
      rw [hvanish S hS _ ⟨β, hroots ▸ hβ, hnβ, hpos β ⟨hroots ▸ hβ, hnβ⟩⟩, zero_mul]
    · simp

end Langlands.Global.ArthurTruncation.Idempotence

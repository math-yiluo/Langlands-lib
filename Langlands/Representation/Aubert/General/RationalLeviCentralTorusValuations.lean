import Langlands.Representation.Aubert.General.RationalCentralTorusValuations
import Langlands.Representation.Aubert.General.RationalSuppliedCoxeterComparisons

/-! # Root valuations on the torus points of an actual Levi center -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- Commutation with one representative fixes the point under its inverse
normalizing automorphism. -/
theorem normalizingAut_inv_point_eq_of_commute
    (t : rationalPoints T.toGrp) (n : normalizerPoints i)
    (hc : Commute (n : rationalPoints G)⁻¹ (t ≫ i.hom.hom)) :
    t ≫ (CommGroupScheme.groupHom (normalizingAut i n).inv).hom.hom = t := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono i.hom.hom).1
  have hn := (isNormalizingPoint_normalizingAut i n).inv.conj_comp
    (Over.mk (𝟙 _)) t
  rw [constantPoint_self, hc.eq, mul_inv_cancel_right] at hn
  exact hn.symm

/-- Evaluation is invariant under any representative commuting with the
ambient image of the torus point. -/
theorem torusPointCharacterValue_weylAction_of_commute
    (t : rationalPoints T.toGrp) (n : normalizerPoints i)
    (hc : Commute (n : rationalPoints G)⁻¹ (t ≫ i.hom.hom))
    (χ : characterLattice T) :
    torusPointCharacterValue t (weylAction i n χ) = torusPointCharacterValue t χ := by
  change Additive.ofMul (rationalCharacterEval
    (characterRestrict (CommGroupScheme.groupHom (normalizingAut i n).inv)
      ((rationalCharacters.equivCharacterLattice T).symm χ)) t) = _
  rw [rationalCharacterEval_characterRestrict, rationalPoints.map_apply,
    normalizingAut_inv_point_eq_of_commute i t n hc]
  rfl

variable [IsAffineHom G.X.hom]

/-- A commuting actual root-reflection representative forces its root value
to have square one. -/
theorem rootPointValue_sq_eq_one_of_commute_reflection
    (hT : IsSplitTorus T.toGrp)
    (t : rationalPoints T.toGrp) (n : normalizerPoints i)
    (hc : Commute (n : rationalPoints G)⁻¹ (t ≫ i.hom.hom))
    {α : characterLattice T}
    (hn : IsRelativeReflection i α (QuotientGroup.mk n)) :
    (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm α) t)^2 = 1 := by
  have hflip := hn.weylAction_apply_self i hT n
  have hinv := torusPointCharacterValue_weylAction_of_commute i t n hc α
  rw [hflip, map_neg] at hinv
  let x := rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm α) t
  have hxi : x⁻¹ = x := congrArg Additive.toMul hinv
  calc
    x ^ 2 = x⁻¹ * x := by
      rw [pow_two]
      exact congrArg (fun y => y * x) hxi.symm
    _ = 1 := inv_mul_cancel x

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The actual torus points whose ambient images belong to the full abstract
center of the literal standard Levi. -/
def leviCentralTorusPoints (I : Finset (SimpleRoot i ν)) :
    Subgroup (rationalPoints T.toGrp) :=
  ((Subgroup.center (levi i ν I)).map (levi i ν I).subtype).comap
    (rationalPoints.map i)

@[simp]
theorem mem_leviCentralTorusPoints_iff (I : Finset (SimpleRoot i ν))
    (t : rationalPoints T.toGrp) :
    t ∈ leviCentralTorusPoints i ν I ↔
      ∃ z : Subgroup.center (levi i ν I),
        ((z : levi i ν I) : rationalPoints G) = t ≫ i.hom.hom := by
  constructor
  · rintro ⟨z, hz, hzt⟩
    exact ⟨⟨z, hz⟩, hzt⟩
  · rintro ⟨z, hzt⟩
    exact ⟨z, z.property, hzt⟩

variable [Mono i.hom.hom.left]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) C)
  (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
  (hν : IsGenericCocharacter i ν)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)

include hN hZ cs hT hRoots hν hLength hIdent

/-- Selected simple-root values on the full abstract Levi center have square
one. The representative in the actual Levi comes from its Weyl image. -/
theorem simpleRootPointValue_sq_eq_one_of_mem_leviCentralTorusPoints
    (I : Finset (SimpleRoot i ν)) (t : rationalPoints T.toGrp)
    (ht : t ∈ leviCentralTorusPoints i ν I)
    (α : SimpleRoot i ν) (hα : α ∈ I) :
    simpleRootPointValue i ν α t ^ 2 = 1 := by
  have hw : cs.simple α ∈ pointStandardWeyl i ν I := by
    change cs.simple α ∈ (Group.RelativeWeyl.inclusion (torusPoints i) (levi i ν I)).range
    rw [hIdent I]
    exact simple_mem_standardSubgroup cs hα
  obtain ⟨n, hnI, hn⟩ := (mem_pointStandardWeyl_iff i ν I _).mp hw
  let ns := (normalizerEquiv i hN).symm n
  have hns : QuotientGroup.mk ns = (schemeCoxeterSystem i ν hN hZ cs).simple α := by
    apply (weylEquiv i hN hZ).injective
    rw [weylEquiv_mk]
    simpa only [ns, schemeCoxeterSystem_simple, MulEquiv.apply_symm_apply] using hn
  have hr := schemeCoxeterSystem_isRelativeReflection_simple
    i ν hN hZ cs hT hRoots hν hLength α
  rw [← hns] at hr
  obtain ⟨z, hz⟩ := (mem_leviCentralTorusPoints_iff i ν I t).mp ht
  have hc : Commute (ns : rationalPoints G)⁻¹ (t ≫ i.hom.hom) := by
    rw [← hz]
    exact congrArg (fun m : levi i ν I => (m : rationalPoints G))
      (Subgroup.mem_center_iff.mp z.property ⟨(n : rationalPoints G)⁻¹,
        (levi i ν I).inv_mem hnI⟩)
  exact rootPointValue_sq_eq_one_of_commute_reflection i hT t ns hc hr

variable [ValuativeRel k]

/-- The selected simple-root valuations are one on actual Levi-central
torus points. -/
theorem simpleRootPointValue_valuation_eq_one_of_mem_leviCentralTorusPoints
    (I : Finset (SimpleRoot i ν)) (t : rationalPoints T.toGrp)
    (ht : t ∈ leviCentralTorusPoints i ν I)
    (α : SimpleRoot i ν) (hα : α ∈ I) :
    ValuativeRel.valuation k (simpleRootPointValue i ν α t : k) = 1 := by
  have hsq := simpleRootPointValue_sq_eq_one_of_mem_leviCentralTorusPoints
    i ν hN hZ cs hT hRoots hν hLength hIdent I t ht α hα
  have hval := congrArg (ValuativeRel.valuation k)
    (congrArg (fun x : kˣ => (x : k)) hsq)
  simp only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] at hval
  exact (pow_eq_one_iff_of_nonneg zero_le (by decide : 2 ≠ 0)).mp hval

/-- At a maximal standard Levi, the chamber test for an actual central
torus point is exactly the strict valuation inequality for the omitted root. -/
theorem isNoncentralNegativeTorusPoint_iff_omittedRoot_lt
    [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]
    (α : SimpleRoot i ν) (t : rationalPoints T.toGrp)
    (ht : t ∈ leviCentralTorusPoints i ν (Finset.univ.erase α)) :
    IsNoncentralNegativeTorusPoint i ν t ↔
      ValuativeRel.valuation k (simpleRootPointValue i ν α t : k) < 1 := by
  have hval (β : SimpleRoot i ν) (hβα : β ≠ α) :
      ValuativeRel.valuation k (simpleRootPointValue i ν β t : k) = 1 :=
    simpleRootPointValue_valuation_eq_one_of_mem_leviCentralTorusPoints
      i ν hN hZ cs hT hRoots hν hLength hIdent _ t ht β
      (Finset.mem_erase.mpr ⟨hβα, Finset.mem_univ _⟩)
  constructor
  · rintro ⟨_, β, hβ⟩
    by_cases heq : β = α
    · simpa only [heq] using hβ
    · rw [hval β heq] at hβ
      exact False.elim (lt_irrefl _ hβ)
  · intro hα
    refine ⟨?_, α, hα⟩
    intro β
    by_cases heq : β = α
    · simpa only [heq] using hα.le
    · exact (hval β heq).le

end Langlands.Aubert.General.RationalPointFamily

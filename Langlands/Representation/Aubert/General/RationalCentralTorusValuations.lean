import Langlands.GroupScheme.Rational.RelativeReflectionProperties
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.Representation.Aubert.General.RationalEndpoint
import Langlands.Representation.Aubert.General.RationalSquareIntegrabilityStatement

/-! # Root valuations of torus points in the abstract center -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- Actual evaluation at a rational torus point, additive in the character. -/
def torusPointCharacterValue (t : rationalPoints T.toGrp) :
    characterLattice T →+ Additive kˣ where
  toFun χ := Additive.ofMul
    (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm χ) t)
  map_zero' := congrArg Additive.ofMul (rationalCharacterEval_zero t)
  map_add' χ ψ := congrArg Additive.ofMul (rationalCharacterEval_add
    ((rationalCharacters.equivCharacterLattice T).symm χ)
    ((rationalCharacters.equivCharacterLattice T).symm ψ) t)

/-- The inverse normalizing automorphism fixes a torus point whose ambient
image belongs to the full abstract center of the rational-point group. -/
theorem normalizingAut_inv_point_eq_of_mem_center
    (t : rationalPoints T.toGrp)
    (ht : t ≫ i.hom.hom ∈ Subgroup.center (rationalPoints G))
    (n : normalizerPoints i) :
    t ≫ (CommGroupScheme.groupHom (normalizingAut i n).inv).hom.hom = t := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono i.hom.hom).1
  have hn := (isNormalizingPoint_normalizingAut i n).inv.conj_comp
    (Over.mk (𝟙 _)) t
  have hc : Commute (n : rationalPoints G)⁻¹ (t ≫ i.hom.hom) :=
    Subgroup.mem_center_iff.mp ht _
  rw [constantPoint_self, hc.eq, mul_inv_cancel_right] at hn
  exact hn.symm

/-- Character evaluation at such a point is invariant under every actual
normalizer representative. -/
theorem torusPointCharacterValue_weylAction
    (t : rationalPoints T.toGrp)
    (ht : t ≫ i.hom.hom ∈ Subgroup.center (rationalPoints G))
    (n : normalizerPoints i) (χ : characterLattice T) :
    torusPointCharacterValue t (weylAction i n χ) = torusPointCharacterValue t χ := by
  change Additive.ofMul (rationalCharacterEval
    (characterRestrict (CommGroupScheme.groupHom (normalizingAut i n).inv)
      ((rationalCharacters.equivCharacterLattice T).symm χ)) t) = _
  rw [rationalCharacterEval_characterRestrict, rationalPoints.map_apply,
    normalizingAut_inv_point_eq_of_mem_center i t ht n]
  rfl

variable [IsAffineHom G.X.hom]

/-- A root value at an abstract-central torus point has square one. Only the
actual root-system realization and splitness are used. -/
theorem rootPointValue_sq_eq_one_of_mem_center
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (t : rationalPoints T.toGrp)
    (ht : t ≫ i.hom.hom ∈ Subgroup.center (rationalPoints G))
    {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm α) t)^2 = 1 := by
  obtain ⟨w, hw⟩ := hRoots.exists_isRelativeReflection hα
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  have hflip := hw.weylAction_apply_self i hT n
  have hinv := torusPointCharacterValue_weylAction i t ht n α
  rw [hflip, map_neg] at hinv
  let x := rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm α) t
  have hxi : x⁻¹ = x := congrArg Additive.toMul hinv
  calc
    x ^ 2 = x⁻¹ * x := by
      rw [pow_two]
      exact congrArg (fun y => y * x) hxi.symm
    _ = 1 := inv_mul_cancel x

/-- Consequently every actual root value has valuation one, with no need to
identify the abstract center with the points of the scheme center. -/
theorem rootPointValue_valuation_eq_one_of_mem_center [ValuativeRel k]
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (t : rationalPoints T.toGrp)
    (ht : t ≫ i.hom.hom ∈ Subgroup.center (rationalPoints G))
    {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    ValuativeRel.valuation k
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm α) t : k) = 1 := by
  have hsq := rootPointValue_sq_eq_one_of_mem_center i hT hRoots t ht hα
  have hsqk := congrArg (fun x : kˣ => (x : k)) hsq
  have hval := congrArg (ValuativeRel.valuation k) hsqk
  simp only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] at hval
  exact (pow_eq_one_iff_of_nonneg zero_le (by decide : 2 ≠ 0)).mp hval

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)

/-- A torus point mapping into the full abstract ambient center fails the
noncentral-negative chamber test. -/
theorem not_isNoncentralNegativeTorusPoint_of_mem_center
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (t : RationalPoint k T.X)
    (ht : t ≫ i.hom.hom ∈ Subgroup.center (RationalPoint k G.X)) :
    ¬ IsNoncentralNegativeTorusPoint i ν t := by
  rintro ⟨_, α, hα⟩
  have hv := rootPointValue_valuation_eq_one_of_mem_center i hT hRoots t ht α.property.1.1
  change ValuativeRel.valuation k (simpleRootPointValue i ν α t : k) = 1 at hv
  rw [hv] at hα
  exact (lt_irrefl _ hα)

/-- The original rational structural premises exclude noncentral negative
tests on the full-index Levi's actual abstract center. -/
theorem not_isNoncentralNegativeTorusPoint_of_fullIndex_center
    [Fintype (SimpleRoot i ν)]
    (hStandard : StandardCocharacterStatement.{u}) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hRoots : HasRelativeRootSystem i)
    (t : RationalPoint k T.X) (z : Subgroup.center (levi i ν Finset.univ))
    (hz : ((z : levi i ν Finset.univ) : RationalPoint k G.X) = t ≫ i.hom.hom) :
    ¬ IsNoncentralNegativeTorusPoint i ν t := by
  apply not_isNoncentralNegativeTorusPoint_of_mem_center i ν hi.isSplitSubtorus.1 hRoots t
  rw [← hz]
  apply Subgroup.mem_center_iff.mpr
  intro x
  have hx : x ∈ levi i ν Finset.univ := by
    rw [levi_univ_eq_top i ν hStandard hG hi hν]
    trivial
  exact congrArg (fun m : levi i ν Finset.univ => (m : RationalPoint k G.X))
    (Subgroup.mem_center_iff.mp z.property ⟨x, hx⟩)

end Langlands.Aubert.General.RationalPointFamily

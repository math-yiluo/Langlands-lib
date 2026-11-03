import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.AbelianScheme.Torsion
import Mathlib.GroupTheory.OrderOfElement

/-! # Torsion bounds for intersections with split tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section ArbitraryBase

variable {S : Scheme.{u}} {G D A : GroupScheme S}

/-- The characters of a split torus detect the identity on every test scheme. -/
theorem IsSplitTorus.eq_one_of_characterEval_eq_one (hA : IsSplitTorus A)
    {T : Over S} {x : T ⟶ A.X}
    (hx : ∀ χ : rationalCharacters A, characterEval χ T x = 1) : x = 1 := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hA
  apply ((isoPointsEquiv e T).trans (splitTorus.pointsEquiv I T)).injective
  funext a
  have ha := hx (Additive.ofMul (e.hom ≫ Pi.π (fun _ : I => (Gm S).toGrp) a))
  change Gm.pointsEquiv S T
    (x ≫ (e.hom ≫ Pi.π (fun _ : I => (Gm S).toGrp) a).hom.hom) = 1 at ha
  simpa only [MulEquiv.trans_apply, isoPointsEquiv_apply, splitTorus.pointsEquiv_apply,
    map_one, Pi.one_apply, characterEval_apply, Grp.comp_hom_hom, Category.assoc] using ha

/-- A uniform restriction multiple bounds the full split-torus intersection with an actual
derived subgroup, on all test schemes. -/
theorem IsDerivedSubgroup.pow_eq_one_of_characterRestrict_nsmul {d : D ⟶ G}
    (hd : IsDerivedSubgroup d) (i : A ⟶ G) (hA : IsSplitTorus A) (n : ℕ)
    (hn : ∀ χ : rationalCharacters A, n • χ ∈ (characterRestrict i).range)
    {T : Over S} {x : T ⟶ A.X}
    (hx : x ≫ i.hom.hom ∈ (SubgroupFunctor.range d).carrier T) : x ^ n = 1 := by
  apply hA.eq_one_of_characterEval_eq_one
  intro χ
  obtain ⟨ψ, hψ⟩ := hn χ
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
  rw [map_pow, ← zpow_natCast, ← characterEval_zsmul, natCast_zsmul, ← hψ,
    characterEval_characterRestrict, ← hy, ← characterEval_characterRestrict,
    hd.characterRestrict_eq_zero, characterEval_zero]

variable {B : CommGroupScheme S}

/-- The entire preimage of the derived subgroup in a split torus lies in actual torsion. -/
theorem IsDerivedSubgroup.comap_range_le_torsion_of_characterRestrict_nsmul
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) (i : B.toGrp ⟶ G)
    (hB : IsSplitTorus B.toGrp) (n : ℕ)
    (hn : ∀ χ : rationalCharacters B.toGrp, n • χ ∈ (characterRestrict i).range) :
    (SubgroupFunctor.range d).comap i ≤ SubgroupFunctor.range (torsionι B.toGrp (n : ℤ)) := by
  intro T x hx
  apply (mem_range_kernelι_iff (multiplication B.toGrp (n : ℤ)) x).mpr
  rw [points_multiplication, zpow_natCast]
  exact hd.pow_eq_one_of_characterRestrict_nsmul i hB n hn hx

/-- Factor a homomorphism into a split torus through actual torsion when its composite lands
in an actual derived subgroup and every character has the given restriction multiple. -/
def IsDerivedSubgroup.torusIntersectionTorsionFactor {d : D ⟶ G}
    (hd : IsDerivedSubgroup d) (i : B.toGrp ⟶ G) (hB : IsSplitTorus B.toGrp) (n : ℕ)
    (hn : ∀ χ : rationalCharacters B.toGrp, n • χ ∈ (characterRestrict i).range)
    {C : GroupScheme S} (c : C ⟶ B.toGrp)
    (hc : SubgroupFunctor.range c ≤ (SubgroupFunctor.range d).comap i) :
    C ⟶ torsion B.toGrp (n : ℤ) :=
  (show (SubgroupFunctor.range (torsionι B.toGrp (n : ℤ))).IsRepresentedBy
      (torsionι B.toGrp (n : ℤ)) from ⟨inferInstance, rfl⟩).factorHom c
    (hc.trans (hd.comap_range_le_torsion_of_characterRestrict_nsmul i hB n hn))

theorem IsDerivedSubgroup.torusIntersectionTorsionFactor_comp {d : D ⟶ G}
    (hd : IsDerivedSubgroup d) (i : B.toGrp ⟶ G) (hB : IsSplitTorus B.toGrp) (n : ℕ)
    (hn : ∀ χ : rationalCharacters B.toGrp, n • χ ∈ (characterRestrict i).range)
    {C : GroupScheme S} (c : C ⟶ B.toGrp)
    (hc : SubgroupFunctor.range c ≤ (SubgroupFunctor.range d).comap i) :
    hd.torusIntersectionTorsionFactor i hB n hn c hc ≫ torsionι B.toGrp (n : ℤ) = c :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

end ArbitraryBase

section FiniteIndex

variable {S : Scheme.{u}} {G D : GroupScheme S} {B : CommGroupScheme S}

/-- A finite-index character restriction gives the explicit, nonzero index as a uniform
torsion bound for the full intersection with an actual derived subgroup. -/
theorem IsDerivedSubgroup.exists_comap_range_le_torsion_of_finiteIndex
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) (i : B.toGrp ⟶ G)
    (hB : IsSplitTorus B.toGrp) (hi : (characterRestrict i).range.FiniteIndex) :
    ∃ n : ℕ, n ≠ 0 ∧
      (SubgroupFunctor.range d).comap i ≤ SubgroupFunctor.range (torsionι B.toGrp (n : ℤ)) :=
  ⟨(characterRestrict i).range.index, hi.index_ne_zero,
    hd.comap_range_le_torsion_of_characterRestrict_nsmul i hB _
      ((characterRestrict i).range.nsmul_index_mem)⟩

end FiniteIndex

section Field

variable {k : Type u} [Field k] {G D : GroupScheme (Spec (CommRingCat.of k))}
  {B : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A central split torus in an affine finite-type field group has uniformly torsion
intersection with its actual derived subgroup, including points over nonreduced tests. -/
theorem IsDerivedSubgroup.exists_comap_range_le_torsion_of_isCentralSplitTorus
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (i : B.toGrp ⟶ G) (hi : IsCentralSplitTorus i) :
    ∃ n : ℕ, n ≠ 0 ∧
      (SubgroupFunctor.range d).comap i ≤ SubgroupFunctor.range (torsionι B.toGrp (n : ℤ)) :=
  hd.exists_comap_range_le_torsion_of_finiteIndex i hi.1.1
    (CharacterRestrictionFiniteIndex.finiteIndex_range_characterRestrict i hi)

end Field

end Langlands.GroupScheme

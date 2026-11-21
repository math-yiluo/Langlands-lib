import Langlands.Global.AdelicWeylFamilyCounting
import Langlands.Group.RelativeWeylSolomonProof
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.SimpleReflectionConjugacy

/-! # Standard Weyl representatives for associated inducing parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints
  Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

section Representative

variable {F : Type u} [Field F]
  {G P M Q M' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (nu : cocharacterLattice T)
  (I J : Finset (SimpleRoot i nu))
  {p : P ⟶ G} {l : M ⟶ P} {q : Q ⟶ G} {l' : M' ⟶ Q}

local notation "Point" => (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
local notation "Levi" => fun K => standardLeviPoints i nu (rootSet i nu K)
local notation "Weyl" => relativeWeylGroup i
local notation "Wsub" => fun K => standardRelativeWeylGroup i nu (rootSet i nu K)

private theorem conj_inv_mem_sourceLevi
    (hI : SubgroupFunctor.range (l ≫ p) = standardLevi i nu (rootSet i nu I))
    (hJ : SubgroupFunctor.range (l' ≫ q) = standardLevi i nu (rootSet i nu J))
    {n : Point} {c : M' ⟶ M} (hn : IsWeylConjugation p l q l' n c)
    {m : Point} (hm : m ∈ (Levi) J) :
    n⁻¹ * m * n ∈ (Levi) I := by
  change m ∈ (standardLevi i nu (rootSet i nu J)).carrier _ at hm
  rw [← hJ] at hm
  obtain ⟨x, hx⟩ := hm
  let y : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ M'.X := x
  have hy : y ≫ (l' ≫ q).hom.hom = m := hx
  change n⁻¹ * m * n ∈ (standardLevi i nu (rootSet i nu I)).carrier _
  rw [← hI]
  refine ⟨y ≫ c.hom.hom, ?_⟩
  have h := congrArg (fun e : M' ⟶ G => y ≫ e.hom.hom) hn.comp_eq
  simp only [Grp.comp_hom_hom] at h
  refine h.trans ?_
  calc
    _ = (y ≫ (l' ≫ q).hom.hom) ≫ (G.innerIso n).inv.hom.hom := by
      simp only [Grp.comp_hom_hom, Category.assoc]
    _ = m ≫ (G.innerIso n).inv.hom.hom := by rw [hy]
    _ = _ := by rw [← innerIso_inv_hom, comp_innerIso_hom, constantPoint_self, inv_inv]

private theorem conj_inv_mem_sourceWeyl
    (hI : SubgroupFunctor.range (l ≫ p) = standardLevi i nu (rootSet i nu I))
    (hJ : SubgroupFunctor.range (l' ≫ q) = standardLevi i nu (rootSet i nu J))
    {n : normalizerPoints i} {c : M' ⟶ M} (hn : IsWeylConjugation p l q l' n.val c)
    {m : Weyl} (hm : m ∈ (Wsub) J) :
    (QuotientGroup.mk n : Weyl)⁻¹ * m * QuotientGroup.mk n ∈ (Wsub) I := by
  obtain ⟨m', hm', rfl⟩ := (mem_standardRelativeWeylGroup_iff i nu).mp hm
  refine (mem_standardRelativeWeylGroup_iff i nu).mpr ⟨n⁻¹ * m' * n, ?_, rfl⟩
  exact conj_inv_mem_sourceLevi i nu I J hI hJ hn hm'

variable [Mono i.hom.hom.left]

private theorem maps_roots_of_minimal {C : CoxeterMatrix (SimpleRoot i nu)}
    {cs : CoxeterSystem C Weyl} [Fintype (SimpleRoot i nu)]
    (hcs : IsRelativeWeylCoxeterRealization i nu cs)
    {w : Weyl} (hw : IsMinimal cs J I w)
    (hconj : ∀ x ∈ (Wsub) I, w * x * w⁻¹ ∈ (Wsub) J) :
    ∀ alpha ∈ rootSet i nu I, schemeWeylCharacterAction i w alpha ∈ rootSet i nu J := by
  rintro _ ⟨a, ha, rfl⟩
  have ha' : cs.simple a ∈ (Wsub) I := by
    change cs.simple a ∈ standardRelativeWeylGroup i nu (rootSet i nu I)
    rw [← hcs.2.2.2.2 I]
    exact simple_mem_standardSubgroup cs ha
  have hmem : w * cs.simple a * w⁻¹ ∈ standardSubgroup cs J :=
    (hcs.2.2.2.2 J).symm ▸ hconj _ ha'
  obtain ⟨b, hb, hab⟩ := exists_conj_simple_eq_of_isMinimal cs hw ha hmem
  have hpos := (hcs.2.2.1 w a).mp ((((minimalityLengthCriterion_proof cs) J I w).mp hw).2 a ha)
  rw [hcs.root_eq_of_conj_simple w a b hpos hab]
  exact (val_mem_rootSet i nu J b).mpr hb

/-- A rational right factor in the source Levi makes the normalizer
representative carry the two actual simple-root subsets to one another. -/
theorem exists_rightLevi_standardWeylRepresentative
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
    (hI : SubgroupFunctor.range (l ≫ p) = standardLevi i nu (rootSet i nu I))
    (hJ : SubgroupFunctor.range (l' ≫ q) = standardLevi i nu (rootSet i nu J))
    (n : normalizerPoints i) (c : M' ⟶ M) (hc : IsWeylConjugation p l q l' n.val c) :
    ∃ (z : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ M.X) (n' : normalizerPoints i),
      n'.val = n.val * (z ≫ (l ≫ p).hom.hom) ∧
      (∀ alpha ∈ rootSet i nu I,
        schemeWeylCharacterAction i (QuotientGroup.mk n') alpha ∈ rootSet i nu J) ∧
      ∀ alpha ∈ rootSet i nu J,
        schemeWeylCharacterAction i (QuotientGroup.mk n' : Weyl)⁻¹ alpha ∈ rootSet i nu I := by
  classical
  obtain ⟨_, hfin, C, cs, hcs⟩ := relativeWeylCoxeter F G hG T i hi nu hnu
  let : Fintype (SimpleRoot i nu) := Fintype.ofFinite _
  let w : Weyl := QuotientGroup.mk n
  obtain ⟨v, ⟨a, ha, b, hb, hv⟩, hmin⟩ := exists_minimal_in_doubleCoset_unrestricted cs J I w
  obtain ⟨a', ha', hqa⟩ := (mem_standardRelativeWeylGroup_iff i nu).mp
    (hcs.2.2.2.2 J ▸ ha)
  obtain ⟨b', hb', hqb⟩ := (mem_standardRelativeWeylGroup_iff i nu).mp
    (hcs.2.2.2.2 I ▸ hb)
  let zn : normalizerPoints i := n⁻¹ * a' * n * b'
  have hza : (n⁻¹ * a' * n : normalizerPoints i).val ∈ (Levi) I :=
    conj_inv_mem_sourceLevi i nu I J hI hJ hc ha'
  have hzn : zn.val ∈ (Levi) I := ((Levi) I).mul_mem hza hb'
  have hzMem := hzn
  change zn.val ∈ (standardLevi i nu (rootSet i nu I)).carrier _ at hzMem
  rw [← hI] at hzMem
  obtain ⟨z, hz⟩ := hzMem
  let n' := n * zn
  have hn' : n'.val = n.val * (z ≫ (l ≫ p).hom.hom) := congrArg (n.val * ·) hz.symm
  have hnq : (QuotientGroup.mk n' : Weyl) = v := by
    rw [hv, ← hqa, ← hqb]
    change QuotientGroup.mk n' = QuotientGroup.mk (a' * n * b')
    congr 1
    dsimp only [n', zn]
    group
  have hSub : (QuotientGroup.mk zn : Weyl) ∈ (Wsub) I :=
    (mem_standardRelativeWeylGroup_iff i nu).mpr ⟨zn, hzn, rfl⟩
  obtain ⟨c', _, _, hc'⟩ := hc.symm
  have hConj (x : Weyl) (hx : x ∈ (Wsub) I) : w * x * w⁻¹ ∈ (Wsub) J := by
    simpa only [QuotientGroup.mk_inv, inv_inv] using
      conj_inv_mem_sourceWeyl i nu J I hJ hI (n := n⁻¹) hc' hx
  have hConjV (x : Weyl) (hx : x ∈ (Wsub) I) : v * x * v⁻¹ ∈ (Wsub) J := by
    have hm := hConj _ (((Wsub) I).mul_mem (((Wsub) I).mul_mem hSub hx) (((Wsub) I).inv_mem hSub))
    rw [← hnq]
    change (w * QuotientGroup.mk zn) * x * (w * QuotientGroup.mk zn)⁻¹ ∈ (Wsub) J
    simpa only [mul_inv_rev, mul_assoc] using hm
  have hConjInv (x : Weyl) (hx : x ∈ (Wsub) J) : v⁻¹ * x * v ∈ (Wsub) I := by
    have hm := conj_inv_mem_sourceWeyl i nu I J hI hJ hc hx
    have hh := ((Wsub) I).mul_mem (((Wsub) I).mul_mem (((Wsub) I).inv_mem hSub) hm) hSub
    rw [← hnq]
    change (w * QuotientGroup.mk zn)⁻¹ * x * (w * QuotientGroup.mk zn) ∈ (Wsub) I
    simpa only [mul_inv_rev, mul_assoc] using hh
  refine ⟨z, n', hn', ?_, ?_⟩
  · rw [hnq]
    exact maps_roots_of_minimal i nu I J hcs hmin hConjV
  · rw [hnq]
    apply maps_roots_of_minimal i nu J I hcs (isMinimal_inv cs hmin)
    simpa only [inv_inv] using hConjInv

end Representative

/-- A source Levi adjustment of an associated parabolic Weyl representative
transports the standard Levi simple-root sets in both directions. -/
def StandardWeylRepresentativeStatement : Prop :=
  ∀ (F : Type u) [Field F] (G P M Q M' : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (nu : cocharacterLattice T)
    (I J : Finset (SimpleRoot i nu)) (p : P ⟶ G) (l : M ⟶ P) (q : Q ⟶ G) (l' : M' ⟶ Q),
    IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i nu →
    SubgroupFunctor.range (l ≫ p) = standardLevi i nu (rootSet i nu I) →
    SubgroupFunctor.range (l' ≫ q) = standardLevi i nu (rootSet i nu J) →
    ∀ (n : normalizerPoints i) (c : M' ⟶ M), IsWeylConjugation p l q l' n.val c →
      ∃ (z : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ M.X) (n' : normalizerPoints i),
        n'.val = n.val * (z ≫ (l ≫ p).hom.hom) ∧
        (∀ alpha ∈ rootSet i nu I,
          schemeWeylCharacterAction i (QuotientGroup.mk n') alpha ∈ rootSet i nu J) ∧
        ∀ alpha ∈ rootSet i nu J,
          schemeWeylCharacterAction i (QuotientGroup.mk n' : relativeWeylGroup i)⁻¹ alpha ∈
            rootSet i nu I

theorem standardWeylRepresentative : StandardWeylRepresentativeStatement.{u} := by
  intro F _ G P M Q M' _ T i _ nu I J p l q l' hG hi hnu hI hJ n c hc
  exact exists_rightLevi_standardWeylRepresentative i nu I J hG hi hnu hI hJ n c hc

end Langlands.Global

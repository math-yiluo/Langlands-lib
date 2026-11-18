import Langlands.GroupScheme.Reductive.TitsAdditivity
import Langlands.GroupScheme.Reductive.StarFixedDominantDecomposition
import Langlands.Algebra.BrauerGroup

/-! # The Tits obstruction on star-fixed weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation Langlands.Brauer

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G) [IsGalois k K]

/-- The dominant Tits class only depends on the weight. -/
theorem dominantTitsClass_congr {a b : characterLattice d.toSplitPinning.torus} (h : a = b)
    (ha : d.toSplitPinning.IsDominantWeight a) (hfa : d.IsStarFixedWeight a)
    (hb : d.toSplitPinning.IsDominantWeight b) (hfb : d.IsStarFixedWeight b) :
    d.dominantTitsClass a ha hfa = d.dominantTitsClass b hb hfb := by
  subst h
  rfl

/-- The dominant Tits class is additive (Tits 1971, Corollary 3.5). -/
theorem dominantTitsClass_add {a b : characterLattice d.toSplitPinning.torus}
    (ha : d.toSplitPinning.IsDominantWeight a) (hb : d.toSplitPinning.IsDominantWeight b)
    (hfa : d.IsStarFixedWeight a) (hfb : d.IsStarFixedWeight b) :
    d.dominantTitsClass (a + b) (d.isDominantWeight_add ha hb)
        (d.isStarFixedWeight_add hfa hfb) =
      d.dominantTitsClass a ha hfa + d.dominantTitsClass b hb hfb := by
  obtain ⟨n₁, ρ₁, h₁⟩ := (splitHighestWeightClassification K _ d.toSplitPinning).1 a ha
  obtain ⟨n₂, ρ₂, h₂⟩ := (splitHighestWeightClassification K _ d.toSplitPinning).1 b hb
  obtain ⟨r, ρ, hρ⟩ := (splitHighestWeightClassification K _ d.toSplitPinning).1 (a + b) (d.isDominantWeight_add ha hb)
  rw [d.dominantTitsClass_eq _ _ hρ, d.dominantTitsClass_eq _ _ h₁,
    d.dominantTitsClass_eq _ _ h₂]
  change classOf _ = classOf _ + classOf _
  rw [← classOf_tensor]
  exact (classOf_eq_iff _ _).mpr (d.titsCSAOf_add_isBrauerEquivalent h₁ h₂ hρ hfa hfb)

omit [LocallyOfFiniteType G.X.hom] [IsGalois k K] in
theorem isDominantWeight_zero : d.toSplitPinning.IsDominantWeight 0 := fun a => by
  rw [map_zero, LinearMap.zero_apply]

omit [IsGalois k K] in
theorem isStarFixedWeight_zero : d.IsStarFixedWeight 0 := fun _ => map_zero _

/-- The dominant Tits class of the zero weight vanishes. -/
theorem dominantTitsClass_zero :
    d.dominantTitsClass 0 d.isDominantWeight_zero d.isStarFixedWeight_zero = 0 := by
  have h := d.dominantTitsClass_add d.isDominantWeight_zero d.isDominantWeight_zero
    d.isStarFixedWeight_zero d.isStarFixedWeight_zero
  rw [d.dominantTitsClass_congr (add_zero 0) _ _ d.isDominantWeight_zero
    d.isStarFixedWeight_zero] at h
  exact left_eq_add.mp h

variable (hspan : d.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)

/-- The Tits obstruction of a star-fixed weight `λ`: the difference of the dominant Tits classes
of `dominantPart λ` and `dominantPart λ - λ`. -/
def titsObstructionValue (lam : characterLattice d.toSplitPinning.torus)
    (hfix : d.IsStarFixedWeight lam) : BrauerGroup.{u, u} k :=
  d.dominantTitsClass (d.dominantPart hspan lam) (d.isDominantWeight_dominantPart hspan lam)
      (d.isStarFixedWeight_dominantPart hspan hfix) -
    d.dominantTitsClass (d.dominantPart hspan lam - lam)
      (d.isDominantWeight_dominantPart_sub hspan lam)
      (d.isStarFixedWeight_sub (d.isStarFixedWeight_dominantPart hspan hfix) hfix)

/-- Independence of the decomposition: for any expression `λ = a - b` with `a`, `b` dominant and
star-fixed, the obstruction is the difference of the dominant Tits classes. -/
theorem titsObstructionValue_eq_sub {lam a b : characterLattice d.toSplitPinning.torus}
    (hfix : d.IsStarFixedWeight lam)
    (ha : d.toSplitPinning.IsDominantWeight a) (hb : d.toSplitPinning.IsDominantWeight b)
    (hfa : d.IsStarFixedWeight a) (hfb : d.IsStarFixedWeight b) (h : lam = a - b) :
    d.titsObstructionValue hspan lam hfix =
      d.dominantTitsClass a ha hfa - d.dominantTitsClass b hb hfb := by
  rw [titsObstructionValue, sub_eq_sub_iff_add_eq_add, ← d.dominantTitsClass_add,
    ← d.dominantTitsClass_add]
  exact d.dominantTitsClass_congr (by rw [h]; abel) _ _ _ _

/-- On dominant star-fixed weights the obstruction is the dominant Tits class. -/
theorem titsObstructionValue_of_isDominantWeight {lam : characterLattice d.toSplitPinning.torus}
    (hfix : d.IsStarFixedWeight lam) (hdom : d.toSplitPinning.IsDominantWeight lam) :
    d.titsObstructionValue hspan lam hfix = d.dominantTitsClass lam hdom hfix := by
  rw [d.titsObstructionValue_eq_sub hspan hfix hdom d.isDominantWeight_zero hfix
    d.isStarFixedWeight_zero (sub_zero lam).symm, d.dominantTitsClass_zero, sub_zero]

/-- On a dominant star-fixed weight the obstruction is the class of the Tits algebra of any
representation of that highest weight. -/
theorem titsObstructionValue_eq_classOf {lam : characterLattice d.toSplitPinning.torus}
    (hfix : d.IsStarFixedWeight lam) (hdom : d.toSplitPinning.IsDominantWeight lam) {n : ℕ}
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n)}
    (hρ : d.toSplitPinning.IsHighestWeight ρ lam) :
    d.titsObstructionValue hspan lam hfix = classOf (d.titsCSAOf hρ hfix) := by
  rw [d.titsObstructionValue_of_isDominantWeight hspan hfix hdom,
    d.dominantTitsClass_eq hdom hfix hρ]
  rfl

/-- The obstruction is additive. -/
theorem titsObstructionValue_add {lam mu : characterLattice d.toSplitPinning.torus}
    (hl : d.IsStarFixedWeight lam) (hm : d.IsStarFixedWeight mu) :
    d.titsObstructionValue hspan (lam + mu) (d.isStarFixedWeight_add hl hm) =
      d.titsObstructionValue hspan lam hl + d.titsObstructionValue hspan mu hm := by
  have hpl := d.isStarFixedWeight_dominantPart hspan hl
  have hpm := d.isStarFixedWeight_dominantPart hspan hm
  rw [d.titsObstructionValue_eq_sub hspan (d.isStarFixedWeight_add hl hm)
    (d.isDominantWeight_add (d.isDominantWeight_dominantPart hspan lam)
      (d.isDominantWeight_dominantPart hspan mu))
    (d.isDominantWeight_add (d.isDominantWeight_dominantPart_sub hspan lam)
      (d.isDominantWeight_dominantPart_sub hspan mu))
    (d.isStarFixedWeight_add hpl hpm)
    (d.isStarFixedWeight_add (d.isStarFixedWeight_sub hpl hl) (d.isStarFixedWeight_sub hpm hm))
    (by abel),
    d.dominantTitsClass_add (d.isDominantWeight_dominantPart hspan lam)
      (d.isDominantWeight_dominantPart hspan mu) hpl hpm,
    d.dominantTitsClass_add (d.isDominantWeight_dominantPart_sub hspan lam)
      (d.isDominantWeight_dominantPart_sub hspan mu) (d.isStarFixedWeight_sub hpl hl)
      (d.isStarFixedWeight_sub hpm hm), titsObstructionValue, titsObstructionValue]
  abel

/-- The Tits obstruction as an additive map on any subgroup of star-fixed weights. -/
def titsObstructionOn (S : AddSubgroup (characterLattice d.toSplitPinning.torus))
    (hS : ∀ x ∈ S, d.IsStarFixedWeight x) : S →+ BrauerGroup.{u, u} k where
  toFun x := d.titsObstructionValue hspan x.1 (hS x.1 x.2)
  map_zero' := by
    change d.titsObstructionValue hspan 0 _ = 0
    rw [d.titsObstructionValue_of_isDominantWeight hspan _ d.isDominantWeight_zero,
      d.dominantTitsClass_zero]
  map_add' x y := d.titsObstructionValue_add hspan (hS x.1 x.2) (hS y.1 y.2)

end Langlands.GroupScheme.GaloisPinningData

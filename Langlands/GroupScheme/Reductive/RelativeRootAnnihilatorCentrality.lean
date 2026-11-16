import Langlands.GroupScheme.Reductive.LocalSplitFlatBigCell
import Langlands.GroupScheme.Reductive.LocalSplitClosedResidueCellIsomorphism
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange

/-! # Centrality of torus points annihilating the coordinate roots -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {J : Type u} (P : RootDatum J (I → ℤ) (I → ℤ))

/-- Every root character has value one on this actual relative torus point. -/
def RootCharactersOne {Z : Over (Spec (CommRingCat.of R))}
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) : Prop :=
  ∀ α, VectorGroup.charValue (splitTorus.exponentCharacter _ I (P.root α)) Z t = 1

variable {P}

theorem RootCharactersOne.comp {Z W : Over (Spec (CommRingCat.of R))}
    {t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X}
    (ht : RootCharactersOne P t) (a : W ⟶ Z) :
    RootCharactersOne P (a ≫ t) := by
  intro α
  rw [VectorGroup.charValue_comp, ht α, map_one]

section LocalBase

variable [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}

/-- Big-cell generation detects trivial conjugation over a local test ring
with separably closed residue field, retaining all nilpotents. -/
theorem commute_of_rootCharacters_one_closedResidue
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base)
    {A : Type u} [CommRing A] [IsLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (t : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (ht : RootCharactersOne P t) (g : Over.mk s ⟶ G.X) :
    Commute (t ≫ i.hom.hom) g := by
  classical
  let : Finite J := hP.finite
  let neg := (Finite.equivFin {α // ¬ b.IsPos α}).symm
  let pos := (Finite.equivFin {α // b.IsPos α}).symm
  let fam := LocalSplitBigCell.rootFamily hG hmax hP
  let : IsOpenImmersion
      (cellMap i fam (fun k => (neg k : J)) (fun k => (pos k : J))).left :=
    LocalSplitBigCell.isOpenImmersion_rootFamily hG hmax hP b neg pos
  let Ψ := (MulAut.conj (t ≫ i.hom.hom)).toMonoidHom
  let Φ := MonoidHom.id (Over.mk s ⟶ G.X)
  have hΨi : ∀ z : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
      Ψ (z ≫ i.hom.hom) = z ≫ i.hom.hom := by
    intro z
    change (t ≫ i.hom.hom) * (z ≫ i.hom.hom) * (t ≫ i.hom.hom)⁻¹ = _
    have hc : (t ≫ i.hom.hom) * (z ≫ i.hom.hom) =
        (z ≫ i.hom.hom) * (t ≫ i.hom.hom) := by
      rw [← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
    rw [hc, mul_inv_cancel_right]
  have hΨfam : ∀ α c, Ψ (rootPoint (fam α) _ c) = rootPoint (fam α) _ c := by
    intro α c
    change (t ≫ i.hom.hom) * rootPoint (fam α) _ c * (t ≫ i.hom.hom)⁻¹ = _
    rw [(LocalSplitBigCell.isRootParametrization_rootFamily hG hmax hP α).equivariant,
      ht α, one_mul]
  have heq := pointHom_ext_of_matches hG
    (fun k => (neg k : J)) (fun k => (pos k : J)) s Ψ Φ
    hΨi hΨfam (fun _ => rfl) (fun _ _ => rfl)
  have hg := DFunLike.congr_fun heq g
  change (t ≫ i.hom.hom) * g * (t ≫ i.hom.hom)⁻¹ = g at hg
  exact (mul_inv_eq_iff_eq_mul).mp hg

/-- Over every local base ring, the full root annihilator is central on all
relative scheme tests, without a reducedness or residue-characteristic condition. -/
theorem mem_center_of_rootCharacters_one_local
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base)
    {Z : Over (Spec (CommRingCat.of R))}
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (ht : RootCharactersOne P t) :
    t ≫ i.hom.hom ∈ (center G).carrier Z := by
  intro W a g
  change (a ≫ t ≫ i.hom.hom) * g = g * (a ≫ t ≫ i.hom.hom)
  apply Over.OverMorphism.ext
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply CellGluing.hom_ext_of_closedResidueLocalRingPoints
  intro A _ _ _ q
  let s := q ≫ W.hom
  let r : Over.mk s ⟶ W := Over.homMk q rfl
  have hc := commute_of_rootCharacters_one_closedResidue hG hmax hP b s
    (r ≫ a ≫ t) (ht.comp (r ≫ a)) (r ≫ g)
  have he : r ≫ ((a ≫ t ≫ i.hom.hom) * g) =
      r ≫ (g * (a ≫ t ≫ i.hom.hom)) := by
    simpa only [MonObj.comp_mul, Category.assoc] using hc.eq
  exact congrArg CommaMorphism.left he

end LocalBase

end Langlands.GroupScheme

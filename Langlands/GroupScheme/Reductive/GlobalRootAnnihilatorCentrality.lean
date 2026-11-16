import Langlands.GroupScheme.Reductive.RelativeRootAnnihilatorCentrality
import Langlands.GroupScheme.Reductive.LocalSplitRootBaseChange
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Full centrality from simple-root character equations over arbitrary bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- The actual simple-root characters all take value one. -/
def SimpleRootCharactersOne (b : P.Base)
    {Z : Over (Spec (CommRingCat.of R))}
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) : Prop :=
  ∀ α ∈ b.support,
    VectorGroup.charValue (splitTorus.exponentCharacter _ I (P.root α)) Z t = 1

/-- The root lattice is spanned integrally by the simple roots, so their
character equations imply the equations for every root. -/
theorem rootCharactersOne_of_simple {b : P.Base}
    {Z : Over (Spec (CommRingCat.of R))}
    {t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X}
    (ht : SimpleRootCharactersOne b t) : RootCharactersOne P t := by
  let E := splitTorus.exponentValue I (splitTorus.pointsEquiv I Z t)
  let L := E.toAdditiveRight.toIntLinearMap
  have hspan : Submodule.span ℤ (P.root '' b.support) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨α, hα, rfl⟩
    have hαone := ht α hα
    rw [Corepresented.charValue_exponentCharacter] at hαone
    have hunit : E (Multiplicative.ofAdd (P.root α)) = 1 :=
      Units.ext hαone
    exact congrArg Additive.ofMul hunit
  intro α
  rw [Corepresented.charValue_exponentCharacter]
  have h := hspan (b.root_mem_span_int α)
  have hunit : E (Multiplicative.ofAdd (P.root α)) = 1 :=
    congrArg Additive.toMul h
  exact congrArg Units.val hunit

section ArbitraryBase

variable {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}

private theorem commute_on_algebra_test
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base)
    (A : Type u) [CommRing A] [IsLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] [Algebra R A]
    (t : (Over.map (algebraBaseMap R A)).obj (Over.mk (𝟙 (Spec (CommRingCat.of A)))) ⟶
      (splitTorus (Spec (CommRingCat.of R)) I).X)
    (ht : RootCharactersOne P t)
    (g : (Over.map (algebraBaseMap R A)).obj (Over.mk (𝟙 (Spec (CommRingCat.of A)))) ⟶ G.X) :
    Commute (t ≫ i.hom.hom) g := by
  let δ := algebraBaseMap R A
  let U : Over (Spec (CommRingCat.of A)) := Over.mk (𝟙 _)
  let GA := (baseChange δ).obj G
  let : IsAffineHom GA.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom δ))
  let : Smooth G.X.hom := hG.smooth
  let iA := splitTorus.baseChangeHom (K := A) G I i
  let ET := baseChangePointsEquiv δ (splitTorus (Spec (CommRingCat.of R)) I) U
  let E := baseChangePointsEquiv δ G U
  let tA := ET.symm t ≫ (splitTorus.baseChangeIso δ I).hom.hom.hom
  have hTA : ET (tA ≫ (splitTorus.baseChangeIso δ I).inv.hom.hom) = t := by
    dsimp only [tA]
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id, MulEquiv.apply_symm_apply]
  have htA : RootCharactersOne P tA := by
    intro α
    rw [LocalSplitRootBaseChange.charValue_exponentCharacter_baseChange (R := R) A]
    exact (congrArg
      (VectorGroup.charValue (splitTorus.exponentCharacter _ I (P.root α)) _) hTA).trans
        (ht α)
  have hc := commute_of_rootCharacters_one_closedResidue
    (G := GA) (i := iA) (hG.baseChange δ)
    (splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i hmax)
    hP.baseChange_implicit b (𝟙 _) tA htA (E.symm g)
  have he := congrArg E hc.eq
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply,
    LocalSplitRootBaseChange.baseChangePointsEquiv_torus, hTA] at he
  exact he

/-- A torus point annihilating all roots commutes with every group point
over a local test ring, irrespective of the original base ring. -/
theorem commute_of_rootCharacters_one
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base)
    {A : Type u} [CommRing A] [IsLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (t : Over.mk s ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (ht : RootCharactersOne P t) (g : Over.mk s ⟶ G.X) :
    Commute (t ≫ i.hom.hom) g := by
  let φ := Spec.preimage s
  let : Algebra R A := φ.hom.toAlgebra
  have hs : algebraBaseMap R A = s := by
    change Spec.map (CommRingCat.ofHom φ.hom) = s
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let e : Over.mk s ≅
      (Over.map (algebraBaseMap R A)).obj (Over.mk (𝟙 (Spec (CommRingCat.of A)))) :=
    Over.isoMk (Iso.refl _) (by simp [hs])
  have hc := commute_on_algebra_test hG hmax hP b A (e.inv ≫ t) (ht.comp e.inv) (e.inv ≫ g)
  have he := congrArg (fun x => e.hom ≫ x) hc.eq
  simp only [MonObj.comp_mul, ← Category.assoc, Iso.hom_inv_id, Category.id_comp] at he
  exact he

/-- Over an arbitrary commutative base ring, the actual root annihilator
maps into the full centre on every relative scheme test. -/
theorem mem_center_of_rootCharacters_one
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
  have hc := commute_of_rootCharacters_one hG hmax hP b s
    (r ≫ a ≫ t) (ht.comp (r ≫ a)) (r ≫ g)
  have he : r ≫ ((a ≫ t ≫ i.hom.hom) * g) =
      r ≫ (g * (a ≫ t ≫ i.hom.hom)) := by
    simpa only [MonObj.comp_mul, Category.assoc] using hc.eq
  exact congrArg CommaMorphism.left he

/-- Simple-root character equations alone imply full centrality, including
on nonaffine and nonreduced tests over an arbitrary coefficient ring. -/
theorem mem_center_of_simpleRootCharacters_one
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base)
    {Z : Over (Spec (CommRingCat.of R))}
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (ht : SimpleRootCharactersOne b t) :
    t ≫ i.hom.hom ∈ (center G).carrier Z :=
  mem_center_of_rootCharacters_one hG hmax hP b t (rootCharactersOne_of_simple ht)

end ArbitraryBase

end Langlands.GroupScheme

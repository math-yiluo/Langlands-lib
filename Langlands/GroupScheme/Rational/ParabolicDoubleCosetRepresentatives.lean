import Langlands.GroupScheme.Rational.ParabolicDoubleCosetFiniteness
import Langlands.GroupScheme.Rational.ParabolicIntersectionAssembly
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Transporting a common split torus into two supplied Levi subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A maximal split torus contained in an actual parabolic can be conjugated
into a supplied rational Levi by a rational point of that parabolic. -/
def ParabolicSplitTorusLeviConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P M : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
        IsMaximalSplitTorus i →
        ∀ f : T.toGrp ⟶ P, f ≫ p = i →
          ∃ (u : rationalPoints P) (a : T.toGrp ⟶ M),
            a ≫ l ≫ p = i ≫ (G.innerIso (rationalPoints.map p u)).hom

variable {k : Type u} [Field k]
    {G P M Q L : GroupScheme (Spec (CommRingCat.of k))}

/-- Two parabolic-point conjugations of a common torus give the required
representative, with all point images and torus factors kept literal. -/
theorem torusAdaptedDoubleCosetRepresentative_of_conjugate_factors
    (p : P ⟶ G) (l : M ⟶ P) (q : Q ⟶ G) (lQ : L ⟶ Q)
    (g : rationalPoints G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i)
    (u : rationalPoints P) (v : rationalPoints Q)
    (a : T.toGrp ⟶ M) (b : T.toGrp ⟶ L)
    (ha : a ≫ l ≫ p = i ≫ (G.innerIso (rationalPoints.map p u)).hom)
    (hb : b ≫ lQ ≫ q =
      i ≫ (G.innerIso g).inv ≫ (G.innerIso (rationalPoints.map q v)).hom) :
    ∃ z : rationalPoints G,
      DoubleCoset.mk (rationalPoints.map p).range (rationalPoints.map q).range z =
        DoubleCoset.mk (rationalPoints.map p).range (rationalPoints.map q).range g ∧
      ∃ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G),
        IsMaximalSplitTorus i' ∧ (∃ a' : T'.toGrp ⟶ M, a' ≫ l ≫ p = i') ∧
          ∃ b' : T'.toGrp ⟶ L, b' ≫ lQ ≫ q ≫ (G.innerIso z).hom = i' := by
  let U := rationalPoints.map p u
  let V := rationalPoints.map q v
  let z := U * g * V⁻¹
  have hz : (G.innerIso V).hom ≫ (G.innerIso z).hom =
      (G.innerIso g).hom ≫ (G.innerIso U).hom := by
    rw [← innerIso_mul_hom, ← innerIso_mul_hom]
    congr 1
    dsimp only [z]
    group
  refine ⟨z, ?_, T, i ≫ (G.innerIso U).hom,
    hi.comp_iso (G.innerIso U), ⟨a, ha⟩, b, ?_⟩
  · apply DoubleCoset.eq.mpr
    refine ⟨U⁻¹, (rationalPoints.map p).range.inv_mem ⟨u, rfl⟩,
      V, ⟨v, rfl⟩, ?_⟩
    dsimp only [z]
    group
  · calc
      b ≫ lQ ≫ q ≫ (G.innerIso z).hom =
          (b ≫ lQ ≫ q) ≫ (G.innerIso z).hom := by
            simp only [Category.assoc]
      _ = (i ≫ (G.innerIso g).inv ≫ (G.innerIso V).hom) ≫
          (G.innerIso z).hom := by rw [hb]
      _ = i ≫ (G.innerIso U).hom := by
        simp only [Category.assoc]
        rw [hz, Iso.inv_hom_id_assoc]

/-- A common maximal split torus of the two parabolics and conjugation into
each supplied rational Levi imply the torus-adapted representative clause. -/
theorem torusAdaptedDoubleCosetRepresentative_of_common_torus
    (hCommon : ParabolicIntersectionSplitTorusStatement.{u})
    (hMove : ParabolicSplitTorusLeviConjugacyStatement.{u})
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l)
    (q : Q ⟶ G) (lQ : L ⟶ Q) (hq : IsParabolicSubgroup q)
    (hlQ : IsRationalLeviSubgroup lQ) (g : rationalPoints G) :
    ∃ z : rationalPoints G,
      DoubleCoset.mk (rationalPoints.map p).range (rationalPoints.map q).range z =
        DoubleCoset.mk (rationalPoints.map p).range (rationalPoints.map q).range g ∧
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
        IsMaximalSplitTorus i ∧ (∃ a : T.toGrp ⟶ M, a ≫ l ≫ p = i) ∧
          ∃ b : T.toGrp ⟶ L, b ≫ lQ ≫ q ≫ (G.innerIso z).hom = i := by
  obtain ⟨T, i, hi, f, fQ, hf, hfQ⟩ :=
    hCommon k G hG P Q p (q ≫ (G.innerIso g).hom) hp
      (hq.comp_iso (G.innerIso g))
  obtain ⟨u, a, ha⟩ := hMove k G hG P M p l hp hl T i hi f hf
  have hfQ' : fQ ≫ q = i ≫ (G.innerIso g).inv := by
    rw [← hfQ, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨v, b, hb⟩ := hMove k G hG Q L q lQ hq hlQ T
    (i ≫ (G.innerIso g).inv) (hi.comp_iso (G.innerIso g).symm) fQ hfQ'
  exact torusAdaptedDoubleCosetRepresentative_of_conjugate_factors
    p l q lQ g i hi u v a b ha (by simpa only [Category.assoc] using hb)

/-- Assembly of the exact published proposition from the explicit structural
inputs for finiteness and torus-adapted representatives. -/
theorem representedParabolicDoubleCosetStatement_of_structural_inputs
    (hBruhat : RationalBruhatStatement.{u})
    (hGeneric : GenericMinimalParabolicStatement.{u})
    (hConjugacy : MinimalParabolicConjugacyStatement.{u})
    (hCommon : ParabolicIntersectionSplitTorusStatement.{u})
    (hMove : ParabolicSplitTorusLeviConjugacyStatement.{u}) :
    RepresentedParabolicDoubleCosetStatement.{u} := by
  intro k _ G hG P M Q L p l hp hl q lQ hq hlQ
  exact ⟨finite_parabolicDoubleCosets_of_bruhat_minimal_conjugacy
      hBruhat hGeneric hConjugacy hG p q hp hq,
    torusAdaptedDoubleCosetRepresentative_of_common_torus
      hCommon hMove hG p l hp hl q lQ hq hlQ⟩

end Langlands.GroupScheme

import Langlands.ClassFieldTheory.Local.ClassFormationCupLawsStatement
import Langlands.ClassFieldTheory.Local.FundamentalConsequencesProof
import Langlands.Cohomology.Tate.CupTransfer
import Langlands.Cohomology.Tate.CupProof
import Langlands.Cohomology.Tate.ReindexNaturality
import Langlands.Cohomology.Tate.PositiveRestriction

/-!
# Fundamental-class cup products commute with Tate restriction and corestriction

Two generic facts about the constructed Tate cup product are proved first:
the projection formula with the restricted class in the first variable, and
compatibility of the tensor cup with reindexing along a group isomorphism.
They give, for every tower `K ⊆ L ⊆ M` with `M/K` and `M/L` finite, the
unscaled restriction and corestriction diagrams for left cup with a
degree-two class and its restriction. The finite class-formation axioms
identify the restriction of the fundamental class of `M/K` with that of `M/L`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

section LeftProjection

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

omit [Fintype G] [Fintype H] [Fintype (G ⧸ H)] in
lemma restrict_tensorInvariantLeft (A B : Rep.{u} R G) (a : A.ρ.invariants) :
    (Rep.resFunctor H.subtype).map (tensorInvariantLeft A B a) =
      tensorInvariantLeft (Rep.res H.subtype A) (Rep.res H.subtype B)
        (invariantRestriction H A a) := rfl

lemma tensorCup_corestriction_left_zero (A B : Rep.{u} R G) (q : ℤ)
    (a : tateCohomology A 0) (b : tateCohomology (Rep.res H.subtype B) q) :
    corestriction H (A ⊗ B) (0 + q)
        (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) 0 q
          (restriction H A 0 a) b) =
      tensorCup A B 0 q a (corestriction H B q b) := by
  obtain ⟨a, rfl⟩ := zeroClass_surjective A a
  change corestriction H (A ⊗ B) (0 + q)
    (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) 0 q
      (restrictionZero H A (zeroClass A a)) b) = _
  rw [restrictionZero_zeroClass, tensorCup_invariantLeft, tensorCup_invariantLeft]
  refine (corestriction_degreeTransport H (A ⊗ B) (show q = 0 + q by omega)
    ((tateCohomologyFunctor q).map
      ((Rep.resFunctor H.subtype).map (tensorInvariantLeft A B a)) b)).trans ?_
  exact congrArg (tateDegreeIso (A ⊗ B) (show q = 0 + q by omega)).hom
    (corestriction_naturality H q (tensorInvariantLeft A B a) b).symm

omit [Fintype G] [Fintype H] [Fintype (G ⧸ H)] in
lemma restricted_tensorRight_shortExact (S : ShortComplex (Rep.{u} R G))
    (B : Rep.{u} R G) (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact) :
    ((S.map (Rep.resFunctor H.subtype)).map
      (MonoidalCategory.tensorRight (Rep.res H.subtype B))).ShortExact := by
  change ((S.map (MonoidalCategory.tensorRight B)).map (Rep.resFunctor H.subtype)).ShortExact
  exact hB.map_of_exact _

/-- Restricting a first-variable boundary and corestricting the cup gives the
boundary of the corestricted cup. -/
lemma tensorCup_corestriction_left_boundary (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (B : Rep.{u} R G) (p q : ℤ) (x : tateCohomology S.X₃ p)
    (b : tateCohomology (Rep.res H.subtype B) q) :
    corestriction H (S.X₁ ⊗ B) ((p + 1) + q)
        (tensorCup (Rep.res H.subtype S.X₁) (Rep.res H.subtype B) (p + 1) q
          (restriction H S.X₁ (p + 1)
            (TateCohomology.δ (scalarSplit_shortExact S s) p x)) b) =
      tateDeltaTo (scalarSplit_tensorRight_shortExact S s B)
        (p + q) ((p + 1) + q) (by omega)
        (corestriction H (S.X₃ ⊗ B) (p + q)
          (tensorCup (Rep.res H.subtype S.X₃) (Rep.res H.subtype B) p q
            (restriction H S.X₃ p x) b)) := by
  rw [restriction_scalarSplit_delta H S s p x]
  refine (congrArg (corestriction H (S.X₁ ⊗ B) ((p + 1) + q))
    (tensorCup_delta_first (S.map (Rep.resFunctor H.subtype))
      ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype))
      (Rep.res H.subtype B)
      (restricted_tensorRight_shortExact H S B (scalarSplit_tensorRight_shortExact S s B))
      p q (restriction H S.X₃ p x) b)).trans ?_
  exact corestriction_deltaTo H (S.map (MonoidalCategory.tensorRight B))
    (scalarSplitting_tensorRight S s B) (p + q) ((p + 1) + q) (by omega)
    (tensorCup (Rep.res H.subtype S.X₃) (Rep.res H.subtype B) p q
      (restriction H S.X₃ p x) b)

/-- The tensor projection formula with the restricted class in the first
variable, in every integer bidegree. -/
lemma tensorCup_corestriction_left (A B : Rep.{u} R G) (p q : ℤ)
    (a : tateCohomology A p) (b : tateCohomology (Rep.res H.subtype B) q) :
    corestriction H (A ⊗ B) (p + q)
        (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q
          (restriction H A p a) b) =
      tensorCup A B p q a (corestriction H B q b) := by
  refine tateClass_shift_induction
    (fun A p a => corestriction H (A ⊗ B) (p + q)
        (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q
          (restriction H A p a) b) =
      tensorCup A B p q a (corestriction H B q b))
    (fun A a => tensorCup_corestriction_left_zero H A B q a b) ?_ ?_ A p a
  · intro A p x ih
    refine (tensorCup_corestriction_left_boundary H (shiftUpSequence A)
      (shiftUpSequence_scalarSplitting A) B p q x b).trans ?_
    refine Eq.trans ?_ (tensorCup_delta_first (shiftUpSequence A)
      (shiftUpSequence_shortExact A) B
      (scalarSplit_tensorRight_shortExact _ (shiftUpSequence_scalarSplitting A) B)
      p q x (corestriction H B q b)).symm
    exact congrArg (tateDeltaTo (scalarSplit_tensorRight_shortExact _
      (shiftUpSequence_scalarSplitting A) B) (p + q) ((p + 1) + q) (by omega)) ih
  · intro A p x ih
    let e := tensorShiftDownLeftIso A B (p + q) ≪≫
      tateDegreeIso (shiftDown A ⊗ B) (show (p + q) + 1 = (p + 1) + q by omega)
    apply e.toLinearEquiv.injective
    exact (tensorCup_corestriction_left_boundary H (shiftDownSequence A)
      (shiftDownSequence_scalarSplitting A) B p q x b).symm.trans
        (ih.trans (tensorCup_delta_first (shiftDownSequence A)
          (shiftDownSequence_shortExact A) B
          (scalarSplit_tensorRight_shortExact _ (shiftDownSequence_scalarSplitting A) B)
          p q x (corestriction H B q b)))

/-- The projection formula for every equivariant pairing, with the restricted
class in the first variable. -/
lemma cup_corestriction_left {A B C : Rep.{u} R G} (φ : Pairing A B C) (p q : ℤ)
    (a : tateCohomology A p) (b : tateCohomology (Rep.res H.subtype B) q) :
    corestriction H C (p + q) (cup (φ.restrict H) p q (restriction H A p a) b) =
      cup φ p q a (corestriction H B q b) := by
  refine (corestriction_naturality H (p + q) φ.tensorHom
    (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q
      (restriction H A p a) b)).symm.trans ?_
  exact congrArg (fun x => (tateCohomologyFunctor (p + q)).map φ.tensorHom x)
    (tensorCup_corestriction_left H A B p q a b)

end LeftProjection

section Reindex

variable {R G H : Type u} [CommRing R] [Group G] [Group H] [Fintype G] [Fintype H]
variable (e : G ≃* H)

/-- Reindexing commutes with transport between equal degrees. -/
lemma reindex_degreeTransport {A : Rep.{u} R G} {B : Rep.{u} R H}
    (φ : Rep.res e.symm.toMonoidHom A ⟶ B) {m n : ℤ} (h : m = n)
    (x : tateCohomology A m) :
    reindex e φ n ((tateDegreeIso A h).hom x) =
      (tateDegreeIso B h).hom (reindex e φ m x) := by
  subst h
  rfl

/-- Reindexing by a coefficient map is reindexing by the identity followed by
the map on Tate cohomology. -/
lemma reindex_eq_map {A : Rep.{u} R G} {B : Rep.{u} R H}
    (φ : Rep.res e.symm.toMonoidHom A ⟶ B) (n : ℤ) (x : tateCohomology A n) :
    reindex e φ n x =
      (tateCohomologyFunctor n).map φ
        (reindex e (𝟙 (Rep.res e.symm.toMonoidHom A)) n x) := by
  have h := reindex_naturality e (𝟙 (Rep.res e.symm.toMonoidHom A)) φ (𝟙 A) φ
    (by rw [Category.id_comp]; exact (Category.id_comp φ).symm) n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact (ConcreteCategory.congr_hom h x).symm

/-- Identity reindexing is natural in the coefficient module. -/
lemma reindex_id_map {A C : Rep.{u} R G} (f : A ⟶ C) (n : ℤ) (x : tateCohomology A n) :
    reindex e (𝟙 (Rep.res e.symm.toMonoidHom C)) n ((tateCohomologyFunctor n).map f x) =
      (tateCohomologyFunctor n).map ((Rep.resFunctor e.symm.toMonoidHom).map f)
        (reindex e (𝟙 (Rep.res e.symm.toMonoidHom A)) n x) :=
  (ConcreteCategory.congr_hom (reindex_naturality e (𝟙 _) (𝟙 _) f
    ((Rep.resFunctor e.symm.toMonoidHom).map f) (by simp) n) x).symm

omit [Fintype G] [Fintype H] in
lemma reindexed_shortExact {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact) :
    (S.map (Rep.resFunctor e.symm.toMonoidHom)).ShortExact :=
  hS.map_of_exact _

omit [Fintype G] [Fintype H] in
lemma reindexed_tensorLeft_shortExact (S : ShortComplex (Rep.{u} R G))
    (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact) :
    ((S.map (Rep.resFunctor e.symm.toMonoidHom)).map
      (MonoidalCategory.tensorLeft (Rep.res e.symm.toMonoidHom A))).ShortExact := by
  change ((S.map (MonoidalCategory.tensorLeft A)).map
    (Rep.resFunctor e.symm.toMonoidHom)).ShortExact
  exact hA.map_of_exact _

/-- Identity reindexing commutes with the degree-transported connecting maps. -/
lemma reindex_tateDeltaTo {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (n m : ℤ) (h : n + 1 = m) (x : tateCohomology S.X₃ n) :
    reindex e (𝟙 (Rep.res e.symm.toMonoidHom S.X₁)) m (tateDeltaTo hS n m h x) =
      tateDeltaTo (reindexed_shortExact e hS) n m h
        (reindex e (𝟙 (Rep.res e.symm.toMonoidHom S.X₃)) n x) := by
  subst m
  have h := ConcreteCategory.congr_hom (reindex_delta e hS (reindexed_shortExact e hS)
    (𝟙 (S.map (Rep.resFunctor e.symm.toMonoidHom))) n) x
  simp only [tateDeltaTo, tateDegreeIso, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact h

omit [Fintype G] [Fintype H] in
lemma reindex_tensorInvariantRight (A B : Rep.{u} R G) (b : B.ρ.invariants) :
    (Rep.resFunctor e.symm.toMonoidHom).map (tensorInvariantRight A B b) =
      tensorInvariantRight (Rep.res e.symm.toMonoidHom A) (Rep.res e.symm.toMonoidHom B)
        (reindexInvariants e (𝟙 (Rep.res e.symm.toMonoidHom B)) b) := rfl

lemma reindex_tensorCup_zero (A B : Rep.{u} R G) (p : ℤ)
    (a : tateCohomology A p) (b : tateCohomology B 0) :
    reindex e (𝟙 (Rep.res e.symm.toMonoidHom (A ⊗ B))) (p + 0) (tensorCup A B p 0 a b) =
      tensorCup (Rep.res e.symm.toMonoidHom A) (Rep.res e.symm.toMonoidHom B) p 0
        (reindex e (𝟙 (Rep.res e.symm.toMonoidHom A)) p a)
        (reindex e (𝟙 (Rep.res e.symm.toMonoidHom B)) 0 b) := by
  obtain ⟨b, rfl⟩ := zeroClass_surjective B b
  rw [reindex_zeroClass, tensorCup_invariantRight, tensorCup_invariantRight,
    reindex_degreeTransport, ← reindex_tensorInvariantRight]
  exact congrArg (tateDegreeIso _ (show p = p + 0 by omega)).hom
    (reindex_id_map e (tensorInvariantRight A B b) p a)

lemma reindex_tensorCup_boundary (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (p q : ℤ) (a : tateCohomology A p) (b : tateCohomology S.X₃ q) :
    reindex e (𝟙 (Rep.res e.symm.toMonoidHom (A ⊗ S.X₁))) (p + (q + 1))
        (tensorCup A S.X₁ p (q + 1) a (TateCohomology.δ hS q b)) =
      (p.negOnePow : ℤ) •
        tateDeltaTo (reindexed_shortExact e hA) (p + q) (p + (q + 1)) (by omega)
          (reindex e (𝟙 (Rep.res e.symm.toMonoidHom (A ⊗ S.X₃))) (p + q)
            (tensorCup A S.X₃ p q a b)) := by
  rw [tensorCup_delta_second S hS A hA, map_zsmul]
  exact congrArg (fun x => (p.negOnePow : ℤ) • x)
    (reindex_tateDeltaTo e hA (p + q) (p + (q + 1)) (by omega)
      (tensorCup A S.X₃ p q a b))

lemma reindexed_tensorCup_boundary (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (p q : ℤ) (a : tateCohomology (Rep.res e.symm.toMonoidHom A) p)
    (b : tateCohomology S.X₃ q) :
    tensorCup (Rep.res e.symm.toMonoidHom A) (Rep.res e.symm.toMonoidHom S.X₁) p (q + 1) a
        (reindex e (𝟙 (Rep.res e.symm.toMonoidHom S.X₁)) (q + 1)
          (TateCohomology.δ hS q b)) =
      (p.negOnePow : ℤ) •
        tateDeltaTo (reindexed_shortExact e hA) (p + q) (p + (q + 1)) (by omega)
          (tensorCup (Rep.res e.symm.toMonoidHom A) (Rep.res e.symm.toMonoidHom S.X₃) p q a
            (reindex e (𝟙 (Rep.res e.symm.toMonoidHom S.X₃)) q b)) := by
  have hb : reindex e (𝟙 (Rep.res e.symm.toMonoidHom S.X₁)) (q + 1)
      (TateCohomology.δ hS q b) =
        TateCohomology.δ (reindexed_shortExact e hS) q
          (reindex e (𝟙 (Rep.res e.symm.toMonoidHom S.X₃)) q b) :=
    ConcreteCategory.congr_hom (reindex_delta e hS (reindexed_shortExact e hS)
      (𝟙 (S.map (Rep.resFunctor e.symm.toMonoidHom))) q) b
  rw [hb]
  exact tensorCup_delta_second (S.map (Rep.resFunctor e.symm.toMonoidHom))
    (reindexed_shortExact e hS) (Rep.res e.symm.toMonoidHom A)
    (reindexed_tensorLeft_shortExact e S A hA) p q a
    (reindex e (𝟙 (Rep.res e.symm.toMonoidHom S.X₃)) q b)

lemma reindexedTensorCoinduced_tate_isZero (A B : Rep.{u} R G) (n : ℤ) :
    IsZero (tateCohomology (Rep.res e.symm.toMonoidHom (A ⊗ coinduced B)) n) :=
  (tensorCoinduced_tate_isZero A B n).of_iso (reindexIso e (Iso.refl _) n).symm

/-- The tensor augmentation boundary remains invertible after reindexing. -/
def reindexedTensorShiftDownIso (A B : Rep.{u} R G) (n : ℤ) :
    tateCohomology (Rep.res e.symm.toMonoidHom (A ⊗ B)) n ≅
      tateCohomology (Rep.res e.symm.toMonoidHom (A ⊗ shiftDown B)) (n + 1) := by
  let hS := reindexed_shortExact e (scalarSplit_tensorLeft_shortExact _
    (shiftDownSequence_scalarSplitting B) A)
  have := tate_delta_isIso hS n
    (reindexedTensorCoinduced_tate_isZero e A B n)
    (reindexedTensorCoinduced_tate_isZero e A B (n + 1))
  exact asIso (TateCohomology.δ hS n)

/-- Reindexing along a group isomorphism preserves the constructed tensor cup
in every integer bidegree. -/
lemma reindex_tensorCup (A B : Rep.{u} R G) (p q : ℤ)
    (a : tateCohomology A p) (b : tateCohomology B q) :
    reindex e (𝟙 (Rep.res e.symm.toMonoidHom (A ⊗ B))) (p + q) (tensorCup A B p q a b) =
      tensorCup (Rep.res e.symm.toMonoidHom A) (Rep.res e.symm.toMonoidHom B) p q
        (reindex e (𝟙 (Rep.res e.symm.toMonoidHom A)) p a)
        (reindex e (𝟙 (Rep.res e.symm.toMonoidHom B)) q b) := by
  refine tateClass_shift_induction
    (fun B q b => reindex e (𝟙 (Rep.res e.symm.toMonoidHom (A ⊗ B))) (p + q)
        (tensorCup A B p q a b) =
      tensorCup (Rep.res e.symm.toMonoidHom A) (Rep.res e.symm.toMonoidHom B) p q
        (reindex e (𝟙 (Rep.res e.symm.toMonoidHom A)) p a)
        (reindex e (𝟙 (Rep.res e.symm.toMonoidHom B)) q b))
    (fun B b => reindex_tensorCup_zero e A B p a b) ?_ ?_ B q b
  · intro B q b ih
    refine (reindex_tensorCup_boundary e (shiftUpSequence B)
      (shiftUpSequence_shortExact B) A
      (scalarSplit_tensorLeft_shortExact _ (shiftUpSequence_scalarSplitting B) A)
      p q a b).trans ?_
    refine Eq.trans ?_ (reindexed_tensorCup_boundary e (shiftUpSequence B)
      (shiftUpSequence_shortExact B) A
      (scalarSplit_tensorLeft_shortExact _ (shiftUpSequence_scalarSplitting B) A) p q
      (reindex e (𝟙 (Rep.res e.symm.toMonoidHom A)) p a) b).symm
    exact congrArg (fun x => (p.negOnePow : ℤ) •
      tateDeltaTo (reindexed_shortExact e (scalarSplit_tensorLeft_shortExact _
        (shiftUpSequence_scalarSplitting B) A)) (p + q) (p + (q + 1)) (by omega) x) ih
  · intro B q b ih
    let i := reindexedTensorShiftDownIso e A B (p + q) ≪≫
      tateDegreeIso (Rep.res e.symm.toMonoidHom (A ⊗ shiftDown B))
        (show (p + q) + 1 = p + (q + 1) by omega)
    apply i.toLinearEquiv.injective
    have hb := (reindex_tensorCup_boundary e (shiftDownSequence B)
      (shiftDownSequence_shortExact B) A
      (scalarSplit_tensorLeft_shortExact _ (shiftDownSequence_scalarSplitting B) A)
      p q a b).symm.trans
        (ih.trans (reindexed_tensorCup_boundary e (shiftDownSequence B)
          (shiftDownSequence_shortExact B) A
          (scalarSplit_tensorLeft_shortExact _ (shiftDownSequence_scalarSplitting B) A) p q
          (reindex e (𝟙 (Rep.res e.symm.toMonoidHom A)) p a) b))
    have hh := congrArg (fun x => (p.negOnePow : ℤ) • x) hb
    have hs : (p.negOnePow : ℤ) * (p.negOnePow : ℤ) = 1 :=
      congrArg Units.val (Int.units_mul_self p.negOnePow)
    simp only [smul_smul, hs, one_smul] at hh
    exact hh

/-- A pairing restricted along the inverse group isomorphism. -/
def Pairing.reindexed {A B C : Rep.{u} R G} (φ : Pairing A B C) :
    Pairing (Rep.res e.symm.toMonoidHom A) (Rep.res e.symm.toMonoidHom B)
      (Rep.res e.symm.toMonoidHom C) where
  bilinear := φ.bilinear
  equivariant h a b := φ.equivariant (e.symm h) a b

/-- Reindexing along a group isomorphism preserves cup products for compatible
coefficient pairings, in every integer bidegree. -/
lemma reindex_cup {A B C : Rep.{u} R G} {A' B' C' : Rep.{u} R H}
    (φ : Pairing A B C) (ψ : Pairing A' B' C')
    (α : Rep.res e.symm.toMonoidHom A ⟶ A') (β : Rep.res e.symm.toMonoidHom B ⟶ B')
    (γ : Rep.res e.symm.toMonoidHom C ⟶ C')
    (hφ : ∀ a b, γ.hom (φ.bilinear a b) = ψ.bilinear (α.hom a) (β.hom b))
    (p q : ℤ) (a : tateCohomology A p) (b : tateCohomology B q) :
    reindex e γ (p + q) (cup φ p q a b) =
      cup ψ p q (reindex e α p a) (reindex e β q b) := by
  rw [reindex_eq_map e γ, reindex_eq_map e α, reindex_eq_map e β]
  have h1 : reindex e (𝟙 (Rep.res e.symm.toMonoidHom C)) (p + q) (cup φ p q a b) =
      cup (φ.reindexed e) p q (reindex e (𝟙 (Rep.res e.symm.toMonoidHom A)) p a)
        (reindex e (𝟙 (Rep.res e.symm.toMonoidHom B)) q b) := by
    change reindex e (𝟙 (Rep.res e.symm.toMonoidHom C)) (p + q)
        ((tateCohomologyFunctor (p + q)).map φ.tensorHom (tensorCup A B p q a b)) =
      (tateCohomologyFunctor (p + q)).map (φ.reindexed e).tensorHom
        (tensorCup _ _ p q (reindex e (𝟙 (Rep.res e.symm.toMonoidHom A)) p a)
          (reindex e (𝟙 (Rep.res e.symm.toMonoidHom B)) q b))
    rw [reindex_id_map, reindex_tensorCup]
    rfl
  rw [h1]
  exact cup_naturality p q (φ.reindexed e) ψ α β γ hφ _ _

end Reindex

end Langlands.Tate

namespace Langlands.ClassFieldTheory.Local

set_option backward.isDefEq.respectTransparency false

section Tower

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [FiniteDimensional K M] [FiniteDimensional L M]

/-- In degree two, subgroup reindexing of a restricted class is the
constructed Tate restriction of that class. -/
theorem relativeSubgroupTateIso_relativeRestriction (c : relativeCohomology K M 2) :
    letI := Fintype.ofFinite Gal(M/K)
    letI := Fintype.ofFinite Gal(M/L)
    letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
    letI := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
    (relativeSubgroupTateIso K L M 2).hom
        (((TateCohomology.isoGroupCohomology 2).app (unitsRepresentation L M)).inv
          (relativeRestriction K L M 2 c)) =
      Langlands.Tate.restriction (relativeGaloisSubgroup K L M) (unitsRepresentation K M) 2
        (((TateCohomology.isoGroupCohomology 2).app (unitsRepresentation K M)).inv c) := by
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  let := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  have h0 := ConcreteCategory.congr_hom (relativeSubgroupTateIso_positive K L M 2)
    (((TateCohomology.isoGroupCohomology 2).app (unitsRepresentation L M)).inv
      (relativeRestriction K L M 2 c))
  have h1 := ConcreteCategory.congr_hom
    (Langlands.Tate.restriction_groupCohomology (relativeGaloisSubgroup K L M)
      (unitsRepresentation K M) 2)
    (((TateCohomology.isoGroupCohomology 2).app (unitsRepresentation K M)).inv c)
  have h2 := ConcreteCategory.congr_hom
    (relativeRestriction_comp_subgroupCohomologyIso K L M 2) c
  simp only [ModuleCat.hom_ofHom, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at h0 h1
  refine h0.trans (Eq.trans ?_ h1.symm)
  exact congrArg ((TateCohomology.isoGroupCohomology 2).app
    (Rep.res (relativeGaloisSubgroup K L M).subtype (unitsRepresentation K M))).inv h2

/-- Subgroup reindexing carries left cup with a degree-two class of `M/L` to
the subgroup cup with the reindexed class. -/
theorem relativeSubgroupTateIso_relativeTateCup (n : ℤ) (d : relativeCohomology L M 2)
    (x : integralTateCohomology L M n) :
    letI := Fintype.ofFinite Gal(M/K)
    letI := Fintype.ofFinite Gal(M/L)
    letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
    (relativeSubgroupTateIso K L M (n + 2)).hom (relativeTateCup L M n d x) =
      (Langlands.Tate.tateDegreeIso _ (add_comm 2 n)).hom
        (Langlands.Tate.cup
          ((Langlands.Tate.scalarPairing (unitsRepresentation K M)).restrict
            (relativeGaloisSubgroup K L M)) 2 n
          ((relativeSubgroupTateIso K L M 2).hom
            (((TateCohomology.isoGroupCohomology 2).app (unitsRepresentation L M)).inv d))
          ((integralSubgroupTateIso K L M n).hom x)) := by
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  change Langlands.Tate.reindex (relativeGaloisSubgroupEquiv K L M)
      (relativeSubgroupUnitsIso K L M).hom (n + 2)
      ((Langlands.Tate.tateDegreeIso _ (add_comm 2 n)).hom
        (Langlands.Tate.cup (Langlands.Tate.scalarPairing (unitsRepresentation L M)) 2 n
          (((TateCohomology.isoGroupCohomology 2).app (unitsRepresentation L M)).inv d)
          x)) = _
  rw [Langlands.Tate.reindex_degreeTransport,
    Langlands.Tate.reindex_cup (relativeGaloisSubgroupEquiv K L M)
      (Langlands.Tate.scalarPairing _)
      ((Langlands.Tate.scalarPairing (unitsRepresentation K M)).restrict
        (relativeGaloisSubgroup K L M))
      (relativeSubgroupUnitsIso K L M).hom (integralSubgroupCoefficientsIso K L M).hom
      (relativeSubgroupUnitsIso K L M).hom (fun _ _ => rfl)]
  rfl

/-- Left cup with a degree-two class commutes with Tate restriction, the
class itself being restricted, in every integer degree. -/
theorem relativeTateRestriction_relativeTateCup (c : relativeCohomology K M 2) (n : ℤ)
    (x : integralTateCohomology K M n) :
    relativeTateRestriction K L M (n + 2) (relativeTateCup K M n c x) =
      relativeTateCup L M n (relativeRestriction K L M 2 c)
        (integralTateRestriction K L M n x) := by
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  let := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  let H := relativeGaloisSubgroup K L M
  let A := unitsRepresentation K M
  let Z := Rep.trivial IntegerScalars.{u} Gal(M/K) IntegerScalars.{u}
  apply (relativeSubgroupTateIso K L M (n + 2)).toLinearEquiv.injective
  change (relativeSubgroupTateIso K L M (n + 2)).hom
      ((relativeSubgroupTateIso K L M (n + 2)).inv
        (Langlands.Tate.restriction H A (n + 2) (relativeTateCup K M n c x))) =
    (relativeSubgroupTateIso K L M (n + 2)).hom
      (relativeTateCup L M n (relativeRestriction K L M 2 c)
        ((integralSubgroupTateIso K L M n).inv (Langlands.Tate.restriction H Z n x)))
  rw [Iso.inv_hom_id_apply, relativeSubgroupTateIso_relativeTateCup, Iso.inv_hom_id_apply,
    relativeSubgroupTateIso_relativeRestriction]
  refine (Langlands.Tate.restriction_degreeTransport H A (add_comm 2 n) _).trans ?_
  exact congrArg (Langlands.Tate.tateDegreeIso (Rep.res H.subtype A) (add_comm 2 n)).hom
    (Langlands.Tate.cup_restriction H (Langlands.Tate.scalarPairing A) 2 n _ x)

/-- Left cup with a degree-two class satisfies the projection formula for
Tate corestriction against its restriction, in every integer degree. -/
theorem relativeTateCorestriction_relativeTateCup (c : relativeCohomology K M 2) (n : ℤ)
    (x : integralTateCohomology L M n) :
    relativeTateCorestriction K L M (n + 2)
        (relativeTateCup L M n (relativeRestriction K L M 2 c) x) =
      relativeTateCup K M n c (integralTateCorestriction K L M n x) := by
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  let := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  let H := relativeGaloisSubgroup K L M
  let A := unitsRepresentation K M
  change Langlands.Tate.corestriction H A (n + 2)
      ((relativeSubgroupTateIso K L M (n + 2)).hom
        (relativeTateCup L M n (relativeRestriction K L M 2 c) x)) = _
  rw [relativeSubgroupTateIso_relativeTateCup, relativeSubgroupTateIso_relativeRestriction]
  refine (Langlands.Tate.corestriction_degreeTransport H A (add_comm 2 n) _).trans ?_
  exact congrArg (Langlands.Tate.tateDegreeIso A (add_comm 2 n)).hom
    (Langlands.Tate.cup_corestriction_left H (Langlands.Tate.scalarPairing A) 2 n _ _)

end Tower

/-- The finite class-formation axioms give the unscaled fundamental-class cup
restriction and corestriction diagrams in every integer Tate degree. -/
theorem classFormationTransferLaws : ClassFormationTransferLawsStatement.{u} := by
  intro p _ I hI F E M _ _ _ _ _ _ _ _ _ _ _
  refine ⟨fun c d hc hd n x => ?_, fun c d hc hd n x => ?_⟩
  · rw [← I.fundamentalRestriction_of_relativeClassFormation hI F E M c d hc hd]
    exact relativeTateRestriction_relativeTateCup F.Carrier E.Carrier M c n x
  · rw [← I.fundamentalRestriction_of_relativeClassFormation hI F E M c d hc hd]
    exact relativeTateCorestriction_relativeTateCup F.Carrier E.Carrier M c n x

end Langlands.ClassFieldTheory.Local

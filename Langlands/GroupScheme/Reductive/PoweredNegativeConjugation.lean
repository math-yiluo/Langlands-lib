import Langlands.GroupScheme.Reductive.LocalSplitWeylBraid
import Langlands.GroupScheme.Reductive.LocalSplitRootPairUniqueness
import Langlands.GroupScheme.Reductive.LocalSplitRootPairRescaling
import Langlands.GroupScheme.Reductive.PowerCommutatorTransport

/-! # Inverse-unit Weyl conjugation for powered root maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

section Power

variable {R : Type u} [CommRing R]
  {F : Ga R ⟶ Ga R} {q : ℕ}
  (hF : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
    rootPoint F Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ q))
  {G : GroupScheme (Spec (CommRingCat.of R))}

include hF

/-- Moving a scalar past a supplied power map raises the scalar to that power. -/
theorem scaleHom_precompose_power (r : R) (w : Ga R ⟶ G) :
    scaleHom r ≫ F ≫ w = F ≫ scaleHom (r ^ q) ≫ w := by
  apply hom_ext_rootPoint
  intro Z x
  rw [rootPoint_scaleHom, rootPoint_precompose_power hF,
    rootPoint_precompose_power hF, rootPoint_scaleHom, map_pow, mul_pow]

omit hF in
/-- Any additive-line precomposition commutes with a word of inner conjugations. -/
theorem wordConj_precompose {I J : Type u} (P : RootDatum J (I → ℤ) (I → ℤ))
    (u : J → (Ga R ⟶ G)) (l : List J) (F : Ga R ⟶ Ga R) (w : Ga R ⟶ G) :
    wordConj P u l (F ≫ w) = F ≫ wordConj P u l w := by
  rw [wordConj_eq_innerIso, wordConj_eq_innerIso, Category.assoc]

variable [IsLocalRing R] [IsAffineHom G.X.hom]
  {I : Type u} [Fintype I] {J : Type u}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- A powered equality identifies the genuine root rescaling at the point one. -/
theorem eq_scaleHom_of_precompose_power
    (hP : IsFibrewiseRootDatumOf I G i P) {a : J} {w z : Ga R ⟶ G}
    (hw : IsRootParametrization i (P.root a) w)
    (hz : IsRootParametrization i (P.root a) z) (κ : Rˣ)
    (h : F ≫ w = scaleHom (κ : R) ≫ F ≫ z) :
    w = scaleHom ((κ ^ q : Rˣ) : R) ≫ z := by
  apply eq_scaleHom_of_base hP hw hz (κ ^ q)
  have he := congrArg (fun v => rootPoint v (baseTest R) 1) h
  simpa only [rootPoint_precompose_power hF, rootPoint_scaleHom,
    one_pow, mul_one, ← map_pow, Units.val_pow_eq_pow_val] using he

end Power

section Negative

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b : P.Base} {W : ∀ a, SimpleWord P b a} {u : J → (Ga R ⟶ G)}
  {F : Ga R ⟶ Ga R} {q : ℕ}
  (hF : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
    rootPoint F Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ q))

include hF

/-- Partner uniqueness and inverse rescaling transfer negative conjugation through
a common actual power map, for every unit of the original ring. -/
theorem IsNormalSimpleData.conj_neg_precompose_power_of_partner
    (hd : IsNormalSimpleData i P b W u)
    (hPU : PartnerUnique P G i) (hSC : PartnerRescales P G i)
    {c : J} (hc : c ∈ b.support) {a : J}
    (ha : b.IsPos a) (hca : b.IsPos (P.reflectionPerm c a)) (κ : Rˣ)
    (h : wordConj P u [c] (F ≫ weylFamily P W u a) =
      scaleHom (κ : R) ≫ F ≫ weylFamily P W u (P.reflectionPerm c a)) :
    wordConj P u [c] (F ≫ weylFamily P W u (P.reflectionPerm a a)) =
      scaleHom ((κ⁻¹ : Rˣ) : R) ≫ F ≫
        weylFamily P W u (P.reflectionPerm c (P.reflectionPerm a a)) := by
  have hw : IsRootParametrization i (P.root (P.reflectionPerm c a))
      (wordConj P u [c] (weylFamily P W u a)) := by
    simpa only [Langlands.LinearAlgebra.wordPerm, List.foldr_cons, List.foldr_nil] using
      hd.isRootParametrization_wordConj (l := [c]) (by simpa using hc)
        (hd.isRootParametrization a)
  rw [wordConj_precompose] at h
  have hp := eq_scaleHom_of_precompose_power hF hd.rootDatum hw
    (hd.isRootParametrization (P.reflectionPerm c a)) κ h
  have hn := hd.conj_neg hPU hSC hc ha hca hp
  rw [wordConj_precompose, hn]
  rw [scaleHom_precompose_power hF]
  rfl

/-- For an actual closed fibrewise maximal torus, the published root-pair theorems
discharge both partner hypotheses in the powered negative-conjugation law. -/
theorem IsNormalSimpleData.conj_neg_precompose_power
    (hd : IsNormalSimpleData i P b W u) (hi : IsClosedSubgroup i)
    {c : J} (hc : c ∈ b.support) {a : J}
    (ha : b.IsPos a) (hca : b.IsPos (P.reflectionPerm c a)) (κ : Rˣ)
    (h : wordConj P u [c] (F ≫ weylFamily P W u a) =
      scaleHom (κ : R) ≫ F ≫ weylFamily P W u (P.reflectionPerm c a)) :
    wordConj P u [c] (F ≫ weylFamily P W u (P.reflectionPerm a a)) =
      scaleHom ((κ⁻¹ : Rˣ) : R) ≫ F ≫
        weylFamily P W u (P.reflectionPerm c (P.reflectionPerm a a)) := by
  apply hd.conj_neg_precompose_power_of_partner hF ?_ ?_ hc ha hca κ h
  · intro a xp xm xm' hp hm hm' hn hn'
    exact rootPartner_unique hd.reductive hi hd.maximal hd.rootDatum a hp hm hm' hn hn'
  · intro a xp xm hp hm hn k
    exact isWeylPoint_rescale hd.reductive hi hd.maximal hd.rootDatum a hp hm hn k

end Negative

/-- Actual normal target data imply the inverse-unit negative law after a supplied
common additive power, without assuming that the powered maps parametrize roots. -/
def PoweredNegativeConjugationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (I : Type u) [Fintype I] [DecidableEq I] (J : Type u)
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
    (W : ∀ a, SimpleWord P b a) (u : J → (Ga R ⟶ G)),
    IsNormalSimpleData i P b W u → IsClosedSubgroup i →
    ∀ (F : Ga R ⟶ Ga R) (q : ℕ),
      (∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
        rootPoint F Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ q)) →
      ∀ c ∈ b.support, ∀ a, b.IsPos a → b.IsPos (P.reflectionPerm c a) →
      ∀ κ : Rˣ,
        wordConj P u [c] (F ≫ weylFamily P W u a) =
          scaleHom (κ : R) ≫ F ≫ weylFamily P W u (P.reflectionPerm c a) →
        wordConj P u [c] (F ≫ weylFamily P W u (P.reflectionPerm a a)) =
          scaleHom ((κ⁻¹ : Rˣ) : R) ≫ F ≫
            weylFamily P W u (P.reflectionPerm c (P.reflectionPerm a a))

theorem poweredNegativeConjugation : PoweredNegativeConjugationStatement.{u} := by
  intro R _ _ I _ _ J G _ i P b W u hd hi F q hF c hc a ha hca κ h
  exact hd.conj_neg_precompose_power hF hi hc ha hca κ h

end Langlands.GroupScheme.LocalSplitCell

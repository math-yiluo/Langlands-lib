import Langlands.Representation.CuspidalSupport.AdjacentFactorComparison
import Langlands.Representation.Classification.CuspidalProductContragredient
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof

/-! Actual dual quotient presentations for the adjacent factors. -/

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport

open GeneralLinear Classification

universe uG uV uF

/-- A surjective intertwiner identifies the actual quotient by its kernel
with its target. -/
def quotientKernelEquiv {G : Type uG} [Group G] [TopologicalSpace G]
    (P Q : SmoothRep.{0,uG,uV} ℂ G)
    (q : P.representation.IntertwiningMap Q.representation)
    (hq : Function.Surjective q) :
    (SmoothRep.quotient P q.ker).representation.Equiv Q.representation :=
  Representation.Equiv.mk (q.toLinearMap.quotKerEquivOfSurjective hq) (fun g => by
    apply Submodule.linearMap_qext
    ext v
    exact Representation.IntertwiningMap.isIntertwining _ _ q g v)

/-- A simple subrepresentation of an admissible reducible representation
dualizes to the actual quotient by a nonzero proper kernel in any supplied
equivalent presentation of the smooth dual. -/
theorem dualSubrepresentation_exists_quotient
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : CompactOpenCofinal G)
    (P R : SmoothRep.{0,uG,uV} ℂ G) (S : Subrepresentation P.representation)
    (hP : P.IsAdmissible) (hPred : ¬ P.IsIrreducible)
    (hSi : (SmoothRep.subrepresentation P S).IsIrreducible)
    (hSa : (SmoothRep.subrepresentation P S).IsAdmissible)
    (e : P.contragredient ≅ R) :
    ∃ U : Subrepresentation R.representation, U ≠ ⊥ ∧ U ≠ ⊤ ∧
      Nonempty ((SmoothRep.quotient R U).representation.Equiv
        (SmoothRep.subrepresentation P S).contragredient.representation) := by
  let L := SmoothRep.subrepresentation P S
  have hLi : L.contragredient.IsIrreducible :=
    (SmoothRep.isIrreducible_contragredient_iff hG L hSa).mpr hSi
  have hRred : ¬ R.IsIrreducible := by
    intro hR
    have hPd := JacquetLength.isIrreducible_of_equiv
      (SmoothRep.equivOfIso e.symm) hR
    exact hPred ((SmoothRep.isIrreducible_contragredient_iff hG P hP).mp hPd)
  let i := SmoothRep.subtype P S
  let q := (SmoothRep.hom (SmoothRep.contragredientHom i)).comp
    (SmoothRep.equivOfIso e.symm).toIntertwiningMap
  have hq : Function.Surjective q :=
    (contragredientMap_surjective_of_injective_of_compact_cofinal hG
      L.isSmooth P.isSmooth (SmoothRep.hom i) (SmoothRep.subtype_injective P S)).comp
      (SmoothRep.equivOfIso e.symm).surjective
  have hU₀ : q.ker ≠ ⊥ := by
    intro hU
    have hi : Function.Injective q := LinearMap.ker_eq_bot.mp
      (congrArg Subrepresentation.toSubmodule hU)
    exact hRred (JacquetLength.isIrreducible_of_equiv (q.ofBijective ⟨hi,hq⟩).symm hLi)
  have hU₁ : q.ker ≠ ⊤ := by
    intro hU
    let := hLi
    let : Nontrivial L.contragredient :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) L.contragredient.representation.asModule
    obtain ⟨v, hv⟩ := exists_ne (0 : L.contragredient)
    obtain ⟨x, rfl⟩ := hq v
    have hx : x ∈ q.ker := by rw [hU]; trivial
    exact hv hx
  exact ⟨q.ker, hU₀, hU₁, ⟨quotientKernelEquiv R L.contragredient q hq⟩⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- An actual two-factor product of admissible factors is admissible. -/
theorem twoFactorProduct_admissible {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)),
      A.IsAdmissible → B.IsAdmissible →
      ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks a b ha hb)).obj
        (twoBlockFactors ha hb A B)).IsAdmissible := by
  let := T.topology
  let (r : ℕ) := T.generalLinearTopologicalGroup r
  intro A B hA hB
  apply Parabolic.normalizedInductionAdmissibility F T _ _
  exact FiniteTensor.isAdmissible_external
    (fun i => (twoBlockFactors ha hb A B i).representation)
    (Fin.cases hA (Fin.cases hB finZeroElim))

/-- The smooth dual of the actual two-factor product is the actual product
of the smooth duals, in the same order and on the same two-block shape. -/
def twoFactorProduct_contragredientIso {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    letI (r : ℕ) := T.generalLinearTopologicalGroup r
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier))
      (_hA : A.IsAdmissible) (_hB : B.IsAdmissible),
      ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks a b ha hb)).obj
        (twoBlockFactors ha hb A B)).contragredient ≅
      (T.normalizedProductInductionFunctor (Shahidi.twoBlocks a b ha hb)).obj
        (twoBlockFactors ha hb A.contragredient B.contragredient) := by
  let := T.topology
  let (r : ℕ) := T.generalLinearTopologicalGroup r
  intro A B hA hB
  let K := Shahidi.twoBlocks a b ha hb
  let fac := twoBlockFactors ha hb A B
  let P := (T.normalizedProductInductionFunctor K).obj fac
  let Q := (T.normalizedProductInductionFunctor K).obj
    (twoBlockFactors ha hb A.contragredient B.contragredient)
  have hfac : ∀ i, IsAdmissible (fac i).representation :=
    Fin.cases hA (Fin.cases hB finZeroElim)
  let e := Classical.choice (TwoFactorCommutativity.productSmoothDual F T K
    (fun i => (fac i).representation) hfac)
  let eFac :
      (T.normalizedProductInduced K
        (fun i => smoothContragredient (fac i).representation)).Equiv Q.representation :=
    T.normalizedProductInducedEquiv K
      (Fin.cases (Representation.Equiv.refl _)
        (Fin.cases (Representation.Equiv.refl _) finZeroElim))
  exact SmoothRep.mkIso (A := P.contragredient) (B := Q) (e.symm.trans eFac)

/-- Smooth duality reverses the adjacent class relation: the dual of the
lower factor is the unit positive twist of the dual of the upper factor. -/
theorem dualRep_adjacent_reverse {d : ℕ} :
    letI := T.topology
    ∀ (B A : SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := d)),
      A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
      (CuspidalProductContragredient.dualRep T B).isoClass =
        T.supercuspidalClassRealPowerTwist d 1
          (CuspidalProductContragredient.dualRep T A).isoClass := by
  let := T.topology
  intro B A hAB
  have hdual := congrArg
    (T.supercuspidalClassContragredient GeneralLinear.supercuspidalContragredient.{uF,uV} d) hAB
  rw [CuspidalProductContragredient.classContragredient_realPowerTwist] at hdual
  change (CuspidalProductContragredient.dualRep T A).isoClass =
    T.supercuspidalClassRealPowerTwist d (-1)
      (CuspidalProductContragredient.dualRep T B).isoClass at hdual
  rw [hdual, T.supercuspidalClassRealPowerTwist_add]
  simp only [add_neg_cancel, T.supercuspidalClassRealPowerTwist_zero]

end Langlands.CuspidalSupport

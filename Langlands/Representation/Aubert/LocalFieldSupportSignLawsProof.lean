import Langlands.Representation.Aubert.LocalFieldSupportSignLawsStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.ProductConstituentSupportProof
import Langlands.Representation.Aubert.ActualFixedFactorVector

/-! Support addition and the Jordan–Hölder comparison give the sign laws. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped MonoidAlgebra
open scoped DirectSum

namespace Langlands.Aubert.LocalFieldGraded

open GeneralLinear SmoothRep VirtualRepresentation
open AllFieldBZ.LocalFieldPackage.TopologicalData
open SmoothRep.IrreducibleGrothendieckProof SmoothRep.IrreducibleOperator

universe uF uV uM

variable {K : AllFieldBZ.LocalFieldPackage.{uF}} (T : K.TopologicalData)

/-- Maps from the homogeneous exact Grothendieck group are determined
by the actual irreducible classes. -/
theorem ext_irreducible {n : ℕ} {M : Type uM} [AddCommGroup M] [Module ℤ M]
    {L R : (letI := T.topology; FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier) →ₗ[ℤ] M}
    (h : letI := T.topology
      ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n K.Carrier))
        (hA : A.IsIrreducible),
        L (finiteLengthClass n K.Carrier A (hasFiniteLength_of_isIrreducible hA)) =
          R (finiteLengthClass n K.Carrier A (hasFiniteLength_of_isIrreducible hA))) : L = R := by
  let := T.topology
  let realize := SmoothRep.realizeIrreducibles.{0, uF, max uF uV} ℂ (GeneralLinear n K.Carrier)
  have he : L.comp realize = R.comp realize := by
    apply integral_hom_ext
    intro c
    obtain ⟨A, hA, rfl⟩ := IrreducibleIsoClass.exists_eq c
    change L (SmoothRep.realizeIrreducibles ℂ _ (generator (irreducibleIsoClass A hA))) =
      R (SmoothRep.realizeIrreducibles ℂ _ (generator (irreducibleIsoClass A hA)))
    rw [realizeIrreducibles_generator_irreducibleIsoClass A hA (hasFiniteLength_of_isIrreducible hA)]
    exact h A hA
  apply LinearMap.ext
  intro x
  have hx : realize (factorMap x) = x := LinearMap.congr_fun realize_comp_factorMap x
  have he' := LinearMap.congr_fun he (factorMap x)
  simpa only [LinearMap.comp_apply, hx] using he'

/-- Adjustment is precomposition by the support sign. -/
theorem adjust_comp (n : ℕ) :
    letI := T.topology
    ∀ D : FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier →ₗ[ℤ]
        FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier,
      adjustOperator T n D = D.comp (adjustOperator T n LinearMap.id) := by
  let := T.topology
  intro D
  apply ext_irreducible T
  intro A hA
  simp only [LinearMap.comp_apply, adjustOperator_irreducible, LinearMap.id_apply, map_zsmul]

/-- The homogeneous support sign squares to the identity. -/
theorem sign_square (n : ℕ) :
    letI := T.topology
    (adjustOperator.{uF, uV} T n LinearMap.id).comp (adjustOperator T n LinearMap.id) =
      LinearMap.id := by
  let := T.topology
  apply ext_irreducible T
  intro A hA
  simp only [LinearMap.comp_apply, adjustOperator_irreducible, LinearMap.id_apply, map_zsmul,
    smul_smul]
  have hs : supportSign T n (irreducibleIsoClass A hA) ^ 2 = 1 := by
    rw [supportSign, ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [← pow_two, hs, one_smul]

private theorem sign_rankZero :
    letI := T.topology
    adjustOperator.{uF, uV} T 0 LinearMap.id = LinearMap.id := by
  let := T.topology
  apply ext_irreducible T
  intro A hA
  simp only [adjustOperator_irreducible, LinearMap.id_apply, supportSign_rankZero, one_smul]

private theorem support_card_le {n : ℕ} :
    letI := T.topology
    ∀ {A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n K.Carrier)}
      {s : Multiset (CuspidalDatum.{max uF uV, uF} T)},
      IsSupercuspidalSupport A s → s.card ≤ n := by
  let := T.topology
  rintro A s ⟨k, ρ, rfl, hρ, -⟩
  simpa using (T.cuspidalShape ρ hρ).length_le

private theorem binary_constituent_sign {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a K.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier))
      (hA : A.IsIrreducible) (hB : B.IsIrreducible)
      (P : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) K.Carrier))
      (hP : P.IsIrreducible),
      IsSubquotient P ((T.binaryNormalizedProductFunctor a b).obj (A, B)) →
      supportSign T (a + b) (irreducibleIsoClass P hP) =
        supportSign T a (irreducibleIsoClass A hA) * supportSign T b (irreducibleIsoClass B hB) := by
  let := T.topology
  intro A B hA hB P hP hsub
  obtain ⟨k, ρ, hρ⟩ := AllFieldBZ.glSupercuspidalEmbedding.{max uF uV, uF} K T a ha A hA
  obtain ⟨l, σ, hσ⟩ := AllFieldBZ.glSupercuspidalEmbedding.{max uF uV, uF} K T b hb B hB
  let s : Multiset (CuspidalDatum.{max uF uV, uF} T) := List.ofFn ρ
  let t : Multiset (CuspidalDatum.{max uF uV, uF} T) := List.ofFn σ
  have hs : IsSupercuspidalSupport A s := ⟨k, ρ, rfl, hρ.isCuspidalConstituent⟩
  have ht : IsSupercuspidalSupport B t := ⟨l, σ, rfl, hσ.isCuspidalConstituent⟩
  let shape := BlockShape.binary a b ha hb
  let factors := (T.binaryPairFamilyFunctor ha hb).obj (A, B)
  let supports : Fin shape.length → Multiset (CuspidalDatum.{max uF uV, uF} T) :=
    Fin.cases s (fun _ => t)
  have hsup : ∀ i, IsSupercuspidalSupport (factors i) (supports i) := by
    intro i
    fin_cases i
    · exact hs
    · exact ht
  have hp' := AllFieldBZ.CuspidalSupport.productConstituentSupport.{uF, max uF uV}
    T (a + b) shape factors supports hsup P hP
    (hsub.of_iso_right ((T.binaryNormalizedProductPositiveIso ha hb).app (A, B)))
  have hp : IsSupercuspidalSupport P (s + t) := by
    change IsSupercuspidalSupport P (∑ i : Fin 2, supports i) at hp'
    rw [Fin.sum_univ_two] at hp'
    exact hp'
  have hsle := support_card_le T hs
  have htle := support_card_le T ht
  rw [supportSign_of_support T P hP _ hp, supportSign_of_support T A hA _ hs,
    supportSign_of_support T B hB _ ht, Multiset.card_add, ← pow_add]
  congr 1
  omega

/-- If all actual constituents have the same support sign, the sign
operator scales the class by that sign. -/
theorem sign_of_constituents {n : ℕ} :
    letI := T.topology
    ∀ (M : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n K.Carrier))
      (hM : M.HasFiniteLength) (s : ℤ),
      (∀ (P : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n K.Carrier))
        (hP : P.IsIrreducible), IsSubquotient P M →
          supportSign T n (irreducibleIsoClass P hP) = s) →
      adjustOperator T n LinearMap.id (finiteLengthClass n K.Carrier M hM) =
        s • finiteLengthClass n K.Carrier M hM := by
  let := T.topology
  intro M hM s hs
  let v := compositionFactors ⟨M, hM⟩
  have hreal : realizeIrreducibles ℂ (GeneralLinear n K.Carrier) v =
      finiteLengthClass n K.Carrier M hM := by
    change realizeIrreducibles ℂ (GeneralLinear n K.Carrier) (compositionFactors ⟨M, hM⟩) = _
    rw [← factorMap_ofRepresentation M hM]
    exact LinearMap.congr_fun realize_comp_factorMap _
  let sign := adjustOperator.{uF, uV} T n LinearMap.id
  let scale := s • (LinearMap.id : FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier →ₗ[ℤ] _)
  suffices h : sign (SmoothRep.realizeIrreducibles ℂ _ v) =
      scale (SmoothRep.realizeIrreducibles ℂ _ v) by
    simpa only [hreal, scale, sign, LinearMap.smul_apply, LinearMap.id_apply] using h
  rw [← Finsupp.sum_single v]
  simp only [map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  obtain ⟨P, hP, rfl⟩ := IrreducibleIsoClass.exists_eq c
  have hsub := (mem_support_compositionFactors_iff_isSubquotient ⟨M, hM⟩ P hP).mp hc
  have hsingle : Finsupp.single (irreducibleIsoClass P hP) (v (irreducibleIsoClass P hP)) =
      v (irreducibleIsoClass P hP) • generator (irreducibleIsoClass P hP) := by
    simp [generator]
  simp only [hsingle, map_zsmul,
    realizeIrreducibles_generator_irreducibleIsoClass P hP (hasFiniteLength_of_isIrreducible hP),
    LinearMap.smul_apply, LinearMap.id_apply, sign, scale]
  have hadj := adjustOperator_irreducible.{uF, uV} T n LinearMap.id P hP
    (hasFiniteLength_of_isIrreducible hP)
  rw [hs P hP hsub, LinearMap.id_apply] at hadj
  exact congrArg (v (irreducibleIsoClass P hP) • ·) hadj

private theorem sign_binary_positive (h : LocalFieldBinaryProductExactLengthStatement.{uF, uV})
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (x : FiniteLengthGrothendieckGroup.{uV, uF} a K.Carrier)
      (y : FiniteLengthGrothendieckGroup.{uV, uF} b K.Carrier),
      adjustOperator T (a + b) LinearMap.id (binaryProduct T h a b x y) =
        binaryProduct T h a b (adjustOperator T a LinearMap.id x)
          (adjustOperator T b LinearMap.id y) := by
  let := T.topology
  intro x y
  let s n := adjustOperator.{uF, uV} T n LinearMap.id
  let p := binaryProduct T h a b
  refine LinearMap.congr_fun (ext_irreducible T (L := (s (a + b)).comp (p.flip y))
    (R := (p.flip (s b y)).comp (s a)) ?_) x
  intro A hA
  let xA := finiteLengthClass a K.Carrier A (hasFiniteLength_of_isIrreducible hA)
  change s (a + b) (p xA y) = p (s a xA) (s b y)
  refine LinearMap.congr_fun (ext_irreducible T (L := (s (a + b)).comp (p xA))
    (R := (p (s a xA)).comp (s b)) ?_) y
  intro B hB
  let hAL := hasFiniteLength_of_isIrreducible hA
  let hBL := hasFiniteLength_of_isIrreducible hB
  let xB := finiteLengthClass b K.Carrier B hBL
  let P := (T.binaryNormalizedProductFunctor a b).obj (A, B)
  let hPL : P.HasFiniteLength := (h K.Carrier T a b).1 A B hAL hBL
  have hp : p xA xB = finiteLengthClass (a + b) K.Carrier P hPL :=
    binaryProduct_objects T h a b ⟨A, hAL⟩ ⟨B, hBL⟩
  let sA := supportSign T a (irreducibleIsoClass A hA)
  let sB := supportSign T b (irreducibleIsoClass B hB)
  change s (a + b) (p xA xB) = p (s a xA) (s b xB)
  have hA' : s a xA = sA • xA := adjustOperator_irreducible T a LinearMap.id A hA hAL
  have hB' : s b xB = sB • xB := adjustOperator_irreducible T b LinearMap.id B hB hBL
  calc
    s (a + b) (p xA xB) = (sA * sB) • p xA xB := by
      rw [hp]
      exact sign_of_constituents T P hPL (sA * sB) (binary_constituent_sign T ha hb A B hA hB)
    _ = p (s a xA) (s b xB) := by
      rw [hA', hB', LinearMap.map_smul₂, map_smul, smul_smul]

/-! ### The rank-zero factors -/

section RankZero

open SmoothRep.FiniteLengthGrothendieckGroup

/-- Every irreducible smooth representation of the trivial group `GL₀(F)`
is equivalent to the actual trivial line. -/
private theorem rankZero_equiv_unit :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 K.Carrier)),
      A.IsIrreducible →
        Nonempty (A.representation.Equiv (unitObject.{uF, uV} T).representation) := by
  let := T.topology
  intro A hA
  have : Representation.IsIrreducible A.representation := hA
  have : Subsingleton (GeneralLinear 0 K.Carrier) := subsingleton_of_rank_eq_zero rfl
  have : Nontrivial A :=
    IsSimpleModule.nontrivial ℂ[GeneralLinear 0 K.Carrier] A.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  let f : (Representation.trivial ℂ (GeneralLinear 0 K.Carrier) ℂ).IntertwiningMap
      A.representation :=
    { toLinearMap := LinearMap.toSpanSingleton ℂ A v
      isIntertwining' := by
        intro g
        rw [Subsingleton.elim g 1, map_one, map_one]
        rfl }
  have hf : f ≠ 0 := by
    intro hz
    apply hv
    simpa [f] using congrArg (fun q => q 1) hz
  let e := f.ofBijective ⟨smul_left_injective ℂ hv,
    (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf⟩
  let eU : (Representation.trivial ℂ (GeneralLinear 0 K.Carrier) ℂ).Equiv
      (unitObject.{uF, uV} T).representation :=
    Representation.Equiv.mk (ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm (fun _ => rfl)
  exact ⟨e.symm.trans eU⟩

/-- Every exact class in rank zero is an integer multiple of the class of
the trivial line. -/
private theorem rankZero_eq_smul_unit :
    letI := T.topology
    ∀ x : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} 0 K.Carrier,
      ∃ k : ℤ, k • unit T = inclusion T 0 x := by
  let := T.topology
  intro x
  obtain ⟨f, rfl⟩ := (SmoothRep.irreducibleGrothendieckStatement.{0, uF, max uF uV} ℂ
    (GeneralLinear 0 K.Carrier)).2 x
  induction f using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add f g hf hg =>
    obtain ⟨k, hk⟩ := hf
    obtain ⟨l, hl⟩ := hg
    exact ⟨k + l, by rw [map_add, map_add, add_smul, hk, hl]⟩
  | single c k =>
    obtain ⟨A, hA, rfl⟩ := IrreducibleIsoClass.exists_eq c
    have hs : Finsupp.single (irreducibleIsoClass A hA) k =
        k • generator (irreducibleIsoClass A hA) := by
      simp [generator]
    obtain ⟨e⟩ := rankZero_equiv_unit.{uF, uV} T A hA
    refine ⟨k, ?_⟩
    rw [hs, map_zsmul, map_zsmul,
      realizeIrreducibles_generator_irreducibleIsoClass A hA (hasFiniteLength_of_isIrreducible hA),
      ofRepresentation_eq_of_equiv _ (unitObject_hasFiniteLength T) e]
    rfl

/-- Equivalent representations in equal ranks have the same graded class. -/
private theorem inclusion_eq_of_rank_equiv {a b : ℕ} (e : a = b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a K.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier))
      (hA : A.HasFiniteLength) (hB : B.HasFiniteLength),
      A.representation.Equiv (B.representation.comp
        (GeneralLinear.reindex (R := K.Carrier) (finCongr e)).toMonoidHom) →
      inclusion T a (ofRepresentation A hA) = inclusion T b (ofRepresentation B hB) := by
  let := T.topology
  subst b
  intro A B hA hB E
  apply congrArg (inclusion T a)
  apply ofRepresentation_eq_of_equiv hA hB
  refine E.trans (Representation.Equiv.mk (LinearEquiv.refl ℂ B) fun g => ?_)
  ext v
  change B.representation (GeneralLinear.reindex (R := K.Carrier) (finCongr rfl) g) v =
    B.representation g v
  rw [GeneralLinear.reindex_finCongr_rfl]
  rfl

/-- The trivial line is a left unit for the graded product. -/
private theorem unit_mul (h : LocalFieldBinaryProductExactLengthStatement.{uF, uV})
    (x : GradedGrothendieckGroup.{uF, uV} T) : multiplication T h (unit T) x = x := by
  let := T.topology
  let U := (⟨unitObject T, unitObject_hasFiniteLength T⟩ :
    FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear 0 K.Carrier))
  have hUnit : multiplication T h (unit T) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro b
    refine hom_ext_object ℂ (GeneralLinear b K.Carrier)
      (M := GradedGrothendieckGroup.{uF, uV} T)
      (l₁ := (multiplication T h (unit T)).comp (inclusion T b))
      (l₂ := inclusion T b) fun B => ?_
    change multiplication T h (inclusion T 0 (ofObject U)) (inclusion T b (ofObject B)) = _
    rw [multiplication_homogeneous, binaryProduct_objects]
    apply inclusion_eq_of_rank_equiv T (Nat.zero_add b)
    exact (binaryLeftZeroTensorEquiv T rfl (U.val, B.val)).trans
      (BinaryTensor.compEquiv (BinaryTensor.secondFactorUnitEquiv B.val.representation) _)
  exact LinearMap.congr_fun hUnit x

/-- The trivial line is a right unit for the graded product. -/
private theorem mul_unit (h : LocalFieldBinaryProductExactLengthStatement.{uF, uV})
    (x : GradedGrothendieckGroup.{uF, uV} T) : multiplication T h x (unit T) = x := by
  let := T.topology
  let U := (⟨unitObject T, unitObject_hasFiniteLength T⟩ :
    FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear 0 K.Carrier))
  have hUnit : (multiplication T h).flip (unit T) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro a
    refine hom_ext_object ℂ (GeneralLinear a K.Carrier)
      (M := GradedGrothendieckGroup.{uF, uV} T)
      (l₁ := ((multiplication T h).flip (unit T)).comp (inclusion T a))
      (l₂ := inclusion T a) fun A => ?_
    change multiplication T h (inclusion T a (ofObject A)) (inclusion T 0 (ofObject U)) = _
    rw [multiplication_homogeneous, binaryProduct_objects]
    apply inclusion_eq_of_rank_equiv T (Nat.add_zero a)
    exact (binaryRightZeroTensorEquiv T rfl (A.val, U.val)).trans
      (BinaryTensor.compEquiv (BinaryTensor.firstFactorUnitEquiv A.val.representation) _)
  exact LinearMap.congr_fun hUnit x

end RankZero

private def gradedSign : GradedGrothendieckGroup.{uF, uV} T →ₗ[ℤ]
    GradedGrothendieckGroup.{uF, uV} T :=
  let := T.topology
  DirectSum.toModule ℤ ℕ _ (fun n => (inclusion T n).comp (adjustOperator T n LinearMap.id))

private theorem gradedSign_inclusion (n : ℕ) :
    letI := T.topology
    ∀ x : FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier,
      gradedSign T (inclusion T n x) = inclusion T n (adjustOperator T n LinearMap.id x) := by
  let := T.topology
  intro x
  simp only [gradedSign, inclusion, DirectSum.toModule_lof, LinearMap.comp_apply]

private theorem gradedSign_unit : gradedSign.{uF, uV} T (unit T) = unit T := by
  let := T.topology
  unfold unit
  rw [gradedSign_inclusion, sign_rankZero, LinearMap.id_apply]

private theorem gradedSign_multiplication (h : LocalFieldBinaryProductExactLengthStatement.{uF, uV})
    (x y : GradedGrothendieckGroup.{uF, uV} T) :
    gradedSign T (multiplication T h x y) = multiplication T h (gradedSign T x) (gradedSign T y) := by
  let := T.topology
  let S := gradedSign.{uF, uV} T
  let m := multiplication T h
  have hx : S.comp (m.flip y) = (m.flip (S y)).comp S := by
    apply DirectSum.linearMap_ext
    intro a
    apply LinearMap.ext
    intro xa
    let i := inclusion T a xa
    change S (m i y) = m (S i) (S y)
    have hy : S.comp (m i) = (m (S i)).comp S := by
      apply DirectSum.linearMap_ext
      intro b
      apply LinearMap.ext
      intro yb
      change S (m (inclusion T a xa) (inclusion T b yb)) =
        m (S (inclusion T a xa)) (S (inclusion T b yb))
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · obtain ⟨k, hk⟩ := rankZero_eq_smul_unit T xa
        rw [← hk]
        simp only [m, S, map_smul, LinearMap.smul_apply, gradedSign_unit, unit_mul]
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · obtain ⟨k, hk⟩ := rankZero_eq_smul_unit T yb
        rw [← hk]
        simp only [m, S, map_smul, gradedSign_unit, mul_unit]
      simp only [m, S, multiplication_homogeneous, gradedSign_inclusion,
        sign_binary_positive T h ha hb]
    exact LinearMap.congr_fun hy y
  exact LinearMap.congr_fun hx x

/-- The all-field sign twist is an involutive multiplicative adjustment. -/
theorem localFieldSupportSignLaws : LocalFieldSupportSignLawsStatement.{uF, uV} := by
  intro K T h
  let := T.topology
  exact ⟨adjust_comp T, fun n x => LinearMap.congr_fun (sign_square T n) x,
    gradedSign_multiplication T h, gradedSign_unit T⟩

end Langlands.Aubert.LocalFieldGraded

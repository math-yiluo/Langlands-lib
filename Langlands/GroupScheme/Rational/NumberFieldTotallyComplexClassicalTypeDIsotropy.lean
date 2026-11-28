import Langlands.GroupScheme.Quaternionic.QuaternionicSkewIsometryTransport
import Langlands.GroupScheme.Quaternionic.SplitSkewNonsingularIsotropy
import Langlands.GroupScheme.Quaternionic.TorusWittBound
import Langlands.GroupScheme.Quaternionic.UnitaryGramFieldExtension
import Langlands.GroupScheme.Rational.CentralIsogenySplitRank
import Langlands.GroupScheme.Rational.LocalTypeDIsotropy
import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexTypeDSpinIsotropy
import Langlands.GroupScheme.CentralIsogeny.BaseChange

/-! # Totally complex isotropy of the classical forms of type D -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix NumberField
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Quaternionic
open FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2300000
set_option synthInstance.maxHeartbeats 100000

private theorem exists_isotropic_row_of_isotropic_unitaryGroup
    {K D : Type u} [Field K] [Infinite K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    {J : Type} [Fintype J] [DecidableEq J] (τ : FirstKindInvolution K D) (H : Matrix J J D)
    (hU : ¬ IsAnisotropic (τ.unitaryGroup H)) :
    ∃ (x : J → D) (j : J), IsUnit (x j) ∧ τ.matrixSesqBilin H x x = 0 := by
  classical
  obtain ⟨I, hFin, i, hi, hI⟩ : ∃ (I : Type u) (_ : Finite I)
      (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ τ.unitaryGroup H),
        IsClosedSubgroup i ∧ Nonempty I := by
    by_contra h
    apply hU
    apply isAnisotropic_iff.mpr
    intro I hFinite i hi
    exact not_nonempty_iff.mp (fun hn => h ⟨I, hFinite, i, hi, hn⟩)
  let : Fintype I := Fintype.ofFinite I
  let A := Matrix J J D
  let b := Module.finBasis K A
  let j := i ≫ τ.unitaryGroupι H
  let ρ := (FiniteAlgebraUnits.rightRegularRepresentation b).restrict j
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion (τ.unitaryGroupι H).hom.hom.left := τ.isClosedSubgroup_unitaryGroupι H
  let : Mono (FiniteAlgebraUnits.rightRegularRepresentation b).hom.hom.left :=
    FiniteAlgebraUnits.mono_rightRegularRepresentation_left b
  let S := splitTorus (Spec (CommRingCat.of K)) I
  have hr : Mono ((𝟙 S : S ⟶ S).hom.hom ≫ ρ.hom.hom).left := by
    change Mono ((i.hom.hom.left ≫ (τ.unitaryGroupι H).hom.hom.left) ≫
      (FiniteAlgebraUnits.rightRegularRepresentation b).hom.hom.left)
    infer_instance
  let w := CharacterRestrictionFiniteIndex.weight ρ I (𝟙 _)
  have hcl : AddSubgroup.closure {m | w m ≠ 0} = ⊤ :=
    CharacterRestrictionFiniteIndex.closure_weights_eq_top ρ I (𝟙 _) hr
  obtain ⟨m, hm, hm0⟩ : ∃ m : I → ℤ, w m ≠ 0 ∧ m ≠ 0 := by
    by_contra! h
    have hsub : AddSubgroup.closure {m | w m ≠ 0} ≤ ⊥ := by
      rw [AddSubgroup.closure_le]
      exact fun m hm => AddSubgroup.mem_bot.mpr (h m hm)
    rw [hcl] at hsub
    obtain ⟨i₀⟩ := hI
    have heq := AddSubgroup.mem_bot.mp (hsub (show (1 : I → ℤ) ∈ (⊤ : AddSubgroup (I → ℤ)) from trivial))
    exact one_ne_zero (congrFun heq i₀)
  have hweight (a b : Fin (Module.finrank K A)) :
      w m a b = GeneralLinear.CocharacterDiagonal.coefficientColumn I ρ m b a := by
    simp [w, CharacterRestrictionFiniteIndex.weight, CharacterRestrictionFiniteIndex.universalMatrix,
      GeneralLinear.CocharacterDiagonal.coefficientColumn, GeneralLinear.CocharacterDiagonal.universalMatrix]
    rfl
  obtain ⟨c, hc⟩ : ∃ c, GeneralLinear.CocharacterDiagonal.coefficientColumn I ρ m c ≠ 0 := by
    by_contra! h
    apply hm
    ext a b
    rw [hweight, h b]
    rfl
  let P := FirstKindInvolution.torusInverseUnitMatrices I j
  let χ := fun t : I → Kˣ => (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : K)
  have hP (t : I → Kˣ) : P t * H * τ.matrix J (P t) = H := by
    simpa only [P, FirstKindInvolution.torusInverseUnitMatrices, j, FirstKindInvolution.unitaryGroupι,
      Grp.comp_hom_hom, Category.assoc] using
      IsometryCut.baseAffineUnit_inv_isometry (τ.matrix J) H
        ((splitTorus.algebraPointsEquiv I K).symm t ≫ i.hom.hom)
  have hm2 : m + m ≠ 0 := by
    intro h
    apply hm0
    funext i
    have h' := congrFun h i
    change m i + m i = 0 at h'
    change m i = 0
    omega
  have hχ : ∃ t, χ t * χ t ≠ 1 := splitTorus.exists_exponentValue_mul_ne_one (K := K) hm2
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FirstKindInvolution.commonWeightSpace_ne_bot_of_coefficientColumn I j hc)
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := not_forall.mp (fun h => hx0 (funext h))
  exact ⟨x, k, isUnit_iff_ne_zero.mpr hk, by
    rw [FirstKindInvolution.matrixSesqBilin_eq_sesqForm]
    exact τ.sesqForm_commonWeightSpace_eq_zero hP hχ hx hx⟩

section NumberField

variable {F D : Type u} [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)
  {n : ℕ} (hn : 4 ≤ n) (q : σ.QuadraticForms (Fin n)) (hq : σ.IsNondegenerateQuadratic q)

local notation "τ" => σ.quaternionConjugation hdim hsym
local notation "H" => σ.conjugationSkewGram q hdim hsym

include hn hq in
private theorem exists_skew_row_of_split_chart {K : Type u} [Field K] [Algebra F K]
    (e : K ⊗[F] D ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)
    (his : ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (Q : QuadraticForm K V), 4 < Module.finrank K V → ∃ z, z ≠ 0 ∧ Q z = 0) :
    let M := coefficientEquiv F D K ((1 : K) ⊗ₜ[F] H)
    ∃ (x : Fin n → K ⊗[F] D) (i : Fin n), IsUnit (x i) ∧ ((τ).baseChange K).matrixSesqBilin M x x = 0 := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let M := coefficientEquiv F D K ((1 : K) ⊗ₜ[F] H)
  let i : Fin n := ⟨0, by omega⟩
  have hH := σ.isAntihermitian_conjugationSkewGram q hdim hsym
  have hunit := σ.isUnit_conjugationSkewGram q hdim hsym hq
  obtain ⟨x, hx, hz⟩ := exists_isotropic_row_unit_of_splitSkew e ((τ).baseChange K)
    (σ.splitQuaternionConjugation_mul_gramTwo hdim hsym e) two_ne_zero his i (by simpa using hn)
    ((τ).matrix_coefficientEquiv_tmul_eq_neg (R := K) hH.1)
    (FirstKindInvolution.isUnit_coefficientEquiv_tmul (R := K) hunit)
  exact ⟨x, i, hx, hz⟩

omit hn hq [Algebra.IsCentral F D] in
private theorem exists_skew_row_of_division {K : Type u} [Field K] [Algebra F K]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (π : G ⟶ σ.isometryGroup q) (hπ : σ.IsSpinCover q π)
    (hdom : IsDomain (K ⊗[F] D))
    (hG : ¬ IsAnisotropic ((GroupScheme.baseChange (algebraBaseMap F K)).obj G)) :
    let M := coefficientEquiv F D K ((1 : K) ⊗ₜ[F] H)
    ∃ (x : Fin n → K ⊗[F] D) (i : Fin n), IsUnit (x i) ∧ ((τ).baseChange K).matrixSesqBilin M x x = 0 := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let : IsDomain (K ⊗[F] D) := hdom
  let : DivisionRing (K ⊗[F] D) := divisionRingOfFiniteDimensional K (K ⊗[F] D)
  let : Smooth (σ.isometryGroup q).X.hom := hπ.smooth
  obtain ⟨p, hp, _⟩ := hπ.exists_centralIsogeny
  let b := algebraBaseMap F K
  let B := GroupScheme.baseChange b
  let U := σ.isometryGroup q
  let U₀ := identityComponent U
  let M := coefficientEquiv F D K ((1 : K) ⊗ₜ[F] H)
  obtain ⟨E⟩ := FirstKindInvolution.nonempty_unitaryGramFieldExtensionIso F D K (Fin n) τ H
  let E' : B.obj U ≅ ((τ).baseChange K).unitaryGroup M :=
    B.mapIso (σ.conjugationSkewIsometryIso q hdim hsym) ≪≫ E
  let j := B.map (identityComponentι U) ≫ E'.hom
  have hj : IsClosedSubgroup j := ((IdentityComponent.isClosedSubgroup_identityComponentι U).baseChange b).comp_iso E'
  let : IsAffineHom (B.obj G).X.hom := MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›
  let : IsAffineHom (B.obj U₀).X.hom :=
    MorphismProperty.pullback_snd _ _ (IdentityComponent.isAffineHom_identityComponent U)
  have he := (hp.baseChange b).splitRank_eq
  have hr := splitRank_le_of_isClosedSubgroup j hj
  apply exists_isotropic_row_of_isotropic_unitaryGroup ((τ).baseChange K) M
  intro h
  exact hG (nonpos_iff_eq_zero.mp (he.le.trans (hr.trans h.le)))

include hn hq in
private theorem isLocallyNonsingularIsotropic_typeD (hF : IsTotallyComplex F)
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin n)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (habs : IsAbsolutelyAlmostSimple G) (π : G ⟶ σ.isometryGroup q) (hπ : σ.IsSpinCover q π) :
    (τ).IsLocallyNonsingularIsotropic H := by
  intro v
  rcases v with v | v
  · let K := v.Completion
    let eK := InfinitePlace.Completion.ringEquivComplexOfIsComplex (hF.isComplex v)
    let : IsAlgClosed K := ⟨fun f => Polynomial.Splits.of_splits_map
      eK.toRingHom (IsAlgClosed.splits _) (fun x _ => eK.surjective x)⟩
    have he := Langlands.CentralSimple.exists_matrix_chart_reducedDegree F D K
    rw [Langlands.CentralSimple.reducedDegree, hdim, show Nat.sqrt 4 = 2 from Nat.sqrt_eq 2] at he
    obtain ⟨chart⟩ := he
    exact exists_skew_row_of_split_chart σ hdim hsym hn q hq (K := K) chart
      (fun _ _ _ _ Q hdimQ => OrthogonalMatrix.exists_isotropic (by omega) Q)
  · let K := Global.FiniteCompletion F v
    let : ValuativeRel K := Global.FiniteCompletion.valuativeRel v
    let : IsNonarchimedeanLocalField K := Global.FiniteCompletion.isNonarchimedeanLocalField v
    rcases quaternionCoefficientDichotomy F D K hdim with hdom | he
    · exact exists_skew_row_of_division σ hdim hsym q (K := K) π hπ hdom
        (localTypeDIsotropy F K G d habs n e hn hD)
    · obtain ⟨chart⟩ := he
      refine exists_skew_row_of_split_chart σ hdim hsym hn q hq (K := K) chart (fun V _ _ _ Q hdimQ => ?_)
      apply Q.not_anisotropic_iff_exists.mp
      intro h
      exact (not_lt_of_ge (Langlands.localQuadraticAnisotropicDimensionBound K V Q h)) hdimQ

end NumberField

/-- The simply connected classical forms of type D of rank at least four
over a totally complex number field have positive split rank. -/
def NumberFieldTotallyComplexClassicalTypeDIsotropyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ) (e : d.Vertex ≃ Fin n),
      4 ≤ n → IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) →
      (∀ (g : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex),
        (e a).val + 2 < n → d.star g a = a) →
      ¬ IsAnisotropic G

theorem numberFieldTotallyComplexClassicalTypeDIsotropy :
    NumberFieldTotallyComplexClassicalTypeDIsotropyStatement.{u} := by
  intro F _ _ hF G _ _ d n e hn hsc habs hD hstar
  refine numberFieldTotallyComplexTypeDSpinIsotropyReduction F hF G d n e hn hsc habs hD hstar
    (fun D _ _ _ _ σ hdim hsym q hq π hπ => ?_)
  exact isLocallyNonsingularIsotropic_typeD σ hdim hsym hn q hq hF d e hD habs π hπ

end Langlands.GroupScheme

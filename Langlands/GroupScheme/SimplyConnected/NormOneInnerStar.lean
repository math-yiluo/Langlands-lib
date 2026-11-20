import Langlands.GroupScheme.SimplyConnected.NormOneAbsolutePinning
import Langlands.GroupScheme.SimplyConnected.NormOneTitsAlgebra
import Langlands.GroupScheme.Rational.SpecialLinearNumberedWeightTransport
import Langlands.LinearAlgebra.RootDatumPathUniqueness

/-! # Triviality of the actual norm-one star action -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix TensorProduct

namespace Langlands.GroupScheme.CentralSimpleUnits

open Langlands.CentralSimple MatrixRepresentation SplitRepresentation TitsDescent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "F" => GroupScheme.baseChange (algebraBaseMap k K)

local instance : IsAffineHom ((F).obj G).X.hom := inferInstanceAs
  (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

private theorem starFixedWeight_of_twistIntertwiners
    (d : GaloisPinningData k K G) {n : ℕ}
    {ρ : MatrixRepresentation ((F).obj G) (Fin n)}
    {lam : characterLattice d.toSplitPinning.torus} (hρ : d.toSplitPinning.IsHighestWeight ρ lam)
    (hC : ∀ σ : K ≃ₐ[k] K, ∃ C : Matrix (Fin n) (Fin n) K,
      ρ.Intertwines (galoisTwist σ ρ) C ∧ Function.Bijective C.mulVecLin) :
    d.IsStarFixedWeight lam := by
  let p := d.toSplitPinning
  have hdim (σ : K ≃ₐ[k] K) (χ : characterLattice p.torus) :
      Module.finrank K (p.representationWeightSpace ρ ((d.starAction σ).val • χ)) =
        Module.finrank K (p.representationWeightSpace ρ χ) := by
    obtain ⟨C, hi, hb⟩ := hC σ
    obtain ⟨w, hw⟩ := d.exists_weyl_mul_galoisAction_eq_starAction σ
    rw [SplitPinning.finrank_representationWeightSpace_eq_of_intertwines hi hb,
      ← hw, mul_smul, d.finrank_representationWeightSpace_weyl _ w.val w.property,
      d.representationWeightSpace_galoisTwist_smul, finrank_galoisComap]
  have hle (σ : K ≃ₐ[k] K) : lam - (d.starAction σ).val • lam ∈ p.positiveRootMonoid := by
    apply hρ.2.2.2
    rw [← Submodule.one_le_finrank_iff, hdim, hρ.2.2.1]
  intro σ
  have hn := d.smul_mem_positiveRootMonoid (d.starAction σ).val (d.starAction σ).property (hle σ⁻¹)
  rw [smul_sub, map_inv] at hn
  change (d.starAction σ).val • lam - (d.starAction σ).val •
    ((d.starAction σ).val⁻¹ • lam) ∈ p.positiveRootMonoid at hn
  rw [smul_inv_smul] at hn
  exact p.eq_of_sub_mem_positiveRootMonoid hn (hle σ)

/-- An automorphism of the numbered type-A chain fixing its first vertex is the identity. -/
private theorem eq_id_of_cartanA_and_first {n : ℕ} (hn : 0 < n) (f : Equiv.Perm (Fin n))
    (hc : ∀ i j, CartanMatrix.A n (f i) (f j) = CartanMatrix.A n i j)
    (h0 : f ⟨0, hn⟩ = ⟨0, hn⟩) (i : Fin n) : f i = i := by
  have hstep (j : ℕ) (hj : j + 1 < n) :
      (f ⟨j, by omega⟩).val + 1 = (f ⟨j + 1, hj⟩).val ∨
        (f ⟨j + 1, hj⟩).val + 1 = (f ⟨j, by omega⟩).val := by
    have h := hc ⟨j, by omega⟩ ⟨j + 1, hj⟩
    have hne : (⟨j, by omega⟩ : Fin n) ≠ ⟨j + 1, hj⟩ := by
      intro h
      have hv := congrArg Fin.val h
      change j = j + 1 at hv
      omega
    have hentry : CartanMatrix.A n ⟨j, by omega⟩ ⟨j + 1, hj⟩ = -1 := by
      simp [CartanMatrix.A, Matrix.of_apply, hne]
    rw [hentry] at h
    by_contra hnadj
    simp [CartanMatrix.A, Matrix.of_apply, f.injective.ne hne, hnadj] at h
  rcases Langlands.LinearAlgebra.RootDatumPathWeights.walk_eq_id_or_rev f f.injective hstep
    with hid | hrev
  · exact Fin.ext (hid i)
  · have hz := hrev ⟨0, hn⟩
    rw [h0] at hz
    apply Fin.ext
    have hh := hrev i
    have hi := i.isLt
    change 0 = n - 1 - 0 at hz
    omega

variable (k K G) in
/-- Every actual split norm-one presentation has trivial star action on the supplied pinning. -/
def NormOneInnerStarStatement : Prop :=
  ∀ (d : GaloisPinningData k K G) (A : CSA.{u, u} k) (_ : G ≅ normOne k A)
    (_ : K ⊗[k] A ≃ₐ[K] Matrix (Fin (reducedDegree k A)) (Fin (reducedDegree k A)) K),
    d.IsInnerStarAction

/-- The column representation fixes the first fundamental weight under the star
 action. Its vertex is an endpoint of the type-A chain, so all vertices are fixed. -/
theorem normOneInnerStar : NormOneInnerStarStatement k K G := by
  classical
  intro d A model chart
  let p := d.toSplitPinning
  let E := (F).mapIso model ≪≫ Splitting.splittingIso k A chart
  let hG : IsSimplyConnected G := IsSimplyConnected.of_iso model (normOne_isSimplyConnected k A)
  let hspan := d.corootSpan_eq_top_of_simplyConnected hG
  by_cases hm : 2 ≤ reducedDegree k A
  · obtain ⟨number, hcartan, hw, _⟩ := p.numberedWeightsOfSpecialLinearIso hm E hspan
    let first := number.symm ⟨0, by omega⟩
    let ω := Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan first
    have hρ : p.IsHighestWeight (representationOn A chart model) ω := by
      simpa only [ω, first, E, representationOn, representation, Iso.trans_hom, Functor.mapIso_hom,
        restrict_comp] using hw
    have hfix := starFixedWeight_of_twistIntertwiners d hρ (fun σ => by
      let C := galoisConjugator chart σ
      exact ⟨C.val, intertwines_restrict_galoisTwist σ
        (column_intertwines_galoisTwist A chart σ) model.hom,
        (Matrix.GeneralLinearGroup.toLin C).toLinearEquiv.bijective⟩)
    intro σ v
    let a := (d.starAction σ).val
    let s := a.indexEquiv.subtypeEquiv (d.starAction σ).property
    let f := (number.symm.trans s).trans number
    have hfirst : s first = first := by
      have h := d.pairing_coroot_indexEquiv_of_fixed a (hfix σ) first.val
      change p.rootDatum.toLinearMap ω (p.rootDatum.coroot (s first).val) =
        p.rootDatum.toLinearMap ω (p.rootDatum.coroot first.val) at h
      dsimp only [ω] at h
      rw [Langlands.RootDatum.fundamentalWeightBasis_pairing,
        Langlands.RootDatum.fundamentalWeightBasis_pairing, ite_eq_left rfl] at h
      by_contra hn
      rw [ite_eq_right hn] at h
      norm_num at h
    have hcart (i j : Fin (reducedDegree k A - 1)) :
        CartanMatrix.A _ (f i) (f j) = CartanMatrix.A _ i j := by
      change CartanMatrix.A _ (number (s (number.symm i))) (number (s (number.symm j))) = _
      rw [← hcartan (s (number.symm i)) (s (number.symm j))]
      change p.rootDatum.pairing (a.indexEquiv (number.symm i).val)
        (a.indexEquiv (number.symm j).val) = _
      rw [a.toHom.pairing, hcartan, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hf0 : f ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
      change number (s first) = _
      rw [hfirst, Equiv.apply_symm_apply]
    have hfv := eq_id_of_cartanA_and_first (by omega) f hcart hf0 (number v)
    have hv : s v = v := by
      apply number.injective
      simpa only [f, Equiv.trans_apply, Equiv.symm_apply_apply] using hfv
    exact congrArg Subtype.val hv
  · have hdegree := reducedDegree_pos k A
    have h1 : reducedDegree k A = 1 := by omega
    have hempty {n : ℕ} (hn : n = 1)
        (J : (F).obj G ≅ SpecialLinear.groupScheme (Fin n) (CommRingCat.of K)) :
        IsEmpty p.base.support := by
      subst n
      obtain ⟨q, _, number, _⟩ := SpecialLinear.FinSucc.exists_splitPinning (n := 0) (k := K)
      obtain ⟨_, _, e, _, _, hb⟩ := p.exists_inner_comp_based q J
      exact ⟨fun v => Fin.elim0 (number (e.indexEquiv.subtypeEquiv hb v))⟩
    exact fun _ v => ((hempty h1 E).false v).elim

end Langlands.GroupScheme.CentralSimpleUnits

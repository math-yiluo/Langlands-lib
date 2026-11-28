import Langlands.LinearAlgebra.CartanE6BranchMarking
import Langlands.GroupScheme.SimplyConnected.TypeE6Opposition
import Langlands.GroupScheme.Reductive.TitsIndexRootRestriction
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter

/-! # The possible isotropic E6 marking with unmarked short arm -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators TensorProduct
open Langlands.LinearAlgebra.RationalSpan
open Langlands.CartanE6Root

namespace Langlands.GroupScheme

/-- For an actual simply connected E6 index with some distinguished vertex
and with the short arm unmarked, the distinguished vertices are exactly the
two long-arm endpoints. -/
def TypeE6UnmarkedBranchMarkingStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    IsSimplyConnected G → e.symm 1 ∉ d.distinguishedVertices →
    d.distinguishedVertices.Nonempty →
    ∀ a : d.Vertex, a ∈ d.distinguishedVertices ↔ e a = 0 ∨ e a = 5

open BranchMarking in
private theorem projection_sum {A : Type*} [AddCommGroup A]
    (p : BranchMarking) (a : Fin 6 → A) (c : Coordinates)
    (h₁ : a 1 = 0)
    (hends : p.endsMarked = false → a 0 = 0 ∧ a 5 = 0)
    (harms : p.innerArmMarked = false → a 2 = 0 ∧ a 4 = 0)
    (hcentral : p.centralMarked = false → a 3 = 0)
    (hstar : p.swapsArms = true → a 5 = a 0 ∧ a 4 = a 2) :
    ∑ j, p.project c j • a j = ∑ j, c j • a j := by
  obtain ⟨s, l, b, r⟩ := p
  cases s <;> cases l <;> cases b <;> cases r <;>
    simp_all [project, Fin.sum_univ_six, add_zsmul] <;> abel

open BranchMarking in
private theorem coordinate_sum (c : Coordinates) : ∑ j : Fin 6, c j • unit j = c := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply, mul_ite]

open BranchMarking in
private theorem integralReflections {J M N : Type*}
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing J ℚ M N) [P.IsCrystallographic] (p : BranchMarking)
    (v : Coordinates →+ M)
    (hunit : ∀ j, v (unit j) = 0 ∨ v (unit j) ∈ Set.range P.root)
    (hinj : ∀ x y : Coordinates,
      (∀ j, p.active j = false → x j = 0) → (∀ j, p.active j = false → y j = 0) →
      v x = v y → x = y)
    (hroots : ∀ c : Coordinates, (∀ j, p.active j = false → c j = 0) →
      (p.IsProjectedRoot c ↔ v c = 0 ∨ v c ∈ Set.range P.root)) :
    p.HasIntegralReflections := by
  classical
  intro i m hi hm hp
  have hu (z : ℤ) (j : Fin 6) (hj : p.active j = false) : (z • unit i) j = 0 := by
    have hne : j ≠ i := by rintro rfl; simp [hi] at hj
    simp [hne]
  obtain ⟨r, hr⟩ : v (m • unit i) ∈ Set.range P.root := by
    rcases (hroots _ (hu m)).mp hp with hz | hr
    · have heq := hinj _ 0 (hu m) (by simp) (hz.trans (map_zero v).symm)
      have := congrFun heq i
      simp at this
      omega
    · exact hr
  have hpairing (j : Fin 6) : ∃ n : ℤ, P.coroot' r (v (unit j)) = (n : ℚ) := by
    rcases hunit j with hz | ⟨b, hb⟩
    · exact ⟨0, by simp [hz]⟩
    · refine ⟨P.pairingIn ℤ b r, ?_⟩
      rw [← hb, P.root_coroot'_eq_pairing]
      exact (P.algebraMap_pairingIn ℤ b r).symm
  choose f hf using hpairing
  refine ⟨f, ?_, ?_⟩
  · have heq : (m : ℚ) * (f i : ℚ) = 2 := by
      calc
        (m : ℚ) * (f i : ℚ) = P.coroot' r (v (m • unit i)) := by
          rw [map_zsmul, map_zsmul, hf, zsmul_eq_mul]
        _ = 2 := by rw [← hr, P.root_coroot'_eq_pairing, P.pairing_same]
    exact_mod_cast heq
  · intro c hc
    have hsum : P.coroot' r (v c) = ((∑ j, c j * f j : ℤ) : ℚ) := by
      nth_rw 1 [← coordinate_sum c]
      simp only [map_sum, Int.cast_sum, Int.cast_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_zsmul, map_zsmul, hf, zsmul_eq_mul]
    let d := c - (m * ∑ j, c j * f j) • unit i
    have hd : ∀ j, p.active j = false → d j = 0 := by
      intro j hj
      change c j - ((m * ∑ l, c l * f l) • unit i) j = 0
      rw [hc.apply_eq_zero_of_inactive j hj, hu _ j hj, sub_zero]
    have hreflect : P.reflection r (v c) = v d := by
      rw [P.reflection_apply, hsum, hr, Int.cast_smul_eq_zsmul ℚ (∑ j, c j * f j)]
      simp only [d, map_sub, map_zsmul, smul_smul, mul_comm m]
    apply (hroots _ hd).mpr
    rw [← hreflect]
    rcases (hroots _ hc.apply_eq_zero_of_inactive).mp hc with hz | hroot
    · exact Or.inl (by simp [hz])
    · exact Or.inr (P.mapsTo_reflection_root r hroot)

set_option maxHeartbeats 1600000 in
/-- In a simply connected E6 Tits index with an unmarked short-arm vertex
and at least one marked vertex, exactly the two long-arm ends are marked. -/
theorem typeE6UnmarkedBranchMarking : TypeE6UnmarkedBranchMarkingStatement.{u} := by
  classical
  intro k _ G _ _ d e hE hsc hbranch hne
  let v := e.symm
  let a (j : Fin 6) : d.pinning.rootIndex := (v j).val
  let R (j : Fin 6) : characterLattice d.splitTorus := d.rootRestriction (a j)
  let τ := Langlands.CartanE6Root.symmetry
  let marks (j : Fin 6) : Prop := v j ∈ d.distinguishedVertices
  have hmark (j : Fin 6) : marks (τ j) ↔ marks j := by
    have heq : v (τ j) = d.opposition (v j) := by
      apply e.injective
      simpa [v, τ] using (d.opposition_eq_symmetry_of_E6 e hE hsc (v j)).symm
    change v (τ j) ∈ _ ↔ _
    rw [heq]
    exact d.opposition_mem_distinguished_iff (v j)
  have hstar (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
      (∀ j, d.star σ (v j) = v j) ∨ (∀ j, d.star σ (v j) = v (τ j)) := by
    let f (j : Fin 6) := e (d.star σ (v j))
    have hf (i j) : CartanMatrix.E 6 (f i) (f j) = CartanMatrix.E 6 i j := by
      rw [← hE, d.cartan_star, hE]
      simp [v]
    rcases Langlands.CartanE6Root.eq_id_or_symmetry_of_preserves f hf with hid | hsym
    · exact Or.inl fun j => e.injective (by simpa [f, v] using hid j)
    · exact Or.inr fun j => e.injective (by simpa [f, τ, v] using hsym j)
  let swaps : Prop :=
    ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k, ∀ j, d.star σ (v j) = v (τ j)
  let p : BranchMarking := ⟨decide swaps, decide (marks 0), decide (marks 2), decide (marks 3)⟩
  have hends : marks 5 ↔ marks 0 := hmark 0
  have harms : marks 4 ↔ marks 2 := hmark 2
  have hzero (j : Fin 6) (h : ¬ marks j) : R j = 0 :=
    not_ne_iff.mp h
  have hmarkedActive (j : Fin 6) (hj : p.active j = true) : marks j := by
    fin_cases j <;>
      simp_all [p, BranchMarking.active]
  have hres (i j : Fin 6) (hi : marks i) (hj : marks j) :
      R i = R j ↔ ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
        d.star σ (v i) = v j :=
    (titsIndexRelativeSimpleRoots k G d).1 ⟨v i, hi⟩ ⟨v j, hj⟩
  have hsame (hs : p.swapsArms = true) (j : Fin 6) : R (τ j) = R j := by
    obtain ⟨σ, hσ⟩ : swaps := of_decide_eq_true hs
    by_cases hj : marks j
    · exact ((hres j (τ j) hj ((hmark j).mpr hj)).mpr ⟨σ, hσ j⟩).symm
    · rw [hzero _ (fun h => hj ((hmark j).mp h)), hzero _ hj]
  have hproj (c : BranchMarking.Coordinates) :
      ∑ j, p.project c j • R j = ∑ j, c j • R j := by
    refine projection_sum p R c (hzero 1 hbranch) ?_ ?_ ?_ ?_
    · intro hp
      have hn : ¬ marks 0 := of_decide_eq_false hp
      exact ⟨hzero 0 hn, hzero 5 (fun h => hn (hends.mp h))⟩
    · intro hp
      have hn : ¬ marks 2 := of_decide_eq_false hp
      exact ⟨hzero 2 hn, hzero 4 (fun h => hn (harms.mp h))⟩
    · exact fun hp => hzero 3 (of_decide_eq_false hp)
    · exact fun hp => ⟨hsame hp 0, hsame hp 2⟩
  have hsep (i j : {j : Fin 6 // p.active j = true}) (h : R i = R j) : i = j := by
    obtain ⟨σ, hσ⟩ := (hres i j (hmarkedActive i i.2) (hmarkedActive j j.2)).mp h
    apply Subtype.ext
    rcases hstar σ with hid | hsym
    · exact v.injective ((hid i).symm.trans hσ)
    · have hs : p.swapsArms = true := decide_eq_true ⟨σ, hsym⟩
      have hij : τ i.val = j.val := v.injective ((hsym i).symm.trans hσ)
      have hi := i.property
      have hj := j.property
      change p.active i.val = true at hi
      change p.active j.val = true at hj
      rw [← hij] at hj ⊢
      generalize i.val = l at hi hj ⊢
      fin_cases l <;> simp_all [BranchMarking.active, τ]
  let : Mono d.splitInclusion.hom.hom.left := d.maximalSplit.isSplitSubtorus.mono
  have hR : HasRelativeRootSystem d.splitInclusion :=
    relativeRootSystem k G d.isSemisimple.isConnectedReductive _ _ d.maximalSplit
  let W := relativeRootSpan d.splitInclusion
  have hLI := hR.linearIndependent_simpleRelativeRoots d.splitInclusion d.positiveCocharacter
    d.maximalSplit.1.1 d.generic
  obtain ⟨orbit, horbit⟩ := (titsIndexRelativeSimpleRoots k G d).2
  let sr (j : {j : Fin 6 // p.active j = true}) :
      simpleRelativeRoots d.splitInclusion d.positiveCocharacter :=
    orbit (d.orbitClass ⟨v j, hmarkedActive j j.2⟩)
  have hsr (j : {j : Fin 6 // p.active j = true}) : (sr j).val = R j := horbit _
  have hInd : LinearIndependent ℚ
      (fun j : {j : Fin 6 // p.active j = true} => toRat (R j)) := by
    simp only [← hsr]
    exact hLI.comp sr fun i j h => hsep i j ((hsr i).symm.trans ((congrArg Subtype.val h).trans (hsr j)))
  obtain ⟨J, _, P, _, hcrys, _, hroots, _, _⟩ := hR
  let : P.IsCrystallographic := hcrys
  have hW (j : Fin 6) : toRat (R j) ∈ W := by
    by_cases hj : marks j
    · exact toRat_mem_ratSpan (TitsIndexStarProof.mem_relativeRoots_of_ne_zero d _ hj)
    · simp [hzero _ hj]
  let w (j : Fin 6) : W := ⟨toRat (R j), hW j⟩
  let vector : BranchMarking.Coordinates →+ W :=
    { toFun := fun c => ∑ j, c j • w j
      map_zero' := by simp
      map_add' := by
        intro x y
        simp [add_zsmul, Finset.sum_add_distrib] }
  have hvalue (c : BranchMarking.Coordinates) :
      (vector c : ℚ ⊗[ℤ] characterLattice d.splitTorus) = toRat (∑ j, c j • R j) := by
    change (↑(∑ j, c j • w j) : ℚ ⊗[ℤ] characterLattice d.splitTorus) = _
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul]
    rfl
  have hsum (c : BranchMarking.Coordinates) (hc : ∀ j, p.active j = false → c j = 0) :
      (vector c : ℚ ⊗[ℤ] characterLattice d.splitTorus) =
        ∑ j : {j : Fin 6 // p.active j = true}, (c j : ℚ) • toRat (R j) := by
    rw [hvalue, map_sum]
    let s := Finset.univ.filter (fun j => p.active j = true)
    calc
      ∑ j, toRat (c j • R j) = ∑ j ∈ s, (c j : ℚ) • toRat (R j) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        cases hj : p.active j
        · simp [hc j hj]
        · simp [map_zsmul, Int.cast_smul_eq_zsmul]
      _ = _ := Finset.sum_subtype s (by simp [s]) _
  have hInjective (x y : BranchMarking.Coordinates)
      (hx : ∀ j, p.active j = false → x j = 0) (hy : ∀ j, p.active j = false → y j = 0)
      (h : vector x = vector y) : x = y := by
    have heq := congrArg (fun z : W => (z : ℚ ⊗[ℤ] characterLattice d.splitTorus)) h
    rw [hsum _ hx, hsum _ hy] at heq
    have hdiff : ∑ j : {j : Fin 6 // p.active j = true},
        ((x j : ℚ) - (y j : ℚ)) • toRat (R j) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, heq, sub_self]
    have hc := Fintype.linearIndependent_iff.mp hInd _ hdiff
    ext j
    cases hj : p.active j
    · rw [hx j hj, hy j hj]
    · have hj' := sub_eq_zero.mp (hc ⟨j, hj⟩)
      exact_mod_cast hj'
  have hmem (z : W) :
      z ∈ Set.range P.root ↔
        ∃ r : d.pinning.rootIndex, d.rootRestriction r ≠ 0 ∧
          (z : ℚ ⊗[ℤ] characterLattice d.splitTorus) = toRat (d.rootRestriction r) := by
    have hz : z ∈ Set.range P.root ↔
        (z : ℚ ⊗[ℤ] characterLattice d.splitTorus) ∈ toRat '' relativeRoots d.splitInclusion := by
      rw [← hroots]
      constructor
      · exact fun hz => ⟨z, hz, rfl⟩
      · rintro ⟨y, hy, heq⟩
        exact (Subtype.ext heq : y = z) ▸ hy
    rw [hz]
    constructor
    · rintro ⟨χ, hχ, hχz⟩
      obtain ⟨r, rfl⟩ := TitsIndexStarProof.exists_of_mem_relativeRoots d hχ
      exact ⟨r, (mem_relativeRoots.mp hχ).1, hχz.symm⟩
    · rintro ⟨r, hr, hrz⟩
      exact ⟨_, TitsIndexStarProof.mem_relativeRoots_of_ne_zero d r hr, hrz.symm⟩
  have hunit (j : Fin 6) : vector (BranchMarking.unit j) = 0 ∨
      vector (BranchMarking.unit j) ∈ Set.range P.root := by
    have heq : (vector (BranchMarking.unit j) : ℚ ⊗[ℤ] characterLattice d.splitTorus) =
        toRat (R j) := by
      rw [hvalue]
      simp [BranchMarking.unit, Pi.single_apply, ite_smul]
    by_cases hj : marks j
    · exact Or.inr ((hmem _).mpr ⟨a j, hj, heq⟩)
    · exact Or.inl (Subtype.ext (by simpa [hzero j hj] using heq))
  let Pa := d.pinning.rootDatum
  let : Finite d.pinning.rootIndex := d.pinning.finiteRootIndex
  let : Pa.IsReduced := d.pinning.isReduced
  have hcartan (i j : Fin 6) : Pa.pairing (a i) (a j) = CartanMatrix.E 6 i j := by
    change d.cartan (v i) (v j) = _
    simpa [v] using hE (v i) (v j)
  have hrestrict (j : Fin 36) :
      d.rootRestrictionHom (RootReflectionCoefficients.combination Pa a (positiveCoefficients j)) =
        ∑ i, p.project (positiveCoefficients j) i • R i := by
    rw [hproj]
    simp [Pa, RootReflectionCoefficients.combination, R, map_sum, map_zsmul]
  have hcoeff (j : Fin 36) (s : Bool) :
      ∃ r : d.pinning.rootIndex, d.rootRestriction r =
        ∑ i, (if s then -(p.project (positiveCoefficients j)) else p.project (positiveCoefficients j)) i • R i := by
    obtain ⟨r, hr⟩ := isRoot_positiveCoefficients Pa a hcartan j
    have heq : d.rootRestriction r = ∑ i, p.project (positiveCoefficients j) i • R i := by
      rw [← d.rootRestrictionHom_root]
      change d.rootRestrictionHom (Pa.root r) = _
      rw [hr]
      exact hrestrict j
    cases s
    · exact ⟨r, heq⟩
    · refine ⟨Pa.reflectionPerm r r, ?_⟩
      rw [← d.rootRestrictionHom_root, Pa.root_reflectionPerm, Pa.reflection_apply_self,
        map_neg, d.rootRestrictionHom_root, heq, ← Finset.sum_neg_distrib]
      simp
  have hzeroProj : p.IsProjectedRoot 0 := by
    obtain ⟨s, l, b, r⟩ := p
    cases s <;> cases l <;> cases b <;> cases r <;> exact ⟨false, 1, by decide⟩
  have hprojected (c : BranchMarking.Coordinates) (hc : ∀ j, p.active j = false → c j = 0) :
      p.IsProjectedRoot c ↔ vector c = 0 ∨ vector c ∈ Set.range P.root := by
    constructor
    · rintro ⟨s, j, rfl⟩
      obtain ⟨r, hr⟩ := hcoeff j s
      have heq : (vector (if s then -(p.project (positiveCoefficients j))
          else p.project (positiveCoefficients j)) : ℚ ⊗[ℤ] characterLattice d.splitTorus) =
          toRat (d.rootRestriction r) := by
        rw [hvalue, hr]
      by_cases hz : d.rootRestriction r = 0
      · exact Or.inl (Subtype.ext (by simpa [hz] using heq))
      · exact Or.inr ((hmem _).mpr ⟨r, hz, heq⟩)
    · rintro (hz | hroot)
      · have heq := hInjective c 0 hc (by simp) (hz.trans (map_zero vector).symm)
        simpa [heq] using hzeroProj
      · obtain ⟨r, _, hr⟩ := (hmem _).mp hroot
        obtain ⟨j, hj | hj⟩ := exists_signedCoefficients Pa d.pinning.base e hcartan r
        · let x := p.project (positiveCoefficients j)
          have hx : p.IsProjectedRoot x := ⟨false, j, rfl⟩
          have hval : vector c = vector x := by
            apply Subtype.ext
            rw [hr, hvalue x]
            congr 1
            rw [← d.rootRestrictionHom_root]
            change d.rootRestrictionHom (Pa.root r) = _
            rw [hj]
            exact hrestrict j
          exact hInjective c x hc hx.apply_eq_zero_of_inactive hval ▸ hx
        · let x := -p.project (positiveCoefficients j)
          have hx : p.IsProjectedRoot x := ⟨true, j, rfl⟩
          have hval : vector c = vector x := by
            apply Subtype.ext
            rw [hr, hvalue x]
            congr 1
            rw [← d.rootRestrictionHom_root]
            change d.rootRestrictionHom (Pa.root r) = ∑ i, (-p.project (positiveCoefficients j) i) • R i
            rw [hj, map_neg]
            simpa only [neg_zsmul, Finset.sum_neg_distrib] using congrArg Neg.neg (hrestrict j)
          exact hInjective c x hc hx.apply_eq_zero_of_inactive hval ▸ hx
  have ⟨hb, hr⟩ := p.innerArm_unmarked_and_central_unmarked
    (integralReflections P p vector hunit hInjective hprojected)
  have hn2 : ¬ marks 2 := of_decide_eq_false hb
  have hn3 : ¬ marks 3 := of_decide_eq_false hr
  have hl : marks 0 := by
    obtain ⟨b, hb⟩ := hne
    have hb' : marks (e b) := by simpa [marks, v] using hb
    generalize e b = i at hb'
    fin_cases i
    · exact hb'
    · exact (hbranch hb').elim
    · exact (hn2 hb').elim
    · exact (hn3 hb').elim
    · exact (hn2 (harms.mp hb')).elim
    · exact hends.mp hb'
  intro b
  have h : b ∈ d.distinguishedVertices ↔ marks (e b) := by simp [marks, v]
  have h1 : ¬ marks 1 := hbranch
  have h4 : ¬ marks 4 := fun h => hn2 (harms.mp h)
  have h5 : marks 5 := hends.mpr hl
  rw [h]
  generalize e b = i
  fin_cases i <;> simp [hl, h1, hn2, hn3, h4, h5]

end Langlands.GroupScheme

import Langlands.GroupScheme.OrthogonalMatrix.CoverRootCoordinates
import Langlands.GroupScheme.OrthogonalMatrix.CoverTorusCharacters
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.LinearAlgebra.TypeDNumberedWeights
import Langlands.LinearAlgebra.TypeDVectorNormalization

/-! # Descended numbered vector weights of an aligned orthogonal cover -/
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme.OrthogonalMatrix

variable {k : Type u} [Field k] {n : ℕ}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G)
  {pi : G ⟶ identityComponent (groupScheme (Fin n) (CommRingCat.of k))}

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

/-- Numbered integral vector weights, their actual descents and signed standard coordinates. -/
structure CoverNumberedWeights (e : p.base.support ≃ Fin n) (q : p.torus ⟶ 𝔻) where
  weight : Fin n → characterLattice p.torus
  standard : Fin n → characterLattice 𝔻
  pullback : ∀ i, q ≫ standard i = weight i
  chain : ∀ (a : p.base.support) (h : (e a).val + 1 < n),
    p.rootDatum.root a.val = weight (e a) - weight ⟨(e a).val + 1, h⟩
  last : ∀ (a : p.base.support) (h : (e a).val + 1 = n),
    p.rootDatum.root a.val = weight ⟨n - 2, by omega⟩ + weight ⟨n - 1, by omega⟩
  permutation : Equiv.Perm (Fin n)
  sign : Fin n → ℤˣ
  coordinate : ∀ i, GeneralLinear.characterCoordEquiv (Fin n) k (standard i) =
    Pi.single (permutation i) (sign i : ℤ)

/-- The aligned fundamental weight descends, as do all successive weights;
actual coroot pairings force their standard coordinates to be a signed permutation. -/
theorem nonempty_coverNumberedWeights (hn : 4 ≤ n) (hG : IsSimplyConnected G)
    (hpi : IsCentralIsogeny pi) (e : p.base.support ≃ Fin n)
    (hcartan : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.D n (e a) (e b))
    (halign : ∀ v : p.base.support, (e v).val = 0 →
      ∀ chi : characterLattice p.torus,
        latticePairing _ chi (p.rootDatum.coroot v.val) = 1 →
        (∀ w : p.base.support, w ≠ v →
          latticePairing _ chi (p.rootDatum.coroot w.val) = 0) →
        ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ p.torus.X),
          t ≫ (p.inclusion ≫ pi).hom.hom = 1 →
            t ≫ (CommGroupScheme.groupHom chi).hom.hom = 1)
    (tr : StandardTorusTransport p.inclusion pi) :
    Nonempty (CoverNumberedWeights p e tr.torusMap) := by
  let : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
  have hspan := splitSimplyConnectedCorootSpan k G hG p.torus p.isSplitTorus
    p.inclusion p.isMaximalTorus p.rootIndex p.rootDatum p.isRootDatum p.isReduced
  let eps := TypeDNumberedWeights.weight p.rootDatum p.base hspan e
  have hchain := TypeDNumberedWeights.root_chain p.rootDatum p.base hspan e hn hcartan
  have hlast := TypeDNumberedWeights.root_last p.rootDatum p.base hspan e hn hcartan
  let c := coverRootCoordinates p hn hpi tr
  let z : Fin n := ⟨0, by omega⟩
  have hzero : ∃ psi : characterLattice 𝔻, tr.torusMap ≫ psi = eps z := by
    apply (tr.exists_character_comp_eq_iff _).mpr
    apply halign (e.symm z) (by simp [z])
    · rw [← p.isRootDatum.1]
      simpa [eps, z] using
        TypeDNumberedWeights.pairing_weight_zero p.rootDatum p.base hspan e hn (e.symm z)
    · intro w hw
      rw [← p.isRootDatum.1]
      have hw' : (e w).val ≠ 0 := by
        intro h
        apply hw
        apply e.injective
        apply Fin.ext
        simpa [z] using h
      simpa [eps, hw'] using
        TypeDNumberedWeights.pairing_weight_zero p.rootDatum p.base hspan e hn w
  have hdesc : ∀ i : Fin n, ∃ psi : characterLattice 𝔻,
      tr.torusMap ≫ psi = eps i := by
    suffices ∀ (d : ℕ) (hd : d < n), ∃ psi : characterLattice 𝔻,
        tr.torusMap ≫ psi = eps ⟨d, hd⟩ from fun i => this i.val i.isLt
    intro d
    induction d with
    | zero => intro hd; exact hzero
    | succ d ih =>
      intro hd
      obtain ⟨psi, hpsi⟩ := ih (by omega)
      let a := e.symm (⟨d, by omega⟩ : Fin n)
      refine ⟨psi - (GeneralLinear.characterCoordEquiv (Fin n) k).symm (c.root a.val), ?_⟩
      rw [Preadditive.comp_sub, hpsi, c.pullback_root, hchain a (by simp [a]; omega)]
      simp only [a, Equiv.apply_symm_apply]
      change eps ⟨d, _⟩ - (eps ⟨d, _⟩ - eps ⟨d + 1, hd⟩) = eps ⟨d + 1, hd⟩
      abel
  choose psi hpsi using hdesc
  have := tr.flat
  have := tr.surjective
  have : Epi (CommGroupScheme.groupHom tr.torusMap).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  have hinj := RealTorusSpace.characterRestrict_injective_of_epi tr.torusMap
  have hcoordchain (j : Fin n) (hj : j.val + 1 < n) :
      c.root (e.symm j).val =
        GeneralLinear.characterCoordEquiv (Fin n) k (psi j) -
          GeneralLinear.characterCoordEquiv (Fin n) k (psi ⟨j.val + 1, hj⟩) := by
    apply (GeneralLinear.characterCoordEquiv (Fin n) k).symm.injective
    simp only [map_sub, LinearEquiv.symm_apply_apply]
    apply hinj
    change tr.torusMap ≫ _ = tr.torusMap ≫ _
    rw [c.pullback_root, Preadditive.comp_sub, hpsi, hpsi]
    simpa only [Equiv.apply_symm_apply] using hchain (e.symm j) (by simpa using hj)
  have hcoordlast : c.root (e.symm (⟨n - 1, by omega⟩ : Fin n)).val =
      GeneralLinear.characterCoordEquiv (Fin n) k (psi ⟨n - 2, by omega⟩) +
        GeneralLinear.characterCoordEquiv (Fin n) k (psi ⟨n - 1, by omega⟩) := by
    apply (GeneralLinear.characterCoordEquiv (Fin n) k).symm.injective
    simp only [map_add, LinearEquiv.symm_apply_apply]
    apply hinj
    change tr.torusMap ≫ _ = tr.torusMap ≫ _
    rw [c.pullback_root, Preadditive.comp_add, hpsi, hpsi]
    exact hlast _ (by simp; omega)
  let x := fun i => GeneralLinear.characterCoordEquiv (Fin n) k (psi i)
  have hpair (i : Fin n) (a : p.base.support) :
      dotProduct (x i) (c.root a.val) = TypeDNumberedWeights.coefficient i (e a) := by
    rw [← c.pairing, hpsi, ← p.isRootDatum.1]
    exact TypeDNumberedWeights.pairing_weight p.rootDatum p.base hspan e i a
  have hgram : ∀ i j, dotProduct (x i) (x j) = if i = j then 1 else 0 := by
    apply TypeDVectorNormalization.gram_eq hn
    · intro i j hj
      simpa only [Equiv.apply_symm_apply, hcoordchain j hj] using hpair i (e.symm j)
    · intro i
      simpa only [Equiv.apply_symm_apply, hcoordlast] using
        hpair i (e.symm (⟨n - 1, by omega⟩ : Fin n))
  exact ⟨⟨eps, psi, hpsi, hchain, hlast, TypeDVectorNormalization.permutation x hgram,
    TypeDVectorNormalization.sign x hgram, TypeDVectorNormalization.normalization x hgram⟩⟩

/-- Choose the descended numbered weights from full cover-kernel alignment. -/
def coverNumberedWeights (hn : 4 ≤ n) (hG : IsSimplyConnected G)
    (hpi : IsCentralIsogeny pi) (e : p.base.support ≃ Fin n)
    (hcartan : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.D n (e a) (e b))
    (halign : ∀ v : p.base.support, (e v).val = 0 →
      ∀ chi : characterLattice p.torus,
        latticePairing _ chi (p.rootDatum.coroot v.val) = 1 →
        (∀ w : p.base.support, w ≠ v →
          latticePairing _ chi (p.rootDatum.coroot w.val) = 0) →
        ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ p.torus.X),
          t ≫ (p.inclusion ≫ pi).hom.hom = 1 →
            t ≫ (CommGroupScheme.groupHom chi).hom.hom = 1)
    (tr : StandardTorusTransport p.inclusion pi) :
    CoverNumberedWeights p e tr.torusMap :=
  Classical.choice (nonempty_coverNumberedWeights p hn hG hpi e hcartan halign tr)

/-- Index the two standard weight signs by the units of the integers. -/
def signedWeightIndexEquiv {l : Type} : (l × ℤˣ) ≃ (l ⊕ l) where
  toFun a := if a.2 = 1 then Sum.inl a.1 else Sum.inr a.1
  invFun := Sum.elim (fun i => (i, 1)) (fun i => (i, -1))
  left_inv a := by
    rcases a with ⟨i, s⟩
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp
  right_inv a := by rcases a with i | i <;> simp

@[simp] theorem index_signedWeightIndexEquiv {l : Type} (a : l × ℤˣ) :
    index (signedWeightIndexEquiv a) = a.1 := by
  rcases a with ⟨i, s⟩
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [signedWeightIndexEquiv]

theorem weightChar_signedWeightIndexEquiv (a : Fin n × ℤˣ) :
    weightChar (Fin n) k (signedWeightIndexEquiv a) =
      (a.2 : ℤ) • weightChar (Fin n) k (Sum.inl a.1) := by
  apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
  rcases a with ⟨i, s⟩
  rcases Int.units_eq_one_or s with rfl | rfl <;>
    simp [signedWeightIndexEquiv, characterCoordEquiv_weightChar,
      SymplecticMatrix.weightCoord_inl, SymplecticMatrix.weightCoord_inr] <;>
      funext j <;> simp only [Pi.single_apply, Pi.neg_apply] <;> split_ifs <;> rfl

namespace CoverNumberedWeights
variable {e : p.base.support ≃ Fin n}
  {q : p.torus ⟶ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))}
  (w : CoverNumberedWeights p e q)

/-- The stored coordinates identify each descended character itself. -/
theorem standard_eq (i : Fin n) :
    w.standard i = (w.sign i : ℤ) • weightChar (Fin n) k (Sum.inl (w.permutation i)) := by
  apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
  rw [w.coordinate, map_zsmul, characterCoordEquiv_weightChar,
    SymplecticMatrix.weightCoord_inl]
  funext j
  simp [Pi.single_apply]

/-- Every signed pair of distinct numbered weights is an actual source root. -/
theorem signed_roots (c : CoverRootCoordinates p q) (i j : Fin n) (hij : i ≠ j)
    (s t : ℤˣ) : ∃ a : p.rootIndex,
      p.rootDatum.root a = (s : ℤ) • w.weight i + (t : ℤ) • w.weight j := by
  let a := signedWeightIndexEquiv (w.permutation i, s * w.sign i)
  let b := signedWeightIndexEquiv (w.permutation j, t * w.sign j)
  have hab : index a ≠ index b := by
    simpa only [a, b, index_signedWeightIndexEquiv] using
      (w.permutation.injective.ne hij)
  have hroot : weightChar (Fin n) k a + weightChar (Fin n) k b ∈
      roots (identityTorus (Fin n) k) := by
    rw [roots_identityTorus]
    apply weightChar_add_mem_roots
    · exact fun h => hab (congrArg index h)
    · exact fun h => hab (by rw [h, index_swap])
  obtain ⟨r, hr⟩ := c.roots_pullback _ hroot
  refine ⟨r, hr.symm.trans ?_⟩
  have ha : weightChar (Fin n) k a = (s : ℤ) • w.standard i := by
    rw [w.standard_eq, smul_smul]
    exact weightChar_signedWeightIndexEquiv (w.permutation i, s * w.sign i)
  have hb : weightChar (Fin n) k b = (t : ℤ) • w.standard j := by
    rw [w.standard_eq, smul_smul]
    exact weightChar_signedWeightIndexEquiv (w.permutation j, t * w.sign j)
  rw [ha, hb, Preadditive.comp_add, Preadditive.comp_zsmul,
    Preadditive.comp_zsmul, w.pullback, w.pullback]

end CoverNumberedWeights
end Langlands.GroupScheme.OrthogonalMatrix

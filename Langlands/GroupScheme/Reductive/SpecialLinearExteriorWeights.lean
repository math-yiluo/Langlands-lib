import Langlands.GroupScheme.Chevalley.MatrixExterior
import Langlands.GroupScheme.Reductive.SpecialLinearHighestWeight

/-! # Fundamental weights in the exterior powers of the special-linear column representation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.Chevalley

/-- The exterior power of a diagonal matrix is diagonal with products over
the ordered coordinate subsets. -/
theorem exteriorGL_of_diagonal {N d : ℕ} {A : Type*} [CommRing A]
    (z : Fin N → A) (g : GL (Fin N) A) (hg : (g : Matrix _ _ A) = Matrix.diagonal z) :
    (exteriorGL N d A g :
      Matrix (Set.powersetCard (Fin N) d) (Set.powersetCard (Fin N) d) A) =
      Matrix.diagonal (fun s => ∏ i, z (Set.powersetCard.ofFinEmbEquiv.symm s i)) := by
  classical
  ext s t
  rw [exteriorGL_apply]
  change (Matrix.of fun i j : Fin d => (g : Matrix _ _ A)
    (Set.powersetCard.ofFinEmbEquiv.symm s j) (Set.powersetCard.ofFinEmbEquiv.symm t i)).det = _
  rw [hg]
  by_cases hst : s = t
  · subst t
    rw [Matrix.diagonal_apply_eq, ← Matrix.det_diagonal]
    congr 1
    ext i j
    by_cases hij : j = i
    · subst j
      simp [Matrix.diagonal_apply]
    · simp [Matrix.diagonal_apply, (Set.powersetCard.ofFinEmbEquiv.symm s).injective.eq_iff,
        hij, Ne.symm hij]
  · rw [Matrix.diagonal_apply_ne _ hst]
    have hsub : ¬t.val ⊆ s.val := fun h =>
      hst (Subtype.ext (Finset.eq_of_subset_of_card_le h (by rw [s.prop, t.prop])).symm)
    obtain ⟨a, hat, has⟩ := Finset.not_subset.mp hsub
    obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t a).mpr hat
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    have hne : Set.powersetCard.ofFinEmbEquiv.symm s j ≠ a := fun he =>
      has ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s a).mp ⟨j, he⟩)
    simpa only [Matrix.of_apply, hi] using Matrix.diagonal_apply_ne z hne

end Langlands.GroupScheme.Chevalley

namespace Langlands.GroupScheme.SpecialLinear.FinSucc

open MatrixRepresentation Chevalley

variable {n d : ℕ} {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))
local notation "ι" => Set.powersetCard (Fin (n + 1)) d

/-- The sum of the diagonal characters of the selected coordinates. -/
def exteriorWeight (s : ι) : characterLattice 𝔻 :=
  ∑ y ∈ s.val, weightChar n k y

theorem exteriorWeight_eq_sum (s : ι) :
    exteriorWeight (k := k) s = ∑ i, weightChar n k (Set.powersetCard.ofFinEmbEquiv.symm s i) := by
  obtain ⟨f, rfl⟩ := Set.powersetCard.ofFinEmbEquiv.surjective s
  rw [Equiv.symm_apply_apply]
  change (∑ y ∈ Finset.univ.map f.toEmbedding, weightChar n k y) = _
  rw [Finset.sum_map]
  rfl

private theorem exteriorWeight_eq_indicator (s : ι) :
    exteriorWeight (k := k) s =
      ∑ y, (if y ∈ s.val then (1 : ℤ) else 0) • weightChar n k y := by
  classical
  simp only [exteriorWeight, ite_smul, one_smul, zero_smul]
  rw [← Finset.sum_filter]
  congr 1
  ext y
  simp

/-- Distinct subsets of one cardinality give distinct characters of the
determinant-one diagonal torus. -/
theorem exteriorWeight_injective : Function.Injective (exteriorWeight (n := n) (d := d) (k := k)) := by
  classical
  intro s t h
  let c (v : ι) (y : Fin (n + 1)) : ℤ := if y ∈ v.val then 1 else 0
  have hdiff (y : Fin (n + 1)) : c s y - c t y = c s (Fin.last n) - c t (Fin.last n) := by
    induction y using Fin.lastCases with
    | last => rfl
    | cast a =>
      have ha := congrArg (fun w => GeneralLinear.characterCoordEquiv (Fin n) k w a) h
      rw [exteriorWeight_eq_indicator, exteriorWeight_eq_indicator] at ha
      change GeneralLinear.characterCoordEquiv (Fin n) k (∑ y, c s y • weightChar n k y) a =
        GeneralLinear.characterCoordEquiv (Fin n) k (∑ y, c t y • weightChar n k y) a at ha
      rw [characterCoordEquiv_sum_smul_weightChar, characterCoordEquiv_sum_smul_weightChar] at ha
      omega
  have hsubset (v w : ι) (hle : ∀ y, c v y ≤ c w y) : v = w := by
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le _ (by rw [v.prop, w.prop])
    intro y hy
    by_contra hny
    simpa [c, hy, hny] using hle y
  rcases le_total (c s (Fin.last n)) (c t (Fin.last n)) with hle | hle
  · exact hsubset s t (fun y => by have := hdiff y; omega)
  · exact (hsubset t s (fun y => by have := hdiff y; omega)).symm

variable (n d k) in
/-- The actual exterior power of the standard special-linear column representation. -/
def exteriorColumnRepresentation :
    MatrixRepresentation (groupScheme (Fin (n + 1)) (CommRingCat.of k)) ι :=
  exteriorRepresentation (n + 1) d (CommRingCat.of k)
    (inclusion (Fin (n + 1)) (CommRingCat.of k))

private abbrev diagonalExteriorRepresentation :=
  (exteriorColumnRepresentation n d k).restrict (diagonalTorus n (CommRingCat.of k))

private theorem diagonalExteriorRepresentation_affineMatrix (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶ (𝔻).toGrp.X) :
    ((diagonalExteriorRepresentation (n := n) (d := d) (k := k)).affineMatrix S x :
      Matrix ι ι S) =
        Matrix.diagonal (fun s =>
          ∏ i, (torusEntry (GeneralLinear.torusCoords x)
            (Set.powersetCard.ofFinEmbEquiv.symm s i) : S)) := by
  let R := CommRingCat.of k
  let y := (x ≫ (diagonalTorus n R).hom.hom) ≫ (inclusion (Fin (n + 1)) R).hom.hom
  let g := GeneralLinear.affinePointsEquiv (Fin (n + 1)) R S y
  have h := Corepresented.groupSchemeMap_affinePoints
    (GeneralLinear.corepresentableBy (Fin (n + 1)) R)
    (GeneralLinear.corepresentableBy ι R) (exteriorNat (n + 1) d R) y
  change GeneralLinear.affinePointsEquiv ι R S
    (y ≫ (exteriorGroupHom (n + 1) d R).hom.hom) = exteriorGL (n + 1) d S g at h
  refine Eq.trans ?_ (exteriorGL_of_diagonal _ g (diagonalRepresentation_affineMatrix S x))
  change (GeneralLinear.affinePointsEquiv ι R S
    ((x ≫ (diagonalTorus n R).hom.hom) ≫
      ((inclusion (Fin (n + 1)) R) ≫ exteriorGroupHom (n + 1) d R).hom.hom) :
        Matrix ι ι S) = _
  rw [Grp.comp_hom_hom, ← Category.assoc, h]

private theorem exteriorWeight_unit (s : ι) :
    let A := CharacterUnits.Coord (𝔻).toGrp
    let v : Lie.AffinePoints (𝔻).toGrp A := CharacterUnits.universalPoint (𝔻).toGrp
    CharacterUnits.unit ((rationalCharacters.equivCharacterLattice 𝔻).symm
      (exteriorWeight (k := k) s)) =
    ∏ i, torusEntry (GeneralLinear.torusCoords (A := A) v)
      (Set.powersetCard.ofFinEmbEquiv.symm s i) := by
  intro A v
  rw [exteriorWeight_eq_sum]
  let f := Set.powersetCard.ofFinEmbEquiv.symm s
  let χ := (rationalCharacters.equivCharacterLattice 𝔻).symm.toAddMonoidHom
  have h (t : Finset (Fin d)) :
      CharacterUnits.unit (χ (∑ i ∈ t, weightChar n k (f i))) =
        ∏ i ∈ t, torusEntry (GeneralLinear.torusCoords (A := A) v) (f i) := by
    classical
    induction t using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty, map_zero, CharacterUnits.unit_zero]
    | insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, map_add, CharacterUnits.unit_add, ih]
      congr 1
      exact characterValue_weightChar (S := A) (f i) v
  exact h Finset.univ

private theorem diagonalExterior_universalCharacterMatrix :
    (diagonalExteriorRepresentation (n := n) (d := d) (k := k)).universalCharacterMatrix =
      Matrix.diagonal (fun s => (CharacterUnits.unit
        ((rationalCharacters.equivCharacterLattice 𝔻).symm (exteriorWeight s)) :
          CharacterUnits.Coord (𝔻).toGrp)) := by
  rw [universalCharacterMatrix, diagonalExteriorRepresentation_affineMatrix]
  congr 1
  funext s
  simpa only [Units.coe_prod] using
    (congrArg Units.val (exteriorWeight_unit (k := k) s)).symm

private theorem diagonalExterior_hasCharacterCoefficients :
    (diagonalExteriorRepresentation (n := n) (d := d) (k := k)).HasCharacterCoefficients
      (LinearMap.id : (ι → k) →ₗ[k] (ι → k))
      (fun s => (rationalCharacters.equivCharacterLattice 𝔻).symm (exteriorWeight s)) := by
  classical
  intro v s
  have h (w : ι → CharacterUnits.Coord (𝔻).toGrp) :
      coefficientExtension (LinearMap.id : (ι → k) →ₗ[k] (ι → k)) _ w s = w s := by
    simp [coefficientExtension, Pi.single_apply]
  rw [h]
  change ((diagonalExteriorRepresentation (n := n) (d := d) (k := k)).universalCharacterMatrix *ᵥ
    (fun j => algebraMap k (CharacterUnits.Coord (𝔻).toGrp) (v j))) s = _
  rw [diagonalExterior_universalCharacterMatrix, Matrix.mulVec_diagonal]
  rfl

private theorem diagonalExterior_characterSpace_ne_bot (s : ι) :
    (diagonalExteriorRepresentation (n := n) (d := d) (k := k)).characterSpace
      ((rationalCharacters.equivCharacterLattice 𝔻).symm (exteriorWeight s)) ≠ ⊥ := by
  classical
  refine (Submodule.ne_bot_iff _).mpr ⟨Pi.single s 1, ?_, ?_⟩
  · rw [mem_characterSpace_iff, diagonalExterior_universalCharacterMatrix]
    ext j
    rw [Matrix.mulVec_diagonal]
    by_cases hj : j = s <;> simp [hj, Pi.single_apply]
  · intro h
    have hs := congrFun h s
    exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using hs)

private theorem diagonalExterior_finrank (s : ι) :
    Module.finrank k ((diagonalExteriorRepresentation (n := n) (d := d) (k := k)).characterSpace
      ((rationalCharacters.equivCharacterLattice 𝔻).symm (exteriorWeight s))) = 1 := by
  apply finrank_characterSpace_eq_one _ LinearMap.id _
    diagonalExterior_hasCharacterCoefficients Function.injective_id _ s
  · intro t h
    exact (exteriorWeight_injective
      ((rationalCharacters.equivCharacterLattice 𝔻).symm.injective h)).symm
  · exact diagonalExterior_characterSpace_ne_bot s

private theorem exists_exteriorWeight_of_ne_bot (mu : characterLattice 𝔻)
    (hmu : (diagonalExteriorRepresentation (n := n) (d := d) (k := k)).characterSpace
      ((rationalCharacters.equivCharacterLattice 𝔻).symm mu) ≠ ⊥) :
    ∃ s : ι, mu = exteriorWeight s := by
  obtain ⟨s, hs⟩ := exists_coefficient_character _ LinearMap.id _
    diagonalExterior_hasCharacterCoefficients Function.injective_id hmu
  exact ⟨s, (rationalCharacters.equivCharacterLattice 𝔻).symm.injective hs⟩

private def initialExteriorSubset (a : Fin n) : Set.powersetCard (Fin (n + 1)) (a.val + 1) :=
  Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb (Nat.succ_le_succ a.isLt.le))

private theorem exteriorWeight_initial (a : Fin n) :
    exteriorWeight (k := k) (initialExteriorSubset a) = coordinateFundamentalChar n k a := by
  have hm (y : Fin (n + 1)) : y ∈ (initialExteriorSubset a).val ↔ y.val ≤ a.val := by
    change y ∈ initialExteriorSubset a ↔ _
    rw [initialExteriorSubset, Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
    constructor
    · rintro ⟨j, rfl⟩
      exact Nat.le_of_lt_succ j.isLt
    · intro hy
      exact ⟨⟨y.val, Nat.lt_succ_of_le hy⟩, Fin.ext rfl⟩
  simp only [exteriorWeight_eq_indicator, hm, coordinateFundamentalChar]

section CoordinatePinning

variable {J : Type u} [Finite J]
    {P : RootDatum J
      (characterLattice (splitTorus.commGroupScheme
        (Spec (CommRingCat.of k)) (ULift (Fin n))))
      (cocharacterLattice (splitTorus.commGroupScheme
        (Spec (CommRingCat.of k)) (ULift (Fin n))))}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P)
    (hred : P.IsReduced) (B : P.Base) (e : B.support ≃ Fin n)
    (hnumber : ∀ a : B.support,
      P.root a.val = rootChar n k (e a).castSucc (e a).succ)

include hnumber in
private theorem weightChar_sub_mem (p q : Fin (n + 1)) (hpq : p ≤ q) :
    weightChar n k p - weightChar n k q ∈
      (coordinatePinning P hP hred B).positiveRootMonoid := by
  induction q using Fin.induction with
  | zero =>
    rw [Fin.le_zero_iff.mp hpq, sub_self]
    exact (coordinatePinning P hP hred B).positiveRootMonoid.zero_mem
  | succ q ih =>
    by_cases heq : p = q.succ
    · rw [heq, sub_self]
      exact (coordinatePinning P hP hred B).positiveRootMonoid.zero_mem
    · have hp : p ≤ q.castSucc := by
        have hlt := lt_of_le_of_ne hpq heq
        change p.val < q.val + 1 at hlt
        exact Nat.le_of_lt_succ hlt
      have hr := (coordinatePinning P hP hred B).simpleRoot_mem_positiveRootMonoid (e.symm q)
      change P.root (e.symm q).val ∈ _ at hr
      rw [hnumber, e.apply_symm_apply, rootChar_eq_weightChar_sub] at hr
      simpa only [sub_add_sub_cancel] using
        (coordinatePinning P hP hred B).positiveRootMonoid.add_mem (ih hp) hr

include hnumber in
private theorem coordinateFundamentalChar_sub_exteriorWeight_mem (a : Fin n)
    (s : Set.powersetCard (Fin (n + 1)) (a.val + 1)) :
    coordinateFundamentalChar n k a - exteriorWeight s ∈
      (coordinatePinning P hP hred B).positiveRootMonoid := by
  let f := Set.powersetCard.ofFinEmbEquiv.symm s
  have hf (j : Fin (a.val + 1)) : j.val ≤ (f j).val := by
    induction j using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have hlt : (f j.castSucc).val < (f j.succ).val :=
        f.strictMono Fin.castSucc_lt_succ
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)
  rw [← exteriorWeight_initial, exteriorWeight_eq_sum, exteriorWeight_eq_sum, ← Finset.sum_sub_distrib]
  apply AddSubmonoid.sum_mem
  intro j _
  apply weightChar_sub_mem hP hred B e hnumber
  rw [initialExteriorSubset, Equiv.symm_apply_apply]
  exact hf j

include hnumber in
/-- The degree-`a + 1` exterior power has the `a`-th integral fundamental
weight with multiplicity one, and all its weights lie below it. -/
theorem exteriorColumn_fundamentalWeight (hspan : P.corootSpan ℤ = ⊤) (a : Fin n) :
    let p := coordinatePinning P hP hred B
    let lam : characterLattice p.torus :=
      Langlands.RootDatum.fundamentalWeightBasis P B hspan (e.symm a)
    let ρ := exteriorColumnRepresentation n (a.val + 1) k
    Module.finrank k (p.representationWeightSpace ρ lam) = 1 ∧
      ∀ mu, p.representationWeightSpace ρ mu ≠ ⊥ → lam - mu ∈ p.positiveRootMonoid := by
  dsimp only
  rw [fundamentalWeightBasis_eq_coordinate hP B e hnumber hspan, e.apply_symm_apply]
  constructor
  · change Module.finrank k (characterSpace
      (diagonalExteriorRepresentation (n := n) (d := a.val + 1) (k := k))
      ((rationalCharacters.equivCharacterLattice 𝔻).symm (coordinateFundamentalChar n k a))) = 1
    rw [← exteriorWeight_initial]
    exact diagonalExterior_finrank (initialExteriorSubset a)
  · intro mu hmu
    change characterSpace (diagonalExteriorRepresentation (n := n) (d := a.val + 1) (k := k))
      ((rationalCharacters.equivCharacterLattice 𝔻).symm mu) ≠ ⊥ at hmu
    obtain ⟨s, rfl⟩ := exists_exteriorWeight_of_ne_bot mu hmu
    exact coordinateFundamentalChar_sub_exteriorWeight_mem hP hred B e hnumber a s

end CoordinatePinning

end Langlands.GroupScheme.SpecialLinear.FinSucc

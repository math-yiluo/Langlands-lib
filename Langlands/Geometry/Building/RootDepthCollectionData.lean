import Langlands.Geometry.Building.PositiveDepthRayCompression
import Langlands.Geometry.Building.PositiveDepthCollection

/-! # Actual filtration subgroups sufficient for positive-depth collection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : S.toGrp ⟶ G) (φ : RootFunctionFamily S G) [IsAffineHom G.X.hom]

/-- The actual subgroup carriers and the two bounds used in positive-depth
collection. Reflection, opposite-root, support and nontriviality laws are absent. -/
structure RootDepthCollectionData where
  subgroup : characterLattice S → ℝ → Subgroup (rationalPoints G)
  coe_subgroup : ∀ a r, (subgroup a r : Set (rationalPoints G)) = rootFiltration i φ a r
  commutator_le : ∀ a ∈ relativeRoots i, ∀ b ∈ relativeRoots i,
    (∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] b : Vstar S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a)) → ∀ r s : ℝ,
    ⁅subgroup a r, subgroup b s⁆ ≤
      ⨆ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots i),
        subgroup (p • a + q • b) (p * r + q * s)
  double_le : ∀ a ∈ relativeRoots i, 2 • a ∈ relativeRoots i →
    ∀ r s : ℝ, 2 * r ≤ s → subgroup (2 • a) s ≤ subgroup a r

namespace RootDepthCollectionData

variable {i φ} (D : RootDepthCollectionData i φ)

/-- Literal filtration carriers make every supplied subgroup antitone in depth. -/
theorem antitone (a : characterLattice S) : Antitone (D.subgroup a) := by
  intro r s hrs g hg
  have hmem : g ∈ rootFiltration i φ a s := by
    rw [← D.coe_subgroup]; exact hg
  change g ∈ (D.subgroup a r : Set (rationalPoints G))
  rw [D.coe_subgroup]
  exact ⟨hmem.1, (WithTop.coe_le_coe.mpr hrs).trans hmem.2⟩

/-- Each factor lies in its actual root group, without a valuation premise. -/
theorem le_rootGroupPoints (a : characterLattice S) (r : ℝ) :
    D.subgroup a r ≤ rootGroupPoints i a := by
  intro g hg
  have hmem : g ∈ rootFiltration i φ a r := by
    rw [← D.coe_subgroup]; exact hg
  exact hmem.1

/-- The subgroup retained at a selected character; unselected entries are trivial. -/
def selectedDepthSubgroup (Ψ : Set (characterLattice S)) (f : characterLattice S → ℝ)
    (a : characterLattice S) : Subgroup (rationalPoints G) := by
  classical
  exact if a ∈ Ψ then D.subgroup a (f a) else ⊥

/-- A selected primitive factor, a doubled-only factor, or the identity.
The doubled-only case retains its original depth and actual root group. -/
def rayDepthSubgroup (Ψ : Set (characterLattice S)) (f : characterLattice S → ℝ)
    (a : characterLattice S) : Subgroup (rationalPoints G) := by
  classical
  exact if a ∈ Ψ then D.subgroup a (f a)
    else if 2 • a ∈ Ψ then D.subgroup (2 • a) (f (2 • a)) else ⊥

/-- Ordered products of the actual retained ray subgroups. -/
def orderedRayDepthProduct (Ψ : Set (characterLattice S)) (f : characterLattice S → ℝ)
    {n : ℕ} (a : Fin n → characterLattice S) : Set (rationalPoints G) :=
  Set.range (RelativeRoot.CentralExtension.orderedProduct
    (fun j => (D.rayDepthSubgroup Ψ f (a j)).subtype))

/-- The selected doubled subgroup is absorbed at exactly the supplied depth bound. -/
theorem rayDepthSubgroup_eq_sup
    {Ψ : Set (characterLattice S)} {f : characterLattice S → ℝ}
    (hroots : Ψ ⊆ relativeRoots i)
    (hdouble : ∀ a ∈ Ψ, 2 • a ∈ Ψ → 2 * f a ≤ f (2 • a))
    (a : characterLattice S) :
    D.rayDepthSubgroup Ψ f a =
      D.selectedDepthSubgroup Ψ f a ⊔ D.selectedDepthSubgroup Ψ f (2 • a) := by
  classical
  simp only [rayDepthSubgroup, selectedDepthSubgroup]
  by_cases ha : a ∈ Ψ
  · by_cases h2a : 2 • a ∈ Ψ
    · simp only [ha, h2a, ite_true]
      exact (sup_eq_left.mpr
        (D.double_le a (hroots ha) (hroots h2a) _ _ (hdouble a ha h2a))).symm
    · simp only [ha, h2a, ite_true, ite_false, sup_bot_eq]
  · simp only [ha, ite_false, bot_sup_eq]

variable {ν : cocharacterLattice S} {Ψ : Set (characterLattice S)}
  {f : characterLattice S → ℝ} (hdata : IsClosedPositiveRootDepth i ν Ψ f)

include hdata

/-- The supplied V3 bound and closed-positive depths increase both input heights. -/
theorem commutator_height
    {a b : characterLattice S} (ha : a ∈ Ψ) (hb : b ∈ Ψ) :
    ⁅D.subgroup a (f a), D.subgroup b (f b)⁆ ≤
      ⨆ c : Ψ,
        ⨆ (_ : max (latticePairing S a ν).toNat (latticePairing S b ν).toNat <
          (latticePairing S c ν).toNat), D.subgroup c (f c) := by
  have hapos := hdata.positive ha
  have hbpos := hdata.positive hb
  refine (D.commutator_le a hapos.1 b hbpos.1
    (KPApartmentData.positiveRoots_nonopposite ν hapos hbpos) (f a) (f b)).trans ?_
  refine iSup_le fun p => iSup_le fun q => iSup_le fun hp =>
    iSup_le fun hq => iSup_le fun hc => ?_
  obtain ⟨hcΨ, hdepth⟩ := hdata.combination ha hb hp hq hc
  have hheight :=
    (KPApartmentData.positiveRootCombination_height ν hapos hbpos hp hq hc).2
  exact le_iSup_of_le (⟨p • a + q • b, hcΨ⟩ : Ψ)
    (le_iSup_of_le hheight (D.antitone _ hdepth))

/-- Collection allows a finite list containing extra unselected entries,
which contribute the identity subgroup. -/
theorem range_selectedDepthProduct_eq_iSup
    {n : ℕ} (a : Fin n → characterLattice S) (hcover : Ψ ⊆ Set.range a) :
    Set.range (RelativeRoot.CentralExtension.orderedProduct
      (fun j => (D.selectedDepthSubgroup Ψ f (a j)).subtype)) =
        ((⨆ c : Ψ, D.subgroup c (f c) : Subgroup (rationalPoints G)) :
          Set (rationalPoints G)) := by
  classical
  let H := fun j => D.selectedDepthSubgroup Ψ f (a j)
  have hcollect : Set.range (RelativeRoot.CentralExtension.orderedProduct
      (fun j => (H j).subtype)) = ((⨆ j, H j : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)) := by
    apply Langlands.GroupTheory.HeightCollection.range_orderedProduct_eq_iSup
      (w := fun j => (latticePairing S (a j) ν).toNat)
    intro j k
    by_cases hj : a j ∈ Ψ
    · by_cases hk : a k ∈ Ψ
      · have hjH : H j = D.subgroup (a j) (f (a j)) := ite_eq_left hj
        have hkH : H k = D.subgroup (a k) (f (a k)) := ite_eq_left hk
        rw [hjH, hkH]
        refine (commutator_height D hdata hj hk).trans ?_
        refine iSup_le fun c => iSup_le fun hc => ?_
        obtain ⟨l, hl⟩ := hcover c.2
        exact le_iSup_of_le l (le_iSup_of_le (hl.symm ▸ hc)
          (by dsimp only [H, selectedDepthSubgroup]
              rw [hl, ite_eq_left c.2]))
      · simp only [H, selectedDepthSubgroup, ite_eq_right hk,
          Subgroup.commutator_bot_right, bot_le]
    · simp only [H, selectedDepthSubgroup, ite_eq_right hj,
        Subgroup.commutator_bot_left, bot_le]
  rw [hcollect]
  apply congrArg (fun H : Subgroup (rationalPoints G) => (H : Set (rationalPoints G)))
  apply le_antisymm
  · refine iSup_le fun j => ?_
    dsimp only [H, selectedDepthSubgroup]
    split_ifs with hj
    · exact le_iSup_of_le (⟨a j, hj⟩ : Ψ) le_rfl
    · exact bot_le
  · refine iSup_le fun c => ?_
    obtain ⟨j, hj⟩ := hcover c.2
    exact le_iSup_of_le j (by
      dsimp only [H, selectedDepthSubgroup]
      rw [hj, ite_eq_left c.2])

/-- Arbitrary-depth collection compressed to the supplied primitive/double
positions. A selected doubled root whose primitive is absent is retained as
an actual doubled-root factor at its original depth. -/
theorem orderedRayDepthProduct_eq_iSup
    (hdouble : ∀ a ∈ Ψ, 2 • a ∈ Ψ → 2 * f a ≤ f (2 • a))
    {n : ℕ} (a : Fin n → characterLattice S)
    (hcover : ∀ b ∈ Ψ, ∃ j, b = a j ∨ b = 2 • a j) :
    D.orderedRayDepthProduct Ψ f a =
      ((⨆ c : Ψ, D.subgroup c (f c) : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)) := by
  classical
  let c : Fin (n * 2) → characterLattice S := fun l =>
    if (finProdFinEquiv.symm l).2 = 0 then a (finProdFinEquiv.symm l).1
      else 2 • a (finProdFinEquiv.symm l).1
  let H := fun l => D.selectedDepthSubgroup Ψ f (c l)
  let K := fun j => D.rayDepthSubgroup Ψ f (a j)
  have hc0 (j : Fin n) : c (finProdFinEquiv (j, 0)) = a j := by
    simp only [c, Equiv.symm_apply_apply, ite_true]
  have hc1 (j : Fin n) : c (finProdFinEquiv (j, 1)) = 2 • a j := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [c, Equiv.symm_apply_apply, ite_eq_right h10]
  have hcover' : Ψ ⊆ Set.range c := by
    intro b hb
    obtain ⟨j, hj | hj⟩ := hcover b hb
    · exact ⟨finProdFinEquiv (j, 0), (hc0 j).trans hj.symm⟩
    · exact ⟨finProdFinEquiv (j, 1), (hc1 j).trans hj.symm⟩
  have hsup (j) : K j = H (finProdFinEquiv (j, 0)) ⊔
      H (finProdFinEquiv (j, 1)) := by
    dsimp only [K, H]
    rw [hc0, hc1]
    exact D.rayDepthSubgroup_eq_sup (fun _ hb => (hdata.positive hb).1)
      hdouble (a j)
  have hcomp (j) :
      H (finProdFinEquiv (j, 1)) ≤ H (finProdFinEquiv (j, 0)) ∨
      H (finProdFinEquiv (j, 0)) ≤ H (finProdFinEquiv (j, 1)) := by
    dsimp only [H]
    rw [hc0, hc1]
    by_cases hj : a j ∈ Ψ
    · left
      by_cases h2j : 2 • a j ∈ Ψ
      · simpa only [selectedDepthSubgroup, ite_eq_left hj, ite_eq_left h2j] using
          D.double_le _ (hdata.positive hj).1
            (hdata.positive h2j).1 _ _ (hdouble _ hj h2j)
      · simp only [selectedDepthSubgroup, ite_eq_right h2j, bot_le]
    · right
      simp only [selectedDepthSubgroup, ite_eq_right hj, bot_le]
  change Set.range (RelativeRoot.CentralExtension.orderedProduct
    (fun j => (K j).subtype)) = _
  rw [← range_orderedProduct_rayPairs H K hsup hcomp]
  exact range_selectedDepthProduct_eq_iSup D hdata c hcover'


/-- The collected ray product has exactly the original generated-filtration carrier. -/
theorem orderedRayDepthProduct_eq_closure
    (hdouble : ∀ a ∈ Ψ, 2 • a ∈ Ψ → 2 * f a ≤ f (2 • a))
    {n : ℕ} (a : Fin n → characterLattice S)
    (hcover : ∀ b ∈ Ψ, ∃ j, b = a j ∨ b = 2 • a j) :
    D.orderedRayDepthProduct Ψ f a =
      (Subgroup.closure (⋃ c : Ψ, rootFiltration i φ c (f c)) :
        Set (rationalPoints G)) := by
  rw [D.orderedRayDepthProduct_eq_iSup hdata hdouble a hcover]
  congr 1
  rw [Subgroup.closure_iUnion]
  simp only [← D.coe_subgroup, Subgroup.closure_eq]

end RootDepthCollectionData

end Langlands.Geometry.Building

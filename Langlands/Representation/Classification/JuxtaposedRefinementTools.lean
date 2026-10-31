import Langlands.Representation.Classification.Segments
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof

/-!
# Shared coordinates and factor equivalences for juxtaposed induction

Internal helpers for the increasing-embedding and decreasing-quotient constructions.
-/

noncomputable section

namespace Langlands.Classification.JuxtaposedShuffle

open CategoryTheory GeneralLinear Geometric PadicField.TopologicalData Finset

universe uF uV

/-- Regrouping index compatibility: if the numbering `e` of the inner blocks is
lexicographic, the coordinates of the inner block `(j, k)` are those of block
`e (j, k)` of `B`. -/
theorem index_index_eq_of_lt_iff {n : ℕ} (B D : BlockShape n) (S : BlockRefinement D)
    (e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin B.length)
    (h : ∀ a, (S a.1).size a.2 = B.size (e a))
    (he : ∀ a a', e a < e a' ↔ a.1 < a'.1 ∨ (a.1 = a'.1 ∧ a.2.val < a'.2.val))
    (j : Fin D.length) (k : Fin (S j).length) (x : Fin ((S j).size k)) :
    D.index j ((S j).index k x) = B.index (e ⟨j, k⟩) (Fin.cast (h ⟨j, k⟩) x) := by
  have hs : ∀ i, B.size i = (S (e.symm i).1).size (e.symm i).2 := fun i => by
    rw [h, Equiv.apply_symm_apply]
  let ψ : B.Index → Fin n := fun y =>
    D.index (e.symm y.1).1 ((S (e.symm y.1).1).index (e.symm y.1).2 (Fin.cast (hs y.1) y.2))
  have hψ : ∀ y y' : B.Index, B.indexEquiv y < B.indexEquiv y' → ψ y < ψ y' := by
    rintro ⟨i, c⟩ ⟨i', c'⟩ hyy
    rcases (B.index_lt_iff c c').mp hyy with hi | ⟨rfl, hc⟩
    · have hlt : e (e.symm i) < e (e.symm i') := by
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hi
      exact D.index_index_lt S _ _ _ _
        (((he _ _).mp hlt).imp_right fun h => ⟨h.1, Or.inl h.2⟩)
    · exact D.index_index_lt S _ _ _ _ (Or.inr ⟨rfl, Or.inr ⟨rfl, hc⟩⟩)
  have hmono : StrictMono (ψ ∘ B.indexEquiv.symm) := by
    intro a b hab
    apply hψ
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hab
  have hfix (y : B.Index) : ψ y = B.indexEquiv y := by
    have h' : (ψ ∘ B.indexEquiv.symm) (B.indexEquiv y) = B.indexEquiv y :=
      le_antisymm hmono.apply_le hmono.le_apply
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h'
  have gen : ∀ (a : (j : Fin D.length) × Fin (S j).length) (_ : a = ⟨j, k⟩)
      (pf : (S j).size k = (S a.1).size a.2),
      D.index a.1 ((S a.1).index a.2 (Fin.cast pf x)) = D.index j ((S j).index k x) := by
    rintro a rfl pf
    rfl
  exact (gen _ (e.symm_apply_apply _) ((h ⟨j, k⟩).trans (hs _))).symm.trans
    (hfix ⟨e ⟨j, k⟩, Fin.cast (h ⟨j, k⟩) x⟩)

theorem val_finSigmaFinEquiv_fin_two {n : Fin 2 → ℕ} (x : (j : Fin 2) × Fin (n j)) :
    (finSigmaFinEquiv x : ℕ) = (if x.1.val = 0 then 0 else n 0) + x.2 := by
  rw [finSigmaFinEquiv_apply]
  obtain ⟨j, k⟩ := x
  fin_cases j <;> simp

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Twists by equal characters are isomorphic. -/
def twistCongrIso {G : Type uF} [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, uF, uV} ℂ G) {χ χ' : G →* ℂˣ} (h : χ = χ')
    (hχ : IsOpen (χ.ker : Set G)) (hχ' : IsOpen (χ'.ker : Set G)) :
    A.twist χ hχ ≅ A.twist χ' hχ' := by
  subst h
  exact Iso.refl _

/-- `ν^s (ν^a A) ≅ ν^(s+a) A`. -/
def segmentFactorTwistIso {r : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (a s : ℝ) :
    letI := T.topology
    T.segmentFactor (A.twist (T.determinantPowerCharacter r a)
        (T.isOpen_ker_determinantPowerCharacter r a)) s ≅ T.segmentFactor A (s + a) := by
  let := T.topology
  have hχ : T.determinantPowerCharacter r s * T.determinantPowerCharacter r a =
      T.determinantPowerCharacter r (s + a) := (realPowerCharacter_add _ s a).symm
  have hker : IsOpen ((T.determinantPowerCharacter r s * T.determinantPowerCharacter r a).ker :
      Set (GeneralLinear r F.Carrier)) := by
    rw [hχ]
    exact T.isOpen_ker_determinantPowerCharacter r (s + a)
  exact SmoothRep.twistTwistIso _ _ _ _ hker A ≪≫ twistCongrIso A hχ _ _

/-- The block factor `ν^s A'` of a representative `A'` of `ν^a ρ`, transported to the
rank of `ρ`, is isomorphic to `ν^(s+a) A` for a representative `A` of `ρ`. -/
theorem nonempty_cast_iso {ρ : CuspidalDatum.{uV, uF} T}
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (a : ℝ) {ρ' : CuspidalDatum.{uV, uF} T}
    (hρ' : ρ' = ρ.twist a)
    (A' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ'.rank))
    (hA' : ρ'.IsRepresentedBy A') (h : ρ.rank = ρ'.rank) (s : ℝ)
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear ρ.rank F.Carrier))
    (eX : letI := T.topology; X ≅ T.segmentFactor A.obj (s + a)) :
    letI := T.topology
    Nonempty ((h ▸ X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear ρ'.rank F.Carrier)) ≅
      T.segmentFactor A'.obj s) := by
  let := T.topology
  subst hρ'
  have hcls : A'.isoClass = (SupercuspidalRep.twist (T.determinantPowerCharacter ρ.rank a)
      (T.isOpen_ker_determinantPowerCharacter _ _)
      (T.ker_determinant_le_ker_determinantPowerCharacter _ _) A).isoClass := by
    rw [hA']
    change T.supercuspidalClassRealPowerTwist ρ.rank a ρ.cls =
      T.supercuspidalClassRealPowerTwist ρ.rank a A.isoClass
    rw [hA]
  obtain ⟨eA⟩ := (SupercuspidalRep.isoClass_eq_iff _ _).mp hcls
  have eA' := (supercuspidalProperty (F := F.Carrier) (n := ρ.rank)).ι.mapIso eA
  exact ⟨eX ≪≫ (segmentFactorTwistIso T A.obj a s).symm ≪≫
    (SmoothRep.twistIso _ (T.isOpen_ker_determinantPowerCharacter ρ.rank s) eA').symm⟩

/-- Regroup a product along a refinement and replace each inner product by an
isomorphic representation. -/
theorem regroup_nonempty_iso {n : ℕ} (B D : BlockShape n) (S : BlockRefinement D)
    (e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin B.length)
    (h : ∀ a, (S a.1).size a.2 = B.size (e a))
    (hc : ∀ j k (x : Fin ((S j).size k)),
      D.index j ((S j).index k x) = B.index (e ⟨j, k⟩) (Fin.cast (h ⟨j, k⟩) x))
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (τ : letI := T.topology
      ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (D.size j) F.Carrier))
    (f : letI := T.topology
      ∀ j, Nonempty ((T.normalizedProductInductionFunctor.{uF, uV} (S j)).obj
        (fun k => (h ⟨j, k⟩).symm ▸ σ (e ⟨j, k⟩)) ≅ τ j)) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor.{uF, uV} B).obj σ ≅
      (T.normalizedProductInductionFunctor.{uF, max uF uV} D).obj τ) := by
  let := T.topology
  obtain ⟨ereg⟩ := Parabolic.orderedProductRegrouping.{uF, uV} F T n B D S e h hc σ
  exact ⟨ereg ≪≫ (T.normalizedProductInductionFunctor.{uF, max uF uV} D).mapIso
    (Pi.isoMk fun j => (f j).some)⟩

end Langlands.Classification.JuxtaposedShuffle

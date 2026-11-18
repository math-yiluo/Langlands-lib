import Langlands.Correspondence.BushnellKutzkoLabelSupports
import Mathlib.FieldTheory.Galois.Basic

/-!
# Cardinality of the Bushnell–Kutzko polar-part model

The Galois action on a generating polar part is free. Its order accounts for the
choices of successive roots when passing from the polynomial towers to polar-part orbits.
-/

noncomputable section

namespace Langlands.Henniart.LabelCounting

open BushnellKutzko FieldTheory Numerical IntermediateField

private theorem polarPart_stabilizer_eq_bot {k L : Type*} [Field k] [Field L] [Algebra k L]
    {a m : ℕ} (c : polarParts k L a m) : MulAction.stabilizer Gal(L/k) c = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro g hg
  have hgen : adjoin k (Set.range c.val) = ⊤ := c.property.2.2.1
  have hfix : g ∈ (adjoin k (Set.range c.val)).fixingSubgroup := by
    rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    change c.val i ∈ fixedField (Subgroup.zpowers g)
    rw [mem_fixedField_iff]
    rintro _ ⟨j, rfl⟩
    have hi : g (c.val i) = c.val i :=
      congrArg (fun c' : polarParts k L a m => c'.val i) (MulAction.mem_stabilizer_iff.mp hg)
    exact MulAction.mem_fixedBy_zpow (g := g) hi j
  rwa [hgen, fixingSubgroup_top] at hfix

private theorem card_polarParts (q f : ℕ) [NeZero f] (a m : ℕ) :
    Nat.card (polarParts (BaseField q) (ExtensionField q f) a m) =
      polarPartCountOf (BaseField q) (ExtensionField q f) a m * f := by
  let e := MulAction.selfEquivOrbitsQuotientProd polarPart_stabilizer_eq_bot
    (G := Gal(ExtensionField q f / BaseField q))
    (X := polarParts (BaseField q) (ExtensionField q f) a m)
  rw [Nat.card_congr e, Nat.card_prod]
  exact congrArg (polarPartCountOf (BaseField q) (ExtensionField q f) a m * ·)
    (FiniteField.natCard_algEquiv_extension (BaseField q) (labelFieldSize q).minFac f)

private theorem card_eq_polarPartCountOf {α : Type*} {q f : ℕ} [NeZero f] {a m : ℕ}
    (e : polarParts (BaseField q) (ExtensionField q f) a m ≃ α × Fin f) :
    ENat.card α = (polarPartCountOf (BaseField q) (ExtensionField q f) a m : ℕ∞) := by
  have hf : 0 < f := Nat.pos_of_ne_zero (NeZero.ne f)
  let : Finite α := Finite.of_injective (fun x : α => e.symm (x, ⟨0, hf⟩))
    (fun _ _ h => congrArg Prod.fst (e.symm.injective h))
  have hc := Nat.card_congr e
  rw [Nat.card_prod, Nat.card_fin, card_polarParts] at hc
  rw [ENat.card_eq_coe_natCard, Nat.eq_of_mul_eq_mul_right hf hc.symm]

private theorem polarPartCount_eq_labelField (q n f s : ℕ) [NeZero f]
    (hq : IsPrimePow q) (hn : 1 ≤ n) (hf : 1 ≤ f) (hfn : f ∣ n) (hfs : f ∣ s) :
    polarPartCount q n f s =
      polarPartCountOf (BaseField q) (ExtensionField q f) (n / f) (s / f) := by
  have he : labelFieldSize q = q := ite_eq_right hq.ne_one
  have hq' : IsPrimePow (labelFieldSize q) := he.symm ▸ hq
  conv_lhs => rw [← he]
  unfold polarPartCount
  rw [dite_eq_left ⟨hq', hn, hf, hfn, hfs⟩]

/-- A set equivalent to the positive-level data is counted by `polarPartCount`. -/
theorem encard_eq_polarPartCount_of_equiv {α : Type*} {s : Set α} {q n f m : ℕ}
    (hq : IsPrimePow q) (hn : 1 ≤ n) (hf : 1 ≤ f) (hfn : f ∣ n) (hm : 1 ≤ m)
    (e : s ≃ Σ r : ℕ, PositiveLevels m (n / f) r × PolynomialTowers q (r + 2) f) :
    s.encard = (polarPartCount q n f (f * m) : ℕ∞) := by
  let : NeZero f := ⟨Nat.ne_of_gt hf⟩
  rw [polarPartCount_eq_labelField q n f (f * m) hq hn hf hfn (dvd_mul_right f m),
    Nat.mul_div_cancel_left m hf]
  apply card_eq_polarPartCountOf (q := q) (f := f)
  calc
    _ ≃ SupportedTuples (BaseField q) (ExtensionField q f) m (n / f) :=
      polarPartsEquiv hm
    _ ≃ Σ r : ℕ, (PositiveLevels m (n / f) r × PolynomialTowers q (r + 2) f) × Fin f :=
      Equiv.sigmaCongrRight fun _ =>
        (Equiv.prodCongr (Equiv.refl _) (generatingTupleEquiv q)).trans
          (Equiv.prodAssoc _ _ _).symm
    _ ≃ (Σ r : ℕ, PositiveLevels m (n / f) r × PolynomialTowers q (r + 2) f) × Fin f :=
      (Equiv.sigmaProdDistrib _ _).symm
    _ ≃ _ := Equiv.prodCongr e.symm (Equiv.refl _)

private def oneDegreeProfile (n : ℕ) (hn : 1 ≤ n) : DegreeProfile 1 n where
  degree := fun _ => n
  pos _ := hn
  prod_eq := Fin.prod_univ_one _

private def polynomialLabelsExponentEquiv (q n : ℕ) {e e' : ℕ+} (he : e = e') :
    ↥(irreduciblePolynomialLabels n (ExtensionField q e)) ≃
      ↥(irreduciblePolynomialLabels n (ExtensionField q e')) := by
  subst e'
  exact Equiv.refl _

private def oneTowerEquiv (q n : ℕ) (hq : IsPrimePow q) (hn : 1 ≤ n) :
    PolynomialTowers q 1 n ≃ degenerateLabelSet n q := by
  let d := oneDegreeProfile n hn
  letI : Unique (DegreeProfile 1 n) :=
    { default := d
      uniq := fun D => by
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simpa only [d, oneDegreeProfile, Fin.prod_univ_one] using D.prod_eq }
  have hexp : d.exponent 0 = 1 := Subtype.ext (by simp [DegreeProfile.exponent])
  calc
    _ ≃ TowerPolynomials q d := Equiv.uniqueSigma _
    _ ≃ irreduciblePolynomialLabels n (ExtensionField q (d.exponent 0)) := Equiv.piUnique _
    _ ≃ irreduciblePolynomialLabels n (ExtensionField q 1) :=
      polynomialLabelsExponentEquiv q n (e := d.exponent 0) (e' := 1) hexp
    _ ≃ _ := Equiv.subtypeEquivRight fun _ => ⟨fun h => ⟨hq, h⟩, And.right⟩

/-- At level zero the count is the cardinality of the degenerate polynomial labels. -/
theorem degenerateLabelSet_encard (q n : ℕ) (hq : IsPrimePow q) (hn : 1 ≤ n) :
    (degenerateLabelSet n q).encard = (polarPartCount q n n 0 : ℕ∞) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [polarPartCount_eq_labelField q n n 0 hq hn hn (dvd_refl n) (dvd_zero n),
    Nat.div_self hn, Nat.zero_div]
  apply card_eq_polarPartCountOf (q := q) (f := n)
  exact zeroPolarPartsEquiv.trans <| (generatingTupleEquiv q).trans <|
    Equiv.prodCongr (oneTowerEquiv q n hq hn) (Equiv.refl _)

end Langlands.Henniart.LabelCounting

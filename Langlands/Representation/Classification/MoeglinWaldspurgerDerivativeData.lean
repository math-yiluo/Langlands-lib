import Langlands.Representation.Classification.LeftCuspidalDerivativeStatement
import Langlands.Representation.Classification.MoeglinWaldspurgerLabelInduction

/-!
# The concrete highest left derivative relation on a cuspidal line

For a cuspidal datum `ρ` and a real `x`, choose actual supercuspidal representatives of the
twists `ν^{x+c} ρ`. The relation `LDrel c cls K S` says that some representative of `cls`
embeds into `A^K × D` for a left `A`-reduced irreducible representative `D` of `S`, where `A`
represents `ν^{x+c} ρ`. Its uniqueness is the uniqueness clause of the left cuspidal derivative
lemma.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Aubert.SegmentPolynomialSurjectivity
open Langlands.Classification.LeftCuspidalDerivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ)

/-- A chosen actual supercuspidal representative of `ν^{x+c} ρ`. -/
def cuspRep (c : ℤ) :
    letI := T.topology
    GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := ρ.rank) :=
  Quotient.out (ρ.twist (x + (c : ℝ))).cls

theorem cuspRep_represents (c : ℤ) :
    (ρ.twist (x + (c : ℝ))).IsRepresentedBy (cuspRep F T ρ x c) :=
  Quotient.out_eq _

/-- The highest left derivative relation with respect to `ν^{x+c} ρ`, at the level of
irreducible classes. -/
def LDrel (c : ℤ) {n m : ℕ} (cls : Label.{uF, uV} F T n) (K : ℕ)
    (S : Label.{uF, uV} F T m) : Prop :=
  letI := T.topology
  ∃ (h : powerRank ρ.rank K m = n)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (hπ : π.IsIrreducible)
    (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) (hD : D.IsIrreducible),
    GeneralLinear.irreducibleIsoClass n F.Carrier π hπ = cls ∧
      GeneralLinear.irreducibleIsoClass m F.Carrier D hD = S ∧
      LeftReduced F T (cuspRep F T ρ x c) D ∧
      SmoothRep.IsSubrepresentation π (T.castRank h (powerProduct F T (cuspRep F T ρ x c) K D))

variable {F T}

omit [Fact p.Prime] in
theorem isSubrepresentation_of_iso
    {G : Type*} [Group G] [TopologicalSpace G]
    {A B C : SmoothRep.{0, _, _} ℂ G} (h : SmoothRep.IsSubrepresentation A B) (e : B ≅ C) :
    SmoothRep.IsSubrepresentation A C := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f ≫ e.hom, ?_⟩
  intro u v huv
  apply hf
  have key : ∀ w, SmoothRep.hom e.inv (SmoothRep.hom (f ≫ e.hom) w) = SmoothRep.hom f w := by
    intro w
    change SmoothRep.hom (f ≫ e.hom ≫ e.inv) w = _
    simp
  rw [← key u, ← key v, huv]

variable (F T)

/-- `A^K × -` carries isomorphisms to isomorphisms. -/
def powerProductIso {d : ℕ}
    (A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)) :
    (K : ℕ) → {m : ℕ} →
      {Y Y' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)} →
      (Y ≅ Y') → (powerProduct F T A K Y ≅ powerProduct F T A K Y')
  | 0, _, _, _, e => e
  | K + 1, m, _, _, e =>
    letI := T.topology
    (T.binaryNormalizedProductFunctor d (powerRank d K m)).mapIso
      (Iso.prod (Iso.refl _) (powerProductIso A K e))

/-- **Uniqueness of the derivative data.** -/
theorem LDrel_unique (hL : LeftCuspidalDerivativeLemma.{uF, uV}) (c : ℤ) {n m : ℕ}
    (cls cls' : Label.{uF, uV} F T n) (K : ℕ) (S : Label.{uF, uV} F T m)
    (h₁ : LDrel F T ρ x c cls K S) (h₂ : LDrel F T ρ x c cls' K S) : cls = cls' := by
  let := T.topology
  obtain ⟨h, π, hπ, D, hD, rfl, hDS, hred, hsub⟩ := h₁
  obtain ⟨h', π', hπ', D', hD', rfl, hDS', -, hsub'⟩ := h₂
  subst h
  have hh : h' = rfl := rfl
  subst hh
  have e : D' ≅ D := ((SmoothRep.irreducibleIsoClass_eq_iff hD' hD).mp (hDS'.trans hDS.symm)).some
  have hsub'' : SmoothRep.IsSubrepresentation π' (powerProduct F T (cuspRep F T ρ x c) K D) :=
    isSubrepresentation_of_iso hsub'
      (powerProductIso F T (cuspRep F T ρ x c) K e)
  obtain ⟨-, -, -, huniq, -⟩ := hL p F T ρ.rank (cuspRep F T ρ x c)
  exact (SmoothRep.irreducibleIsoClass_eq_iff hπ hπ').mpr
    (huniq K m D π π' hD hred hπ hπ' hsub hsub'')

end Langlands.MoeglinWaldspurger.Derivation

import Langlands.Representation.Classification.MoeglinWaldspurgerDerivativeData
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Induction.BinaryProductSubquotients
import Langlands.Representation.Aubert.GradedGrothendieck
import Langlands.Representation.Classification.SegmentHeadSupportStep
import Langlands.Representation.Smooth.IrreducibleRealization

/-!
# Transport lemmas for embeddings into iterated cuspidal products

Generic facts about subrepresentations, left reducedness and the iterated products
`A × (A × ⋯ × Y)`: transport along isomorphisms and rank casts, finite length, and
functoriality in the last factor.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData
open Langlands.Classification.LeftCuspidalDerivative Aubert.SegmentPolynomialSurjectivity

universe uF uV

section General

variable {G : Type*} [Group G] [TopologicalSpace G]

theorem isSubrepresentation_trans {A B C : SmoothRep.{0, _, _} ℂ G}
    (h₁ : SmoothRep.IsSubrepresentation A B) (h₂ : SmoothRep.IsSubrepresentation B C) :
    SmoothRep.IsSubrepresentation A C := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨f ≫ g, fun u v huv => hf (hg huv)⟩

theorem isSubrepresentation_of_iso_left {A A' B : SmoothRep.{0, _, _} ℂ G}
    (e : A ≅ A') (h : SmoothRep.IsSubrepresentation A B) :
    SmoothRep.IsSubrepresentation A' B := by
  obtain ⟨f, hf⟩ := h
  refine ⟨e.inv ≫ f, fun u v huv => ?_⟩
  have h1 := hf huv
  have key : ∀ w, SmoothRep.hom e.hom (SmoothRep.hom e.inv w) = w := by
    intro w
    change SmoothRep.hom (e.inv ≫ e.hom) w = _
    simp
  rw [← key u, ← key v]
  exact congrArg _ h1

theorem isSubrepresentation_refl (A : SmoothRep.{0, _, _} ℂ G) :
    SmoothRep.IsSubrepresentation A A :=
  ⟨𝟙 A, fun _ _ h => h⟩

theorem isSubrepresentation_of_iso' {A B : SmoothRep.{0, _, _} ℂ G} (e : A ≅ B) :
    SmoothRep.IsSubrepresentation A B :=
  isSubrepresentation_of_iso (isSubrepresentation_refl A) e

end General

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

theorem isSubrepresentation_castRank {r s : ℕ} (h : r = s)
    {A B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)}
    (hAB : letI := T.topology; SmoothRep.IsSubrepresentation A B) :
    letI := T.topology; SmoothRep.IsSubrepresentation (T.castRank h A) (T.castRank h B) := by
  subst h
  exact hAB

theorem leftReduced_of_iso {d : ℕ}
    {A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)}
    {m : ℕ} {Y Y' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (e : Y ≅ Y') (h : LeftReduced F T A Y) : LeftReduced F T A Y' := by
  let := T.topology
  intro Z hZ hZY k hk σ
  exact h Z hZ (SmoothRep.IsSubquotient.of_iso_right hZY e.symm) k hk σ

theorem supercuspidal_hasFiniteLength {d : ℕ}
    (A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)) :
    letI := T.topology; A.obj.HasFiniteLength := by
  let := T.topology
  exact SmoothRep.hasFiniteLength_of_isIrreducible A.property.1

theorem powerProduct_hasFiniteLength {d : ℕ}
    (A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)) :
    ∀ (K : ℕ) {m : ℕ}
      {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)},
      (letI := T.topology; Y.HasFiniteLength) →
        (letI := T.topology; (powerProduct F T A K Y).HasFiniteLength)
  | 0, _, _, hY => hY
  | K + 1, m, Y, hY => by
    let := T.topology
    exact Aubert.binaryProduct_preservesFiniteLength F T d (powerRank d K m) A.obj
      (powerProduct F T A K Y) (supercuspidal_hasFiniteLength A)
      (powerProduct_hasFiniteLength A K hY)

/-- `A^K × -` carries subrepresentations to subrepresentations. -/
theorem powerProduct_mono {d : ℕ}
    (A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)) :
    ∀ (K : ℕ) {m : ℕ}
      {Y Y' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)},
      (letI := T.topology; SmoothRep.IsSubrepresentation Y Y') →
        (letI := T.topology;
          SmoothRep.IsSubrepresentation (powerProduct F T A K Y) (powerProduct F T A K Y'))
  | 0, _, _, _, h => h
  | K + 1, m, Y, Y', h => by
    let := T.topology
    obtain ⟨f, hf⟩ := powerProduct_mono A K h
    let g : (A.obj, powerProduct F T A K Y) ⟶ (A.obj, powerProduct F T A K Y') := (𝟙 _, f)
    exact ⟨(T.binaryNormalizedProductFunctor d (powerRank d K m)).map g,
      T.binaryProductMap_injective g (fun _ _ h => h) hf⟩

/-! ### From an embedding to the derivative relation -/

variable (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ)

/-- **Comparison wrapper.** If an irreducible `π` embeds into `A^K × Y` for a finite-length
left-reduced `Y` whose irreducible subrepresentations all have class `S`, and some irreducible
subrepresentation of `Y` exists, then `(K, S)` is the derivative datum of the class of `π`. -/
theorem LDrel_of_embedding (hL : LeftCuspidalDerivativeLemma.{uF, uV}) (c : ℤ) {K m n : ℕ}
    (h : powerRank ρ.rank K m = n)
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible)
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hYf : letI := T.topology; Y.HasFiniteLength)
    (hYred : LeftReduced F T (cuspRep F T ρ x c) Y)
    (S : Label.{uF, uV} F T m)
    (hYS : letI := T.topology; ∀ (Z : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (hZ : Z.IsIrreducible), SmoothRep.IsSubrepresentation Z Y →
        GeneralLinear.irreducibleIsoClass m F.Carrier Z hZ = S)
    (hex : letI := T.topology; ∃ (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      D.IsIrreducible ∧ SmoothRep.IsSubrepresentation D Y)
    (hsub : letI := T.topology;
      SmoothRep.IsSubrepresentation π (T.castRank h (powerProduct F T (cuspRep F T ρ x c) K Y))) :
    LDrel F T ρ x c (letI := T.topology; GeneralLinear.irreducibleIsoClass n F.Carrier π hπ)
      K S := by
  let := T.topology
  obtain ⟨D, hD, hDY⟩ := hex
  obtain ⟨hsq, -, hcmp, -, -⟩ := hL p F T ρ.rank (cuspRep F T ρ x c)
  have hDS := hYS D hD hDY
  have hDred : LeftReduced F T (cuspRep F T ρ x c) D :=
    hsq m Y D hYf (SmoothRep.IsSubrepresentation.isSubquotient hDY) hYred
  subst h
  have hall : ∀ Z : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier),
      Z.IsIrreducible → SmoothRep.IsSubrepresentation Z Y → Nonempty (Z ≅ D) := by
    intro Z hZ hZY
    exact (SmoothRep.irreducibleIsoClass_eq_iff hZ hD).mp ((hYS Z hZ hZY).trans hDS.symm)
  have hπD := hcmp K m π Y D hYf hπ hD hYred hall hsub
  exact ⟨rfl, π, hπ, D, hD, rfl, hDS, hDred, hπD⟩

end Langlands.MoeglinWaldspurger.Derivation

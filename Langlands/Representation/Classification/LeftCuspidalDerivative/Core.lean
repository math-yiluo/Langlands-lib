import Langlands.Representation.Classification.LeftCuspidalDerivative.PowerSupport
import Langlands.Representation.Geometric.ReversedIdentityPiece
import Langlands.Representation.Exponents.WeylBranchMultiplicityExtraction
import Langlands.Representation.Classification.UnlinkedSocleProductIrreducibilityProof
import Langlands.Representation.Smooth.IrreducibleCompositionFactors

/-!
# The Jacquet module of `𝔄 × E` along `(a, m)`

Let `A` be a supercuspidal representation of `GL_d`, `𝔄` an irreducible `A`-pure
representation of `GL_a` (`a > 0`) and `E` an irreducible left `A`-reduced representation of
`GL_m` (`m > 0`). In the geometric lemma filtration of the Jacquet module of `𝔄 × E` along
`(a, m)`:

* the identity piece is `𝔄 ⊠ E` (`nonempty_identityPieceEquiv`);
* no other piece has `𝔄` as a first-block subquotient
  (`not_isSubquotient_geometricPiece_of_ne_one`).

Consequently every irreducible subquotient `Z` of that Jacquet module whose first-block
restriction has `𝔄` as a subquotient is equivalent to `𝔄 ⊠ E`
(`nonempty_equiv_of_isSubquotient_jacquetInduction`), and `𝔄 ⊠ E` occurs with
Jordan–Hölder multiplicity one (`multiplicity_eq_one_jacquetInduction`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear Geometric CuspidalSupport BinaryGeometricPieces PadicField.TopologicalData
open OppositeCuspidalJacquetFiltration

universe uF uV uG uX uC vC

section External

variable {ι : Type} [Fintype ι] {H : ι → Type uG} [∀ i, Group (H i)]
  [∀ i, TopologicalSpace (H i)]

/-- An external tensor product of irreducible admissible smooth representations is
irreducible. -/
theorem isIrreducible_externalSmoothObject (C : ∀ i, SmoothRep.{0, uG, uV} ℂ (H i))
    (hi : ∀ i, (C i).IsIrreducible) (ha : ∀ i, (C i).IsAdmissible) :
    (FiniteTensor.externalSmoothObject C).IsIrreducible := by
  classical
  have : ∀ i, (C i).representation.IsIrreducible := hi
  exact FiniteTensor.isIrreducible_external (fun i => (C i).representation)
    (fun i φ => (admissibleSchur_scalarEndomorphism _ (ha i) (hi i) φ).exists)

end External

section Glued

variable {G : Type uG} [Group G] {X : Type uX} [AddCommGroup X] [Module ℂ X]
  {C : Type uC} [Category.{vC} C]

/-- An irreducible subquotient of a glued representation is a subquotient of one piece. -/
theorem exists_isSubquotient_piece {F : C ⥤ Rep.{uV} ℂ G} {n : ℕ}
    {pieces : Fin n → C ⥤ Rep.{uV} ℂ G} (h : IsGluedFrom F pieces) (Y : C)
    {ρ : Representation ℂ G X} (hirr : ρ.IsIrreducible)
    (hρ : WeylBranchPieces.IsSubquotient (F.obj Y).ρ ρ) :
    ∃ i : Fin n, WeylBranchPieces.IsSubquotient ((pieces i).obj Y).ρ ρ := by
  have := hirr
  obtain ⟨e, s, hs⟩ := h
  obtain ⟨j, hj⟩ := WeylBranchPieces.exists_isSubquotient_graded s Y hρ
  obtain ⟨ψ⟩ := hs j
  exact ⟨e j, (WeylBranchPieces.isSubquotient_of_iso (ψ.app Y).symm).trans hj⟩

/-- If one piece of a glued representation has multiplicity one with respect to `τ` and no
other piece has `τ` as a subquotient, the glued representation has multiplicity one. -/
theorem multiplicity_eq_one_of_isGluedFrom {F : C ⥤ Rep.{uV} ℂ G} {n : ℕ}
    {pieces : Fin n → C ⥤ Rep.{uV} ℂ G} (h : IsGluedFrom F pieces) (Y : C)
    {τ : Rep.{uX} ℂ G} {M : ℕ} (hM : HasJordanHolderMultiplicity (F.obj Y) τ M) (i₀ : Fin n)
    (h₀ : HasJordanHolderMultiplicity ((pieces i₀).obj Y) τ 1)
    (hother : ∀ i, i ≠ i₀ → ¬ WeylBranchPieces.IsSubquotient ((pieces i).obj Y).ρ τ.ρ) :
    M = 1 := by
  classical
  obtain ⟨e, s, hs⟩ := h
  let t : ObjectRepFiltration (F.obj Y) n :=
    ObjectRepFiltration.ofSubrepresentations (fun i => (s.step i).obj Y)
      (s.monotone Y) (s.zero Y) (s.top Y)
  obtain ⟨counts, hcounts, hsum⟩ := WeylBranchPieces.grade_multiplicities t hM
  have hc : ∀ j, counts j = if e j = i₀ then 1 else 0 := by
    intro j
    obtain ⟨φ⟩ := hs j
    let E : (t.gradedRepresentation j).ρ.Equiv ((pieces (e j)).obj Y).ρ :=
      Representation.equivOfIso (φ.app Y)
    have hj := (equivJordanHolderMultiplicityTransport ℂ G (t.gradedRepresentation j)
      ((pieces (e j)).obj Y) τ τ E (Representation.Equiv.refl _) (counts j)).mp (hcounts j)
    split_ifs with hji
    · rw [hji] at hj
      exact hj.unique h₀
    · by_contra hne
      exact hother (e j) hji
        (WeylBranchPieces.isSubquotient_of_positive_multiplicity hj (Nat.pos_of_ne_zero hne))
  rw [← hsum, Finset.sum_congr rfl (fun j _ => hc j)]
  have : ∀ j, (e j = i₀) ↔ (j = e.symm i₀) := fun j => (Equiv.eq_symm_apply e).symm
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Glued

section IdentityPiece

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- **The identity piece.** The geometric piece of label `1` (source and target shape equal)
is equivalent to its smooth source. -/
theorem nonempty_identityPieceEquiv (B : BlockShape n) (w : Equiv.Perm (Fin n)) (hw1 : w = 1)
    (S : BlockRefinement B) (R : BlockRefinement B)
    (hS : sourceLevi F.Carrier B B w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier B B w⁻¹ = refinedLevi F.Carrier B R)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) :
    letI := T.topology
    Nonempty (((geometricPieceFunctor T B B w S R hS hR).obj A).ρ.Equiv A.representation) := by
  let := T.topology
  subst hw1
  have e := Langlands.Geometric.wholeConjugatingPieceEquiv T B B 1 S R hS hR (conjugatesLevi_one (F := F.Carrier) B) A
  rw [transport_one] at e
  exact ⟨e⟩

end IdentityPiece

section Exclusion

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- **Non-identity pieces.** For a label `w ≠ 1`, the irreducible `A`-pure `𝔄` is not a
first-block subquotient of the geometric piece of `r_(a,m)(𝔄 × E)` of label `w`, when `E` is
finite-length and left `A`-reduced. -/
theorem not_isSubquotient_geometricPiece_of_ne_one {d a m : ℕ} (hd : 0 < d) (ha : 0 < a)
    (hm : 0 < m)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible) (hp : IsPure T hd A 𝔄)
    {E : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hE : letI := T.topology; E.HasFiniteLength) (hr : LeftReduced F T A E)
    (w : MinimalRepresentatives (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl))
    (hw : w.val ≠ 1)
    (S : BlockRefinement (BlockShape.ofPair a m ha hm rfl))
    (R : BlockRefinement (BlockShape.ofPair a m ha hm rfl))
    (hS : IsIntersectionRefinement (F := F.Carrier) (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl) w.val S)
    (hR : IsIntersectionRefinement (F := F.Carrier) (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl) w.val⁻¹ R) :
    letI := T.topology
    ¬ WeylBranchPieces.IsSubquotient
      (((geometricPieceFunctor.{uF, max uF uV} T (BlockShape.ofPair a m ha hm rfl)
          (BlockShape.ofPair a m ha hm rfl) w.val S R hS.2.1 hR.2.1).obj
          (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E))).ρ.comp
        (MonoidHom.mulSingle
          (fun i => GeneralLinear ((BlockShape.ofPair a m ha hm rfl).size i) F.Carrier)
          (0 : Fin 2)))
      𝔄.representation := by
  let := T.topology
  intro hsq
  have h𝔄fl : 𝔄.HasFiniteLength := SmoothRep.hasFiniteLength_of_isIrreducible h𝔄
  have key := binaryGeometricPieceConstituents.{uF, uV} p F T a m ha hm a m ha hm rfl w S R
    hS hR 𝔄 E 𝔄 h𝔄fl hE h𝔄 (by with_reducible exact hsq)
  have hAirr : A.obj.IsIrreducible := A.property.1
  have hA𝔄 := isFirstBlockConstituent_of_isPure T hd A ha h𝔄 hp
  rcases key with ⟨h1, -⟩ | hfb | hmix
  · exact hw h1
  · exact not_leftReduced_of_isFirstBlockConstituent F T A E hE
      (isFirstBlockConstituent_trans T hE h𝔄 hAirr hfb hA𝔄) hr
  · obtain ⟨a₁, a₂, -, ha₂, ha', ρ₁, ρ₂, hρ₁, hρ₂, -, hfb₂, hsq'⟩ := hmix
    subst ha'
    have hp₂ : IsPure T hd A ρ₂ :=
      isPure_right_of_isSubquotient_binaryProduct T hd A h𝔄 hp hρ₁ hρ₂ hsq'
    have hA₂ := isFirstBlockConstituent_of_isPure T hd A ha₂ hρ₂ hp₂
    exact not_leftReduced_of_isFirstBlockConstituent F T A E hE
      (isFirstBlockConstituent_trans T hE hρ₂ hAirr hfb₂ hA₂) hr

end Exclusion

section Constituents

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- In `𝔄 ⊠ E` with `E` nonzero, `𝔄` is a subquotient of the first-block restriction. -/
theorem isSubquotient_firstBlock_twoBlock {a m : ℕ} (ha : 0 < a) (hm : 0 < m)
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible)
    {E : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hE : letI := T.topology; E.IsIrreducible) :
    letI := T.topology
    WeylBranchPieces.IsSubquotient
      ((FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).representation.comp
        (MonoidHom.mulSingle
          (fun i => GeneralLinear ((BlockShape.ofPair a m ha hm rfl).size i) F.Carrier)
          (0 : Fin 2)))
      𝔄.representation := by
  let := T.topology
  have hnt : ∀ i, Nontrivial (twoBlockFactors ha hm 𝔄 E i) := by
    intro i
    fin_cases i
    · exact nontrivial_of_isIrreducible h𝔄
    · exact nontrivial_of_isIrreducible hE
  exact isSubquotient_external_comp_mulSingle
    (fun i => (twoBlockFactors ha hm 𝔄 E i).representation) hnt 0

/-- `𝔄 ⊠ E` is irreducible for irreducible `𝔄` and `E`. -/
theorem isIrreducible_twoBlock {a m : ℕ} (ha : 0 < a) (hm : 0 < m)
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible)
    {E : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hE : letI := T.topology; E.IsIrreducible) :
    letI := T.topology
    (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).IsIrreducible := by
  let := T.topology
  have h𝔄a : 𝔄.IsAdmissible := glFiniteLengthAdmissibility.{uF, max uF uV} F T a 𝔄
    (SmoothRep.hasFiniteLength_of_isIrreducible h𝔄)
  have hEa : E.IsAdmissible := glFiniteLengthAdmissibility.{uF, max uF uV} F T m E
    (SmoothRep.hasFiniteLength_of_isIrreducible hE)
  apply isIrreducible_externalSmoothObject
  · intro i
    fin_cases i
    · exact h𝔄
    · exact hE
  · intro i
    fin_cases i
    · exact h𝔄a
    · exact hEa

/-- The `𝔄`-type constituent, given the data of the geometric lemma for `(a, m)`, `(a, m)`. -/
theorem nonempty_equiv_of_isSubquotient_glued {d a m : ℕ} (hd : 0 < d) (ha : 0 < a)
    (hm : 0 < m)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible) (hp : IsPure T hd A 𝔄)
    {E : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hE : letI := T.topology; E.IsIrreducible) (hr : LeftReduced F T A E)
    (S : MinimalRepresentatives (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl) → BlockRefinement (BlockShape.ofPair a m ha hm rfl))
    (R : MinimalRepresentatives (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl) → BlockRefinement (BlockShape.ofPair a m ha hm rfl))
    (hS : ∀ w, IsIntersectionRefinement (F := F.Carrier) (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl) w.val (S w))
    (hR : ∀ w, IsIntersectionRefinement (F := F.Carrier) (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl) w.val⁻¹ (R w))
    {n : ℕ} (eo : Fin n ≃ MinimalRepresentatives (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl))
    (hglue : letI := T.topology;
      IsGluedFrom (jacquetInductionFunctor.{uF, max uF uV} T (BlockShape.ofPair a m ha hm rfl)
          (BlockShape.ofPair a m ha hm rfl))
        (fun i => geometricPieceFunctor T (BlockShape.ofPair a m ha hm rfl)
          (BlockShape.ofPair a m ha hm rfl) (eo i).val (S (eo i)) (R (eo i))
          (hS (eo i)).2.1 (hR (eo i)).2.1))
    {V : Type uX} [AddCommGroup V] [Module ℂ V]
    {Z : Representation ℂ ((BlockShape.ofPair a m ha hm rfl).Levi F.Carrier) V}
    (hZ : Z.IsIrreducible)
    (hZsq : letI := T.topology; WeylBranchPieces.IsSubquotient
      ((jacquetInductionFunctor.{uF, max uF uV} T (BlockShape.ofPair a m ha hm rfl)
          (BlockShape.ofPair a m ha hm rfl)).obj
        (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E))).ρ Z)
    (h𝔄Z : letI := T.topology; WeylBranchPieces.IsSubquotient
      (Z.comp (MonoidHom.mulSingle
          (fun i => GeneralLinear ((BlockShape.ofPair a m ha hm rfl).size i) F.Carrier)
          (0 : Fin 2)))
      𝔄.representation) :
    letI := T.topology
    Nonempty (Z.Equiv
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).representation) := by
  let := T.topology
  have hEfl := SmoothRep.hasFiniteLength_of_isIrreducible hE
  have hXirr := isIrreducible_twoBlock F T ha hm h𝔄 hE
  obtain ⟨i, hi⟩ := exists_isSubquotient_piece hglue
    (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)) hZ hZsq
  by_cases h1 : (eo i).val = 1
  · obtain ⟨e⟩ := nonempty_identityPieceEquiv.{uF, max uF uV} T
      (BlockShape.ofPair a m ha hm rfl) (eo i).val h1 (S (eo i))
      (R (eo i)) (hS (eo i)).2.1 (hR (eo i)).2.1
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E))
    have hsq := WeylBranchPieces.IsSubquotient.of_equiv_left e.symm hi
    obtain ⟨e'⟩ := CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient hXirr hZ hsq
    exact ⟨e'.symm⟩
  · exfalso
    apply not_isSubquotient_geometricPiece_of_ne_one F T hd ha hm A h𝔄 hp hEfl hr (eo i) h1
      (S (eo i)) (R (eo i)) (hS (eo i)) (hR (eo i))
    exact (WeylBranchPieces.IsSubquotient.comp hi _).trans h𝔄Z

/-- **The `𝔄`-type constituent.** An irreducible subquotient `Z` of `r_(a,m)(𝔄 × E)` whose
first-block restriction has `𝔄` as a subquotient is equivalent to `𝔄 ⊠ E`. -/
theorem nonempty_equiv_of_isSubquotient_jacquetInduction {d a m : ℕ} (hd : 0 < d) (ha : 0 < a)
    (hm : 0 < m)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible) (hp : IsPure T hd A 𝔄)
    {E : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hE : letI := T.topology; E.IsIrreducible) (hr : LeftReduced F T A E)
    {V : Type uX} [AddCommGroup V] [Module ℂ V]
    {Z : Representation ℂ ((BlockShape.ofPair a m ha hm rfl).Levi F.Carrier) V}
    (hZ : Z.IsIrreducible)
    (hZsq : letI := T.topology; WeylBranchPieces.IsSubquotient
      ((jacquetInductionFunctor.{uF, max uF uV} T (BlockShape.ofPair a m ha hm rfl)
          (BlockShape.ofPair a m ha hm rfl)).obj
        (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E))).ρ Z)
    (h𝔄Z : letI := T.topology; WeylBranchPieces.IsSubquotient
      (Z.comp (MonoidHom.mulSingle
          (fun i => GeneralLinear ((BlockShape.ofPair a m ha hm rfl).size i) F.Carrier)
          (0 : Fin 2)))
      𝔄.representation) :
    letI := T.topology
    Nonempty (Z.Equiv
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).representation) := by
  let := T.topology
  obtain ⟨S, R, hS, hR, n, eo, hglue⟩ :=
    padicGeometricLemma.{uF, max uF uV} p F T (a + m) (by omega)
      (BlockShape.ofPair a m ha hm rfl) (BlockShape.ofPair a m ha hm rfl)
  exact nonempty_equiv_of_isSubquotient_glued F T hd ha hm A h𝔄 hp hE hr S R
    (by with_reducible exact hS) (by with_reducible exact hR) eo
    (by with_reducible exact hglue) hZ hZsq h𝔄Z

/-- Multiplicity one, given the data of the geometric lemma. -/
theorem multiplicity_eq_one_glued {d a m : ℕ} (hd : 0 < d) (ha : 0 < a)
    (hm : 0 < m)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible) (hp : IsPure T hd A 𝔄)
    {E : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hE : letI := T.topology; E.IsIrreducible) (hr : LeftReduced F T A E)
    (S : MinimalRepresentatives (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl) → BlockRefinement (BlockShape.ofPair a m ha hm rfl))
    (R : MinimalRepresentatives (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl) → BlockRefinement (BlockShape.ofPair a m ha hm rfl))
    (hS : ∀ w, IsIntersectionRefinement (F := F.Carrier) (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl) w.val (S w))
    (hR : ∀ w, IsIntersectionRefinement (F := F.Carrier) (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl) w.val⁻¹ (R w))
    {n : ℕ} (eo : Fin n ≃ MinimalRepresentatives (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl))
    (hglue : letI := T.topology;
      IsGluedFrom (jacquetInductionFunctor.{uF, max uF uV} T (BlockShape.ofPair a m ha hm rfl)
          (BlockShape.ofPair a m ha hm rfl))
        (fun i => geometricPieceFunctor T (BlockShape.ofPair a m ha hm rfl)
          (BlockShape.ofPair a m ha hm rfl) (eo i).val (S (eo i)) (R (eo i))
          (hS (eo i)).2.1 (hR (eo i)).2.1)) (M : ℕ)
    (hM : letI := T.topology; HasJordanHolderMultiplicity
      ((jacquetInductionFunctor.{uF, max uF uV} T (BlockShape.ofPair a m ha hm rfl)
          (BlockShape.ofPair a m ha hm rfl)).obj
        (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)))
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).obj M) :
    M = 1 := by
  let := T.topology
  have hEfl := SmoothRep.hasFiniteLength_of_isIrreducible hE
  have hXirr := isIrreducible_twoBlock F T ha hm h𝔄 hE
  have hmin1 : IsMinimalRepresentative (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl) 1 :=
    ⟨fun i => index_strictMono (BlockShape.ofPair a m ha hm rfl) i,
      fun j => index_strictMono (BlockShape.ofPair a m ha hm rfl) j⟩
  have hi₀ : (eo (eo.symm ⟨1, hmin1⟩)).val = 1 := by simp
  obtain ⟨e⟩ := nonempty_identityPieceEquiv.{uF, max uF uV} T (BlockShape.ofPair a m ha hm rfl)
      (eo (eo.symm ⟨1, hmin1⟩)).val hi₀ (S (eo (eo.symm ⟨1, hmin1⟩)))
      (R (eo (eo.symm ⟨1, hmin1⟩))) (hS (eo (eo.symm ⟨1, hmin1⟩))).2.1
      (hR (eo (eo.symm ⟨1, hmin1⟩))).2.1
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E))
  have hXX : HasJordanHolderMultiplicity
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).obj
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).obj 1 :=
    UnlinkedSocleProduct.hasJordanHolderMultiplicity_one hXirr (Representation.Equiv.refl _)
  have h₀ := (equivJordanHolderMultiplicityTransport ℂ
    ((BlockShape.ofPair a m ha hm rfl).Levi F.Carrier)
    (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).obj
    ((geometricPieceFunctor.{uF, max uF uV} T (BlockShape.ofPair a m ha hm rfl)
      (BlockShape.ofPair a m ha hm rfl) (eo (eo.symm ⟨1, hmin1⟩)).val
      (S (eo (eo.symm ⟨1, hmin1⟩))) (R (eo (eo.symm ⟨1, hmin1⟩)))
      (hS (eo (eo.symm ⟨1, hmin1⟩))).2.1 (hR (eo (eo.symm ⟨1, hmin1⟩))).2.1).obj
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)))
    (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).obj
    (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).obj e.symm
    (Representation.Equiv.refl _) 1).mp hXX
  refine multiplicity_eq_one_of_isGluedFrom hglue
    (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)) hM (eo.symm ⟨1, hmin1⟩) h₀ ?_
  intro i hi hsq
  have h1 : (eo i).val ≠ 1 := by
    intro h
    apply hi
    apply eo.injective
    apply Subtype.ext
    rw [h, hi₀]
  apply not_isSubquotient_geometricPiece_of_ne_one F T hd ha hm A h𝔄 hp hEfl hr (eo i) h1
    (S (eo i)) (R (eo i)) (hS (eo i)) (hR (eo i))
  exact (WeylBranchPieces.IsSubquotient.comp hsq _).trans
    (isSubquotient_firstBlock_twoBlock F T ha hm h𝔄 hE)

/-- **Multiplicity one.** `𝔄 ⊠ E` occurs exactly once in `r_(a,m)(𝔄 × E)`: any Jordan–Hölder
count of it equals `1`. -/
theorem multiplicity_eq_one_jacquetInduction {d a m : ℕ} (hd : 0 < d) (ha : 0 < a)
    (hm : 0 < m)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible) (hp : IsPure T hd A 𝔄)
    {E : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hE : letI := T.topology; E.IsIrreducible) (hr : LeftReduced F T A E) (M : ℕ)
    (hM : letI := T.topology; HasJordanHolderMultiplicity
      ((jacquetInductionFunctor.{uF, max uF uV} T (BlockShape.ofPair a m ha hm rfl)
          (BlockShape.ofPair a m ha hm rfl)).obj
        (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)))
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hm 𝔄 E)).obj M) :
    M = 1 := by
  let := T.topology
  obtain ⟨S, R, hS, hR, n, eo, hglue⟩ :=
    padicGeometricLemma.{uF, max uF uV} p F T (a + m) (by omega)
      (BlockShape.ofPair a m ha hm rfl) (BlockShape.ofPair a m ha hm rfl)
  exact multiplicity_eq_one_glued F T hd ha hm A h𝔄 hp hE hr S R
    (by with_reducible exact hS) (by with_reducible exact hR) eo
    (by with_reducible exact hglue) M hM

end Constituents

end Langlands.Classification.LeftCuspidalDerivative

import Langlands.Geometry.Analytic.StrictTestDomain.IteratedLaurentScalarDescentStatement
import Langlands.Geometry.Analytic.StrictTestDomain.ScalarCoverDescentTransport
import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentGluingProof
import Langlands.Geometry.Analytic.StrictTestDomain.RationalPresheaf

/-! # Scalar descent for finite iterated Laurent covers -/

noncomputable section

universe u v w

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

private theorem inter_relative_locus (d e : RationalData K P) :
    ((d.inter e).pullback d.baseMap).locus = (e.pullback d.baseMap).locus := by
  ext x
  rw [mem_locus_pullback, locus_inter]
  exact and_iff_right (d.baseMap_hasImageIn x)

/-- The actual intersection quotient is the inverse-image quotient of its
second factor over its first factor's actual algebra. -/
private def interRelativeEquiv (d e : RationalData K P) :
    BoundedAlgEquiv K (d.inter e).algebra (e.pullback d.baseMap).algebra :=
  (interLeft d e).relativeEquiv.trans
    (StandardRationalLaurentReduction.locusEquiv (inter_relative_locus d e))

private theorem interRelativeEquiv_base (d e : RationalData K P) :
    (interRelativeEquiv d e).toBoundedAlgHom.comp (d.inter e).baseMap =
      (e.pullback d.baseMap).baseMap.comp d.baseMap := by
  change (_ : BoundedAlgHom K _ _).comp
      (((d.inter e).comparison d.baseMap).comp (d.inter e).baseMap) = _
  rw [comparison_comp_baseMap, ← BoundedAlgHom.comp_assoc,
    StandardRationalLaurentReduction.locusMap_comp_baseMap]

private theorem interRelativeEquiv_left (d e : RationalData K P) :
    (interRelativeEquiv d e).toBoundedAlgHom.comp (interLeft d e).restriction =
      (e.pullback d.baseMap).baseMap := by
  apply d.hom_ext
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    interRelativeEquiv_base]

private theorem interRelativeEquiv_right (d e : RationalData K P) :
    (interRelativeEquiv d e).toBoundedAlgHom.comp (interRight d e).restriction =
      e.comparison d.baseMap := by
  apply e.hom_ext
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    interRelativeEquiv_base, comparison_comp_baseMap]

private theorem descent_inter_family {I : Type v} {J : Type w}
    (D : I → RationalData K P) (E : J → RationalData K P)
    (hD : ScalarCoverDescent D) (hE : UniversalScalarCoverDescent E) :
    ScalarCoverDescent (fun p : I × J => (D p.1).inter (E p.2)) := by
  intro s hs
  let r (i : I) (j : J) := interRelativeEquiv (D i) (E j)
  let t (i : I) (j : J) : ((E j).pullback (D i).baseMap).algebra :=
    r i j (s (i,j))
  have ht (i : I) :
      CompatibleScalarSections (fun j => (E j).pullback (D i).baseMap) (t i) := by
    intro j k
    exact compatible_sections_apply (s (i,j)) (s (i,k)) (hs (i,j) (i,k))
      ((interLeft ((E j).pullback (D i).baseMap)
        ((E k).pullback (D i).baseMap)).restriction.comp (r i j).toBoundedAlgHom)
      ((interRight ((E j).pullback (D i).baseMap)
        ((E k).pullback (D i).baseMap)).restriction.comp (r i k).toBoundedAlgHom)
      (by
        rw [BoundedAlgHom.comp_assoc, interRelativeEquiv_base,
          ← BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
          BoundedAlgHom.comp_assoc, interRelativeEquiv_base,
          ← BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap])
  have hex (i : I) := hE (D i).algebra (D i).baseMap (t i) (ht i)
  let a (i : I) : (D i).algebra := (hex i).choose
  have ha (i : I) (j : J) :
      ((E j).pullback (D i).baseMap).baseMap (a i) = t i j :=
    (hex i).choose_spec.1 j
  have hu (i : I) : ∀ b : (D i).algebra,
      (∀ j, ((E j).pullback (D i).baseMap).baseMap b = t i j) → b = a i :=
    (hex i).choose_spec.2
  have hac : CompatibleScalarSections D a := by
    intro i k
    apply (hE ((D i).inter (D k)).algebra ((D i).inter (D k)).baseMap).separated
    intro j
    let l := (E j).pullbackTriangleMap (D i).baseMap
      ((D i).inter (D k)).baseMap (interLeft (D i) (D k)).restriction
      (interLeft (D i) (D k)).restriction_comp_baseMap
    let q := (E j).pullbackTriangleMap (D k).baseMap
      ((D i).inter (D k)).baseMap (interRight (D i) (D k)).restriction
      (interRight (D i) (D k)).restriction_comp_baseMap
    have hl := congrArg l (ha i j)
    have hq := congrArg q (ha k j)
    change (l.comp ((E j).pullback (D i).baseMap).baseMap) (a i) = l (t i j) at hl
    change (q.comp ((E j).pullback (D k).baseMap).baseMap) (a k) = q (t k j) at hq
    rw [pullbackTriangleMap_comp_baseMap] at hl hq
    have hsame : l (t i j) = q (t k j) :=
      compatible_sections_apply (s (i,j)) (s (k,j)) (hs (i,j) (k,j))
        (l.comp (r i j).toBoundedAlgHom) (q.comp (r k j).toBoundedAlgHom)
        (by
          rw [BoundedAlgHom.comp_assoc, interRelativeEquiv_base,
            ← BoundedAlgHom.comp_assoc, pullbackTriangleMap_comp_baseMap,
            BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
            BoundedAlgHom.comp_assoc, interRelativeEquiv_base,
            ← BoundedAlgHom.comp_assoc, pullbackTriangleMap_comp_baseMap,
            BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap])
    exact hl.trans (hsame.trans hq.symm)
  obtain ⟨b, hb, hub⟩ := hD a hac
  refine ⟨b, ?_, ?_⟩
  · intro p
    apply (r p.1 p.2).toAlgEquiv.injective
    have hbase := congrArg (fun f => f b) (interRelativeEquiv_base (D p.1) (E p.2))
    change r p.1 p.2 (((D p.1).inter (E p.2)).baseMap b) =
      ((E p.2).pullback (D p.1).baseMap).baseMap ((D p.1).baseMap b) at hbase
    exact hbase.trans (by rw [hb p.1]; exact ha p.1 p.2)
  · intro c hc
    apply hub c
    intro i
    apply hu i
    intro j
    have hbase := congrArg (fun f => f c) (interRelativeEquiv_base (D i) (E j))
    exact hbase.symm.trans (congrArg (r i j) (hc (i,j)))

private theorem binary_choice_descent (f : P) :
    ScalarCoverDescent (fun b : Bool => laurentChoice f b) := by
  intro s hs
  obtain ⟨a, ha, hu⟩ := binaryLaurentGluing K P f (s false) (s true) (hs false true)
  refine ⟨a, ?_, fun b hb => hu b ⟨hb false, hb true⟩⟩
  intro b
  cases b
  · exact ha.1
  · exact ha.2

private def choicesSuccEquiv (m : ℕ) :
    (Fin (m+1) → Bool) ≃ Bool × (Fin m → Bool) where
  toFun ε := (ε 0, fun i => ε i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv ε := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by cases p; rfl

/-- Scalar descent of the actual finite Laurent leaves before base change. -/
theorem scalarCoverDescent_iteratedLaurent (m : ℕ) :
    ∀ (P : PresentedStrictAffinoidAlgebra K) (g : Fin m → P),
      ScalarCoverDescent (fun ε => iteratedLaurent g ε) := by
  induction m with
  | zero =>
      intro P g s _
      let ε : Fin 0 → Bool := Fin.elim0
      refine ⟨wholeEvaluation K P (s ε), ?_, ?_⟩
      · intro η
        have he : η = ε := Subsingleton.elim _ _
        subst η
        exact congrArg (fun f => f (s ε)) (wholeBaseMap_comp_evaluation K P)
      · intro b hb
        have h := congrArg (wholeEvaluation K P) (hb ε)
        exact (congrArg (fun f => f b) (wholeEvaluation_comp_baseMap K P)).symm.trans h
  | succ m ih =>
      intro P g
      let D (b : Bool) := laurentChoice (g 0) b
      let E (ε : Fin m → Bool) := iteratedLaurent (fun i => g i.succ) ε
      have hE : UniversalScalarCoverDescent E := by
        intro Q φ
        exact (ih Q (fun i => φ (g i.succ))).of_locus_eq
          (fun ε => (locus_iteratedLaurent_pullback (fun i => g i.succ) ε φ).symm)
      have h := descent_inter_family D E (binary_choice_descent (g 0)) hE
      exact h.of_reindex_locus_eq (fun ε => iteratedLaurent g ε) (choicesSuccEquiv m)
        (fun _ => rfl)

/-- Universal scalar descent for finite iterated unit-radius Laurent covers. -/
theorem iteratedLaurentScalarDescent : IteratedLaurentScalarDescentStatement.{u} := by
  intro K _ _ _ P m g Q φ
  exact (scalarCoverDescent_iteratedLaurent m Q (fun i => φ (g i))).of_locus_eq
    (fun ε => (locus_iteratedLaurent_pullback g ε φ).symm)

end Langlands.Analytic.StrictTestDomain

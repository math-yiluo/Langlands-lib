import Langlands.AlgebraicGeometry.PointTopology.AffineTopologyAxioms
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs
import Langlands.AlgebraicGeometry.PointTopology.AffinePolynomialPushouts
import Mathlib.Data.Fintype.Option
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Affine topology uniqueness from binary fibre products
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S]

omit [IsTopologicalRing S] in
theorem affineTopology_eq_of_algEquiv
    (T : AffinePointTopologyFamily R S)
    (hfun : AffineTopologyFunctorial R S T)
    (A B : CommAlgCat.{u} R) [Algebra.FiniteType R A] [Algebra.FiniteType R B]
    (e : A ≃ₐ[R] B)
    (hA : T A = evaluationAffineTopologyFamily R S A) :
    T B = evaluationAffineTopologyFamily R S B := by
  have hp : @IsHomeomorph (AlgPoint R B S) (AlgPoint R A S)
      (T B) (T A) (AlgPoint.precomp e.toAlgHom) := by
    let : TopologicalSpace (AlgPoint R A S) := T A
    let : TopologicalSpace (AlgPoint R B S) := T B
    apply isHomeomorph_iff_exists_inverse.mpr
    refine ⟨hfun A B (CommAlgCat.ofHom e.toAlgHom),
      AlgPoint.precomp e.symm.toAlgHom, ?_, ?_,
      hfun B A (CommAlgCat.ofHom e.symm.toAlgHom)⟩
    · intro p
      ext b
      simp
    · intro p
      ext a
      simp
  rw [hA] at hp
  have hTind : T B =
      TopologicalSpace.induced (AlgPoint.precomp (S := S) e.toAlgHom)
        (evaluationAffineTopologyFamily R S A) := by
    let : TopologicalSpace (AlgPoint R B S) := T B
    exact hp.isEmbedding.isInducing.eq_induced
  exact hTind.trans
    (AlgPoint.congr (S := S) e.symm).isEmbedding.isInducing.eq_induced.symm

theorem polynomialOptionTopology_eq_evaluation
    (T : AffinePointTopologyFamily R S)
    (hpush : AffineTopologyPushouts R S T)
    (hline : AffineTopologyLine R S T)
    (ι : Type u) [Finite ι]
    (hι : T (CommAlgCat.of R (MvPolynomial ι R)) =
      evaluationAffineTopologyFamily R S (CommAlgCat.of R (MvPolynomial ι R))) :
    T (CommAlgCat.of R (MvPolynomial (Option ι) R)) =
      evaluationAffineTopologyFamily R S
        (CommAlgCat.of R (MvPolynomial (Option ι) R)) := by
  have hiEval := (AlgPoint.polynomialPointHomeomorph (R := R) (S := S) ι).isHomeomorph
  have hEvalInd :
      evaluationAffineTopologyFamily R S
          (CommAlgCat.of R (MvPolynomial (Option ι) R)) =
        TopologicalSpace.induced
          (fun (p : AlgPoint R (MvPolynomial (Option ι) R) S) i =>
            p (MvPolynomial.X i)) inferInstance :=
    (AlgPoint.polynomialPointHomeomorph (R := R) (S := S)
      (Option ι)).isEmbedding.isInducing.eq_induced
  let : Subsingleton (AlgPoint R R S) := by
    change Subsingleton (R →ₐ[R] S)
    infer_instance
  let : TopologicalSpace (AlgPoint R (MvPolynomial Unit R) S) :=
    T (CommAlgCat.of R (MvPolynomial Unit R))
  let : TopologicalSpace (AlgPoint R (MvPolynomial ι R) S) :=
    T (CommAlgCat.of R (MvPolynomial ι R))
  let : TopologicalSpace (AlgPoint R (MvPolynomial (Option ι) R) S) :=
    T (CommAlgCat.of R (MvPolynomial (Option ι) R))
  have : Algebra.FiniteType R (polynomialOptionPushout R ι).pt := by
    change Algebra.FiniteType R (MvPolynomial (Option ι) R)
    infer_instance
  have hc := hpush
    (CommAlgCat.of R (MvPolynomial ι R))
    (CommAlgCat.of R (MvPolynomial Unit R)) (CommAlgCat.of R R)
    (CommAlgCat.ofHom (Algebra.ofId R (MvPolynomial ι R)))
    (CommAlgCat.ofHom (Algebra.ofId R (MvPolynomial Unit R)))
    (polynomialOptionPushout R ι) (polynomialOptionPushoutIsColimit R ι)
  have hv : IsHomeomorph
      (Subtype.val :
        {q : AlgPoint R (MvPolynomial ι R) S × AlgPoint R (MvPolynomial Unit R) S //
          AlgPoint.precomp (Algebra.ofId R (MvPolynomial ι R)) q.1 =
            AlgPoint.precomp (Algebra.ofId R (MvPolynomial Unit R)) q.2} →
          AlgPoint R (MvPolynomial ι R) S × AlgPoint R (MvPolynomial Unit R) S) := by
    apply isHomeomorph_iff_isEmbedding_surjective.mpr
    refine ⟨IsEmbedding.subtypeVal, ?_⟩
    intro q
    exact ⟨⟨q, Subsingleton.elim _ _⟩, rfl⟩
  have hp := @IsHomeomorph.comp
    (AlgPoint R (MvPolynomial (Option ι) R) S) _
    (AlgPoint R (MvPolynomial ι R) S × AlgPoint R (MvPolynomial Unit R) S)
    (T (CommAlgCat.of R (MvPolynomial (Option ι) R))) inferInstance inferInstance
    _ _ hv hc
  have hi : IsHomeomorph (fun p : AlgPoint R (MvPolynomial ι R) S =>
      fun i => p (MvPolynomial.X i)) := by
    change @IsHomeomorph (AlgPoint R (MvPolynomial ι R) S) (ι → S)
      (T (CommAlgCat.of R (MvPolynomial ι R))) inferInstance _
    rw [hι]
    exact hiEval
  have hl : IsHomeomorph (fun p : AlgPoint R (MvPolynomial Unit R) S =>
      p (MvPolynomial.X ())) := hline
  let e : ((ι → S) × S) ≃ₜ (Option ι → S) :=
    { toFun := fun q i => Option.elim i q.2 q.1
      invFun := fun f => (fun i => f (some i), f none)
      left_inv := fun q => rfl
      right_inv := fun f => by
        funext i
        cases i <;> rfl
      continuous_toFun := continuous_pi (fun i => by
        cases i with
        | none => exact continuous_snd
        | some i => exact (continuous_apply i).comp continuous_fst)
      continuous_invFun :=
        (continuous_pi (fun i => continuous_apply (some i))).prodMk
          (continuous_apply none) }
  have hprod := hi.prodMap hl
  have hpair := @IsHomeomorph.comp
    (AlgPoint R (MvPolynomial (Option ι) R) S)
    (AlgPoint R (MvPolynomial ι R) S × AlgPoint R (MvPolynomial Unit R) S)
    ((ι → S) × S)
    (T (CommAlgCat.of R (MvPolynomial (Option ι) R))) inferInstance inferInstance
    _ _ hprod hp
  have hcoords := @IsHomeomorph.comp
    (AlgPoint R (MvPolynomial (Option ι) R) S) ((ι → S) × S) (Option ι → S)
    (T (CommAlgCat.of R (MvPolynomial (Option ι) R))) inferInstance inferInstance
    _ _ e.isHomeomorph hpair
  have heq :
      (fun p : AlgPoint R (MvPolynomial (Option ι) R) S =>
        fun i => p (MvPolynomial.X i)) =
      e ∘ Prod.map
        (fun p : AlgPoint R (MvPolynomial ι R) S => fun i => p (MvPolynomial.X i))
        (fun p : AlgPoint R (MvPolynomial Unit R) S => p (MvPolynomial.X ())) ∘
        Subtype.val ∘ affinePushoutPointComparison R S (polynomialOptionPushout R ι) := by
    funext p i
    cases i with
    | none =>
        change p (MvPolynomial.X none) =
          p ((MvPolynomial.rename (fun _ : Unit => (none : Option ι)))
            (MvPolynomial.X ()))
        simp
    | some i =>
        change p (MvPolynomial.X (some i)) =
          p ((MvPolynomial.rename (Option.some : ι → Option ι)) (MvPolynomial.X i))
        simp
  have hpoly : IsHomeomorph
      (fun p : AlgPoint R (MvPolynomial (Option ι) R) S =>
        fun i => p (MvPolynomial.X i)) := by
    rw [heq]
    exact hcoords
  have hTind : T (CommAlgCat.of R (MvPolynomial (Option ι) R)) =
      TopologicalSpace.induced
        (fun (p : AlgPoint R (MvPolynomial (Option ι) R) S) i =>
          p (MvPolynomial.X i)) inferInstance :=
    hpoly.isEmbedding.isInducing.eq_induced
  exact hTind.trans hEvalInd.symm

theorem polynomialTopology_eq_evaluation_of_pushouts
    (T : AffinePointTopologyFamily R S)
    (hfun : AffineTopologyFunctorial R S T)
    (hpush : AffineTopologyPushouts R S T)
    (hline : AffineTopologyLine R S T)
    (ι : Type u) [Finite ι] :
    T (CommAlgCat.of R (MvPolynomial ι R)) =
      evaluationAffineTopologyFamily R S (CommAlgCat.of R (MvPolynomial ι R)) := by
  have h : ∀ (α : Type u) [Finite α],
      T (CommAlgCat.of R (MvPolynomial α R)) =
        evaluationAffineTopologyFamily R S (CommAlgCat.of R (MvPolynomial α R)) := by
    intro α hα
    refine (Finite.induction_empty_option
      (P := fun β => ∀ [Finite β],
        T (CommAlgCat.of R (MvPolynomial β R)) =
          evaluationAffineTopologyFamily R S (CommAlgCat.of R (MvPolynomial β R)))
      ?_ ?_ ?_ α)
    · intro β γ e ih hγ
      let : Finite γ := hγ
      let : Finite β := Finite.of_equiv γ e.symm
      exact affineTopology_eq_of_algEquiv R S T hfun
        (CommAlgCat.of R (MvPolynomial β R))
        (CommAlgCat.of R (MvPolynomial γ R))
        (MvPolynomial.renameEquiv R e) (ih)
    · intro _
      let : Subsingleton (AlgPoint R (MvPolynomial PEmpty R) S) :=
        ⟨fun p q => by
          apply MvPolynomial.algHom_ext
          intro i
          exact PEmpty.elim i⟩
      exact Subsingleton.elim _ _
    · intro β _ ih _
      exact polynomialOptionTopology_eq_evaluation R S T hpush hline β ih
  exact h ι

theorem affineTopology_eq_evaluation_of_pushouts
    (T : AffinePointTopologyFamily R S)
    (hfun : AffineTopologyFunctorial R S T)
    (hpush : AffineTopologyPushouts R S T)
    (hquot : AffineTopologyQuotientEmbeddings R S T)
    (hline : AffineTopologyLine R S T) :
    T = evaluationAffineTopologyFamily R S := by
  funext A hA
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
  let l : ULift.{u} (Fin n) → Fin n := ULift.down
  have hl : Function.Surjective l := fun i => ⟨ULift.up i, rfl⟩
  let g : MvPolynomial (ULift.{u} (Fin n)) R →ₐ[R] A :=
    f.comp (MvPolynomial.rename l)
  have hg : Function.Surjective g := hf.comp (MvPolynomial.rename_surjective l hl)
  have hT := hquot (CommAlgCat.of R (MvPolynomial (ULift.{u} (Fin n)) R)) A
    (CommAlgCat.ofHom g) hg
  rw [polynomialTopology_eq_evaluation_of_pushouts R S T hfun hpush hline
    (ULift.{u} (Fin n))] at hT
  have hTind : T A =
      TopologicalSpace.induced (AlgPoint.precomp (S := S) g) inferInstance := by
    let : TopologicalSpace (AlgPoint R A S) := T A
    exact hT.isInducing.eq_induced
  exact hTind.trans
    (AlgPoint.isEmbedding_precomp_of_surjective (S := S) g hg).isInducing.eq_induced.symm

end Langlands.AlgebraicGeometry.PointTopology

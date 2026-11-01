import Langlands.Representation.Classification.IrreducibleBinaryProductCommutationStatement
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof
import Langlands.Representation.Parabolic.InverseTransposeProductProof
import Langlands.Representation.Parabolic.NaturalInductionDualityProof
import Langlands.Representation.Tensor.SmoothDualInjectivityProof
import Langlands.Representation.Tensor.SmoothDualSurjectivityProof
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Induction.RankCast
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Category.Contragredient
import Langlands.LocalField.Normalization.Proof


/-! Generalization of Worker 1023's inverse-transpose commutation argument. -/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

section InverseTranspose

variable {N : ℕ}

/-- The pullback of a smooth representation of `GL_N(F)` along inverse
transpose, on the same carrier. -/
private abbrev itPullback
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier) :=
  letI := T.topology
  SmoothRep.of (A.representation.comp (GeneralLinear.inverseTranspose N F.Carrier).toMonoidHom)
    (isSmooth_comp _ (GeneralLinear.continuous_inverseTranspose N F.Carrier) A.isSmooth)

/-- Inverse-transpose pullback of an isomorphism, with the same linear map. -/
private def itPullbackIso
    {A A' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)}
    (f : letI := T.topology; A ≅ A') :
    letI := T.topology
    itPullback F T A ≅ itPullback F T A' := by
  letI := T.topology
  let E := SmoothRep.equivOfIso f
  refine SmoothRep.mkIso (Representation.Equiv.mk E.toLinearEquiv fun g => ?_)
  ext v
  exact Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap
    (GeneralLinear.inverseTranspose N F.Carrier g) v

/-- Inverse transpose is an involution, so pulling back twice returns the
original representation through the identity map. -/
private def itPullbackTwiceIso
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)) :
    letI := T.topology
    itPullback F T (itPullback F T A) ≅ A := by
  letI := T.topology
  refine SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun g => ?_)
  ext v
  change A.representation (GeneralLinear.inverseTranspose N F.Carrier
    (GeneralLinear.inverseTranspose N F.Carrier g)) v = A.representation g v
  rw [GeneralLinear.inverseTranspose_involutive]

/-- The published Gelfand–Kazhdan theorem under the selected topology `T.topology`
of `F`, for an arbitrary positive rank `N`: inverse-transpose pullback realizes
the smooth dual of an irreducible admissible representation. -/
private theorem gelfandKazhdanEquiv (hN : 0 < N) {V : Type uV} [AddCommGroup V]
    [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup N
    ∀ ρ : Representation ℂ (GeneralLinear N F.Carrier) V,
      IsAdmissible ρ → Representation.IsIrreducible ρ →
      Nonempty (Representation.Equiv
        (ρ.comp (GeneralLinear.inverseTranspose N F.Carrier).toMonoidHom)
        (smoothContragredient ρ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  let tc : TopologicalSpace F.Carrier := (letI := F.canonicalNormedField; inferInstance)
  have key : ∀ t : TopologicalSpace F.Carrier, tc = t →
      ∀ [IsTopologicalGroup (GeneralLinear (n + 1) F.Carrier)]
        (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V),
        IsAdmissible ρ → Representation.IsIrreducible ρ →
        Nonempty (Representation.Equiv
          (ρ.comp (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom)
          (smoothContragredient ρ)) := by
    intro t ht
    subst ht
    intro _ ρ hadm hirr
    obtain ⟨E, hE⟩ := gelfandKazhdanContragredient p inferInstance F n V ρ hadm hirr
    exact ⟨Representation.Equiv.mk E (fun g => LinearMap.ext (hE g))⟩
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1)
  exact key T.topology T.topology_eq_canonicalNormTopology.symm

/-- Gelfand–Kazhdan for bundled smooth representations: the inverse-transpose
pullback of an irreducible admissible representation is its smooth dual. -/
private theorem gelfandKazhdanIso (hN : 0 < N)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup N
    A.IsAdmissible → A.IsIrreducible →
      Nonempty (itPullback F T A ≅ A.contragredient) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup N
  intro hadm hirr
  obtain ⟨E⟩ := gelfandKazhdanEquiv F T hN A.representation hadm hirr
  exact ⟨SmoothRep.mkIso E⟩

end InverseTranspose

section Products

/-- The smooth dual of a normalized product of admissible blocks is the
normalized product, over the same parabolic, of the smooth duals of the blocks. -/
private theorem productSmoothDualEquiv {n : ℕ} (B : BlockShape n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hA : letI := T.topology; ∀ i, IsAdmissible (A i).representation) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
    Nonempty ((smoothContragredient
        (T.normalizedProductInduced B (fun i => (A i).representation))).Equiv
      (T.normalizedProductInduced B (fun i => smoothContragredient (A i).representation))) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
  letI := T.leviTopologicalGroup B
  let τ := fun i => (A i).representation
  let σ : Rep.{uV} ℂ (B.Levi F.Carrier) := Rep.of (B.blockTensor τ)
  have hσ : IsAdmissible σ.ρ := FiniteTensor.isAdmissible_external τ hA
  obtain ⟨EI, -⟩ := Parabolic.naturalNormalizedInductionDuality.{uF, uV}.1 p F T n B
  have hbij : Function.Bijective (FiniteTensor.smoothDualTensorMap τ) :=
    ⟨FiniteTensor.smoothDualTensorInjectivity.{0, uF, uV} (Fin B.length) _ _ τ,
      FiniteTensor.smoothDualTensorMap_surjective τ hA
      (fun i => GeneralLinear.compactOpen_cofinal F T (B.size i))⟩
  let e2 : (FiniteTensor.external (fun i => smoothContragredient (τ i))).Equiv
      (smoothContragredient (FiniteTensor.external τ)) :=
    Representation.Equiv.mk (LinearEquiv.ofBijective _ hbij)
      (FiniteTensor.smoothDualTensorIntertwiner τ).isIntertwining'
  exact ⟨(EI σ hσ).trans (T.normalizedParabolicInducedEquiv B e2.symm)⟩

/-- Inverse transpose reverses the blocks of a normalized product and pulls
back each block by its own inverse transpose. -/
private theorem itPullbackProductIso {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    Nonempty (itPullback F T ((T.normalizedProductInductionFunctor B).obj A) ≅
      (T.normalizedProductInductionFunctor B.reverse).obj (fun i => itPullback F T (A i.rev))) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  let σ := fun i => (A i).representation
  let τ := fun i : Fin B.reverse.length => (itPullback F T (A i.rev)).representation
  have E : Representation.Equiv ((T.normalizedProductInduced B σ).comp
        (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom)
      (T.normalizedProductInduced B.reverse τ) :=
    Classical.choice (Parabolic.normalizedProductInverseTranspose T n hn B (fun i => A i)
      σ (fun i => (A i).isSmooth))
  exact ⟨SmoothRep.mkIso (A := itPullback F T ((T.normalizedProductInductionFunctor B).obj A))
    (B := (T.normalizedProductInductionFunctor B.reverse).obj
      (fun i => itPullback F T (A i.rev))) E⟩

/-- Equal block shapes with heterogeneously equal block families give
isomorphic normalized products. -/
private theorem productFunctor_obj_congr {n : ℕ} {B C : BlockShape n} (h : B = C)
    (A : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (A' : letI := T.topology
      ∀ i : Fin C.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (hA : HEq A A') :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor B).obj A ≅
      (T.normalizedProductInductionFunctor C).obj A') := by
  letI := T.topology
  subst h
  obtain rfl := eq_of_heq hA
  exact ⟨Iso.refl _⟩

/-- Reversing a block shape twice restores its ordered sizes. -/
private theorem reverse_reverse {n : ℕ} (B : BlockShape n) : B.reverse.reverse = B := by
  cases B
  simp only [BlockShape.reverse, Fin.rev_rev]

end Products

/-- If a normalized product of irreducible blocks is irreducible, reversing
all of its blocks gives an actual isomorphic smooth object. -/
private theorem irreducibleProductReverse {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hA : letI := T.topology; ∀ i, (A i).IsIrreducible)
    (hX : letI := T.topology
      ((T.normalizedProductInductionFunctor B).obj A).IsIrreducible) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor B).obj A ≅
      (T.normalizedProductInductionFunctor B.reverse).obj (fun i => A i.rev)) := by
  letI := T.topology
  letI (r : ℕ) : IsTopologicalGroup (GeneralLinear r F.Carrier) :=
    T.generalLinearTopologicalGroup r
  let X := (T.normalizedProductInductionFunctor B).obj A
  let Y := (T.normalizedProductInductionFunctor B.reverse).obj (fun i => A i.rev)
  have hAa : ∀ i, (A i).IsAdmissible := fun i =>
    (CuspidalSupport.cuspidalEmbedding F T (B.size i) (A i) (hA i)).1
  have hXa : X.IsAdmissible := (CuspidalSupport.cuspidalEmbedding F T n X hX).1
  have e1 := (itPullbackProductIso F T hn B.reverse (fun i => A i.rev)).some
  have hfam : HEq
      (fun i : Fin B.reverse.reverse.length => itPullback F T (A i.rev.rev))
      (fun i : Fin B.length => itPullback F T (A i)) := by
    refine Function.hfunext rfl fun i i' hi => ?_
    obtain rfl := eq_of_heq hi
    rw [Fin.rev_rev]
  have e2 := (productFunctor_obj_congr F T (reverse_reverse B) _ _ hfam).some
  have e3 : (T.normalizedProductInductionFunctor B).obj (fun i => itPullback F T (A i)) ≅
      (T.normalizedProductInductionFunctor B).obj (fun i => (A i).contragredient) :=
    (T.normalizedProductInductionFunctor B).mapIso (Pi.isoMk fun i =>
      (gelfandKazhdanIso F T (B.positive i) (A i) (hAa i) (hA i)).some)
  have e4 : (T.normalizedProductInductionFunctor B).obj (fun i => (A i).contragredient) ≅
      X.contragredient :=
    (SmoothRep.mkIso (productSmoothDualEquiv F T B A hAa).some).symm
  have e5 : itPullback F T X ≅ X.contragredient :=
    (gelfandKazhdanIso F T hn X hXa hX).some
  have eθ : itPullback F T Y ≅ itPullback F T X := e1 ≪≫ e2 ≪≫ e3 ≪≫ e4 ≪≫ e5.symm
  exact ⟨(itPullbackTwiceIso F T X).symm ≪≫ itPullbackIso F T eθ.symm ≪≫
    itPullbackTwiceIso F T Y⟩

/-- Casting the total rank of an induced product casts its block shape. -/
private def rankCastProductIso {m n : ℕ} (h : m = n) (B : BlockShape m)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (Derivative.generalLinearRankCast T h).obj
        ((T.normalizedProductInductionFunctor B).obj A) ≅
      (T.normalizedProductInductionFunctor (B.rankCast h)).obj A := by
  subst h
  exact Iso.refl _

/-- The reversed binary shape is the binary shape in reversed order with its
literal total-rank cast. -/
private theorem reverse_binary {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (BlockShape.binary b a hb ha).rankCast (Nat.add_comm b a) =
      (BlockShape.binary a b ha hb).reverse := by
  change BlockShape.mk 2 (Fin.cases b (fun _ => a)) _ _ =
    BlockShape.mk 2 (fun i => Fin.cases (motive := fun _ : Fin 2 => ℕ) a (fun _ => b) i.rev) _ _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- An irreducible actual upper binary product commutes, including unequal
positive ranks and the literal reversed-sum rank cast. -/
theorem irreducibleBinaryProductCommutation :
    IrreducibleBinaryProductCommutation.{uF, uV} F T := by
  letI := T.topology
  intro a b ha hb α β hα hβ hX
  rw [T.binaryNormalizedProductFunctor_of_pos ha hb] at hX ⊢
  rw [T.binaryNormalizedProductFunctor_of_pos hb ha]
  let B := BlockShape.binary a b ha hb
  let C := BlockShape.binary b a hb ha
  let fab := (T.binaryPairFamilyFunctor ha hb).obj (α, β)
  let fba := (T.binaryPairFamilyFunctor hb ha).obj (β, α)
  have hfab : ∀ i, (fab i).IsIrreducible := by
    intro i
    fin_cases i
    · exact hα
    · exact hβ
  have e1 := (irreducibleProductReverse F T (by omega : 0 < a + b) B fab hfab hX).some
  have hfam : HEq (fun i : Fin B.reverse.length => fab i.rev)
      (fun i : Fin (C.rankCast (Nat.add_comm b a)).length => fba i) := by
    refine Function.hfunext rfl fun i i' hi => ?_
    obtain rfl := eq_of_heq hi
    fin_cases i <;> exact HEq.rfl
  have e2 := (productFunctor_obj_congr F T (reverse_binary ha hb).symm _ _ hfam).some
  have e3 := rankCastProductIso F T (Nat.add_comm b a) C fba
  exact ⟨e1 ≪≫ e2 ≪≫ e3.symm⟩

end Langlands.Classification

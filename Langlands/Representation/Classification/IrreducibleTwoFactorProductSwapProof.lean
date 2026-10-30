import Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapStatement
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof
import Langlands.Representation.Parabolic.InverseTransposeProductProof
import Langlands.Representation.Parabolic.NaturalInductionDualityProof
import Langlands.Representation.Tensor.SmoothDualInjectivityProof
import Langlands.Representation.Tensor.SmoothDualSurjectivityProof
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Category.Contragredient
import Langlands.LocalField.Normalization.Proof

/-!
# Swapping the factors of an irreducible equal-rank product

Write `X = α × β` and `Y = β × α` on `GL_{2k}(F)` and `θ(g) = ᵗg⁻¹`. Inverse
transpose reverses the blocks of a normalized product, so `Y ∘ θ` is the product
of `α ∘ θ` and `β ∘ θ` in this order. By Gelfand–Kazhdan each `α ∘ θ` is the
smooth dual of `α`, the product of the smooth duals is the smooth dual of `X`,
and the smooth dual of the irreducible representation `X` is `X ∘ θ`. Hence
`Y ∘ θ ≅ X ∘ θ`, and pulling back once more by the involution `θ` gives
`X ≅ Y`.
-/

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

/-- Reversing the equal-rank two-block shape gives the same shape. -/
private theorem twoBlocks_reverse {k : ℕ} (hk : 0 < k) :
    (Shahidi.twoBlocks k k hk hk).reverse = Shahidi.twoBlocks k k hk hk := by
  change BlockShape.mk 2 (fun i => ![k, k] i.rev) _ _ = BlockShape.mk 2 ![k, k] _ _
  congr 1
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i <;> rfl

end Products

/-- **Ze80 Theorem 1.9, irreducible equal-rank case.** If the normalized product
`α × β` of irreducible representations of `GL_k(F)` is irreducible, it is
isomorphic to `β × α`. -/
theorem irreducibleTwoFactorProductSwap : IrreducibleTwoFactorProductSwap.{uF, uV} F T := by
  letI := T.topology
  intro k hk α β hα hβ hX
  letI (r : ℕ) : IsTopologicalGroup (GeneralLinear r F.Carrier) :=
    T.generalLinearTopologicalGroup r
  have hn : 0 < k + k := by omega
  let B := Shahidi.twoBlocks k k hk hk
  let fab := twoBlockFactors hk hk α β
  let fba := twoBlockFactors hk hk β α
  let X := (T.normalizedProductInductionFunctor B).obj fab
  let Y := (T.normalizedProductInductionFunctor B).obj fba
  have hαa : α.IsAdmissible := (CuspidalSupport.cuspidalEmbedding F T k α hα).1
  have hβa : β.IsAdmissible := (CuspidalSupport.cuspidalEmbedding F T k β hβ).1
  have hXa : X.IsAdmissible := (CuspidalSupport.cuspidalEmbedding F T (k + k) X hX).1
  have hfab : ∀ i, IsAdmissible (fab i).representation := by
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
    · exact hαa
    · exact hβa
  -- `Y ∘ θ` is the reversed product of the pulled-back blocks.
  have e1 := (itPullbackProductIso F T hn B fba).some
  -- The reversed shape is the same shape, and the reversed family is `(α ∘ θ, β ∘ θ)`.
  have hfam : HEq (fun i : Fin B.reverse.length => itPullback F T (fba i.rev))
      (fun i : Fin B.length => itPullback F T (fab i)) := by
    refine Function.hfunext rfl fun i i' hi => ?_
    obtain rfl := eq_of_heq hi
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
    · exact HEq.rfl
    · exact HEq.rfl
  have e2 := (productFunctor_obj_congr F T (twoBlocks_reverse hk) _ _ hfam).some
  -- Gelfand–Kazhdan on each block.
  have e3 : (T.normalizedProductInductionFunctor B).obj (fun i => itPullback F T (fab i)) ≅
      (T.normalizedProductInductionFunctor B).obj (fun i => (fab i).contragredient) := by
    refine (T.normalizedProductInductionFunctor B).mapIso (Pi.isoMk fun i => ?_)
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
    · exact (gelfandKazhdanIso F T hk α hαa hα).some
    · exact (gelfandKazhdanIso F T hk β hβa hβ).some
  -- The product of the smooth duals is the smooth dual of `X`.
  have e4 : (T.normalizedProductInductionFunctor B).obj (fun i => (fab i).contragredient) ≅
      X.contragredient :=
    (SmoothRep.mkIso (productSmoothDualEquiv F T B fab hfab).some).symm
  -- Gelfand–Kazhdan on the irreducible product `X`.
  have e5 : itPullback F T X ≅ X.contragredient := (gelfandKazhdanIso F T hn X hXa hX).some
  have eθ : itPullback F T Y ≅ itPullback F T X := e1 ≪≫ e2 ≪≫ e3 ≪≫ e4 ≪≫ e5.symm
  exact ⟨(itPullbackTwiceIso F T X).symm ≪≫ itPullbackIso F T eθ.symm ≪≫
    itPullbackTwiceIso F T Y⟩

end Langlands.Classification

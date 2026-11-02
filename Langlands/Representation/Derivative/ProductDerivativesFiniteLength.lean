import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
import Langlands.Representation.Parabolic.HeadTailProductInduction
import Langlands.Representation.Classification.SupercuspidalDerivativesProof
import Langlands.Representation.Classification.NormalizedProductFiniteLengthProof
import Langlands.Representation.Smooth.Admissibility.FiniteLengthProof
import Langlands.Representation.Filtration.RepresentationLength
import Mathlib.Data.ENat.BigOperators

/-! Finite length of all derivatives of finite normalized products of irreducible
supercuspidal representations. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped MonoidAlgebra TensorProduct

namespace Langlands.Derivative.ProductDerivativesFiniteLength

universe uF uK uG uH uV uW uC vC uι

section Generic

variable {k : Type uK} [Field k] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {W : Type uW} [AddCommGroup W] [Module k W]

/-- Finite group-algebra length is invariant under actual equivalences. -/
theorem isFiniteLength_of_equiv {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) (h : IsFiniteLength k[G] ρ.asModule) :
    IsFiniteLength k[G] σ.asModule :=
  (repAsModuleEquiv e).isFiniteLength h

/-- A finite-dimensional representation has finite group-algebra length. -/
theorem isFiniteLength_of_finiteDimensional [FiniteDimensional k V]
    (ρ : Representation k G V) : IsFiniteLength k[G] ρ.asModule :=
  isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

/-- A representation of a finite group of finite group-algebra length is
finite-dimensional. -/
theorem finiteDimensional_of_isFiniteLength [Finite G] (ρ : Representation k G V)
    (h : IsFiniteLength k[G] ρ.asModule) : FiniteDimensional k V := by
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).1
  have : Module.Finite k ρ.asModule := Module.Finite.trans k[G] ρ.asModule
  exact Module.Finite.equiv ρ.asModuleEquiv

/-- Composition with a surjective group homomorphism preserves finite length. -/
theorem isFiniteLength_comp {H : Type uH} [Group H] (ρ : Representation k G V)
    (f : H →* G) (hf : Function.Surjective f) (h : IsFiniteLength k[G] ρ.asModule) :
    IsFiniteLength k[H] (Representation.asModule (ρ.comp f)) := by
  let e : Subrepresentation ρ ≃o Subrepresentation (ρ.comp f) :=
    { toFun := fun S => ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (f h) hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g _ hv => by
        obtain ⟨h, rfl⟩ := hf g
        exact S.apply_mem_toSubmodule h hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have hl : Module.length k[G] ρ.asModule =
      Module.length k[H] (Representation.asModule (ρ.comp f)) := by
    apply WithBot.coe_injective
    rw [Module.coe_length, Module.coe_length]
    exact Order.krullDim_eq_of_orderIso
      (Subrepresentation.subrepresentationSubmoduleOrderIso.symm.trans
        (e.trans Subrepresentation.subrepresentationSubmoduleOrderIso))
  rw [← Module.length_ne_top_iff] at h ⊢
  rwa [← hl]

/-- A finite-length representation tensored on the left with a finite-dimensional
space, the group acting on the second factor, has finite length. -/
theorem isFiniteLength_secondFactor {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (hσ : IsFiniteLength ℂ[G] σ.asModule) :
    IsFiniteLength ℂ[G] (BinaryTensor.secondFactor V σ).asModule := by
  let b := Module.finBasis ℂ V
  let f : Fin (Module.finrank ℂ V) →
      σ.IntertwiningMap (BinaryTensor.secondFactor V σ) := fun i =>
    { toLinearMap := TensorProduct.mk ℂ V W (b i)
      isIntertwining' := fun g => by
        ext w
        rfl }
  let Φ : (Fin (Module.finrank ℂ V) → σ.asModule) →ₗ[ℂ[G]]
      (BinaryTensor.secondFactor V σ).asModule :=
    ∑ i, (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (f i)).comp
      (LinearMap.proj i)
  have hΦ : ∀ w : Fin (Module.finrank ℂ V) → σ.asModule,
      (Φ w : V ⊗[ℂ] W) = ∑ i, b i ⊗ₜ[ℂ] σ.asModuleEquiv (w i) := by
    intro w
    rw [LinearMap.sum_apply]
    rfl
  have hsurj : Function.Surjective Φ := by
    intro x
    change V ⊗[ℂ] W at x
    induction x using TensorProduct.inductionOn with
    | tmul v w =>
      refine ⟨fun i => σ.asModuleEquiv.symm (b.repr v i • w), ?_⟩
      rw [hΦ]
      simp only [LinearEquiv.apply_symm_apply]
      conv_rhs => rw [← b.sum_repr v]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (TensorProduct.smul_tmul _ _ _).symm
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      exact ⟨u + v, by rw [map_add, hu, hv]; rfl⟩
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hσ
  have hpi : IsFiniteLength ℂ[G] (Fin (Module.finrank ℂ V) → σ.asModule) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  exact hpi.of_surjective hsurj

/-- A finite-length representation tensored on the right with a finite-dimensional
space, the group acting on the first factor, has finite length. -/
theorem isFiniteLength_firstFactor {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (hρ : IsFiniteLength ℂ[G] ρ.asModule) :
    IsFiniteLength ℂ[G] (BinaryTensor.firstFactor ρ W).asModule :=
  isFiniteLength_of_equiv
    (Representation.Equiv.mk (TensorProduct.comm ℂ W V) fun g =>
      TensorProduct.ext' fun w v => by simp)
    (isFiniteLength_secondFactor ρ hρ)

/-- Finite group-algebra length of every graded value of a finite actual functor
filtration implies finite length of the filtered value. -/
theorem isFiniteLength_of_filtration {K : Type uK} [Field K] {G : Type uG} [Group G]
    {C : Type uC} [Category.{vC} C] {M : C ⥤ Rep.{uW} K G} {n : ℕ}
    (s : RepFunctorFiltration M n) (X : C)
    (hs : ∀ i, IsFiniteLength (MonoidAlgebra K G) ((s.graded i).obj X).ρ.asModule) :
    IsFiniteLength (MonoidAlgebra K G) (M.obj X).ρ.asModule := by
  apply Module.length_ne_top_iff.mp
  change repLength (M.obj X).ρ ≠ ⊤
  rw [repLength_eq_sum_of_filtration (ObjectRepFiltration.ofSubrepresentations
    (fun i => (s.step i).obj X) (s.monotone X) (s.zero X) (s.top X))]
  apply ENat.sum_ne_top.mpr
  intro j _
  exact Module.length_ne_top_iff.mpr (hs j)

end Generic

section Smooth

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Finite length transfers along isomorphisms of smooth representations. -/
theorem hasFiniteLength_of_iso {G : Type uG} [Group G] [TopologicalSpace G]
    {A B : SmoothRep.{0, uG, uV} ℂ G} (e : A ≅ B) (h : A.HasFiniteLength) :
    B.HasFiniteLength :=
  isFiniteLength_of_equiv (SmoothRep.equivOfIso e) h

/-- The rank transport preserves finite length. -/
theorem hasFiniteLength_rankCast {a b : ℕ} (h : a = b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (hA : letI := T.topology; A.HasFiniteLength) :
    letI := T.topology
    ((generalLinearRankCast T h).obj A).HasFiniteLength := by
  subst h
  exact hA

/-- If all derivatives of `A` have finite length, so do all derivatives of any
isomorphic representation. -/
theorem derivatives_of_iso {N : ℕ}
    {A B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)}
    (e : letI := T.topology; A ≅ B)
    (hA : letI := T.topology
      ∀ k (hk : k ≤ N), ((generalLinearDerivative T ψ N k hk).obj A).HasFiniteLength) :
    letI := T.topology
    ∀ k (hk : k ≤ N), ((generalLinearDerivative T ψ N k hk).obj B).HasFiniteLength := by
  let := T.topology
  exact fun k hk => hasFiniteLength_of_iso ((generalLinearDerivative T ψ N k hk).mapIso e)
    (hA k hk)

/-- If all derivatives of `A` have finite length, so do all derivatives of its
transport along an equality of ranks. -/
theorem derivatives_transport {a b : ℕ} (h : a = b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (hA : letI := T.topology
      ∀ k (hk : k ≤ a), ((generalLinearDerivative T ψ a k hk).obj A).HasFiniteLength) :
    letI := T.topology
    ∀ k (hk : k ≤ b), ((generalLinearDerivative T ψ b k hk).obj (h ▸ A)).HasFiniteLength := by
  subst h
  exact hA

/-- The binary normalized product of two finite-length representations has finite
length, in all ranks. -/
theorem binaryProduct_hasFiniteLength {a b : ℕ}
    (X : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (h₁ : letI := T.topology; X.1.HasFiniteLength)
    (h₂ : letI := T.topology; X.2.HasFiniteLength) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor.{uF, max uF uV} a b).obj X).HasFiniteLength := by
  let := T.topology
  by_cases ha : a = 0
  · have : Subsingleton (GeneralLinear a F.Carrier) :=
      GeneralLinear.subsingleton_of_rank_eq_zero ha
    have : Finite (GeneralLinear a F.Carrier) := Finite.of_subsingleton
    have : FiniteDimensional ℂ X.1 := finiteDimensional_of_isFiniteLength X.1.representation h₁
    refine isFiniteLength_of_equiv (T.binaryLeftZeroTensorEquiv ha X).symm ?_
    exact isFiniteLength_comp _ _ (GeneralLinear.reindex _).surjective
      (isFiniteLength_secondFactor _ h₂)
  by_cases hb : b = 0
  · have : Subsingleton (GeneralLinear b F.Carrier) :=
      GeneralLinear.subsingleton_of_rank_eq_zero hb
    have : Finite (GeneralLinear b F.Carrier) := Finite.of_subsingleton
    have : FiniteDimensional ℂ X.2 := finiteDimensional_of_isFiniteLength X.2.representation h₂
    refine isFiniteLength_of_equiv (T.binaryRightZeroTensorEquiv hb X).symm ?_
    exact isFiniteLength_comp _ _ (GeneralLinear.reindex _).surjective
      (isFiniteLength_firstFactor _ h₁)
  have ha' : 0 < a := Nat.pos_of_ne_zero ha
  have hb' : 0 < b := Nat.pos_of_ne_zero hb
  refine hasFiniteLength_of_iso ((T.binaryNormalizedProductPositiveIso ha' hb').app X).symm ?_
  refine Classification.admissibleFiniteLengthProductPreservation.{uF, max uF uV} F T (a + b)
    (by omega) (GeneralLinear.BlockShape.binary a b ha' hb')
    ((T.binaryPairFamilyFunctor ha' hb').obj X) fun i => ?_
  fin_cases i
  · exact ⟨(finiteLengthAdmissibility.{uF, max uF uV} F T).1 _ X.1 h₁, h₁⟩
  · exact ⟨(finiteLengthAdmissibility.{uF, max uF uV} F T).1 _ X.2 h₂, h₂⟩

/-- BZ77 4.14(c) step: if all derivatives of `A` and of `B` have finite length, so do
all derivatives of their binary normalized product. -/
theorem binaryProduct_derivatives {a b : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hA : letI := T.topology
      ∀ k (hk : k ≤ a), ((generalLinearDerivative T ψ a k hk).obj A).HasFiniteLength)
    (hB : letI := T.topology
      ∀ k (hk : k ≤ b), ((generalLinearDerivative T ψ b k hk).obj B).HasFiniteLength) :
    letI := T.topology
    ∀ d (hd : d ≤ a + b), ((generalLinearDerivative T ψ (a + b) d hd).obj
      ((T.binaryNormalizedProductFunctor.{uF, max uF uV} a b).obj (A, B))).HasFiniteLength := by
  let := T.topology
  intro d hd
  obtain ⟨e, s, hs⟩ :=
    (generalLinearDerivativeLeibnizFiltration.{uF, max uF uV} F T).filtration T ψ a b d hd
  have key := isFiniteLength_of_filtration s (A, B) fun i => by
    obtain ⟨ei⟩ := hs i
    refine isFiniteLength_of_equiv (Representation.equivOfIso (ei.app (A, B))).symm ?_
    have hP := hasFiniteLength_rankCast T (leibnizIndices_rank (e.symm i).property) _
      (binaryProduct_hasFiniteLength T
        ((generalLinearDerivative T ψ a (e.symm i).val.1
            (leibnizIndices_left_le (e.symm i).property)).obj A,
          (generalLinearDerivative T ψ b (e.symm i).val.2
            (leibnizIndices_right_le (e.symm i).property)).obj B)
        (hA _ _) (hB _ _))
    exact hP
  exact key

/-- All derivatives of the normalized product attached to a binary block shape,
transported to rank `n = a + b`, have finite length. -/
theorem binaryStep {a b n : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = n)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hA : letI := T.topology
      ∀ k (hk : k ≤ a), ((generalLinearDerivative T ψ a k hk).obj A).HasFiniteLength)
    (hB : letI := T.topology
      ∀ k (hk : k ≤ b), ((generalLinearDerivative T ψ b k hk).obj B).HasFiniteLength) :
    letI := T.topology
    ∀ k (hk : k ≤ n), ((generalLinearDerivative T ψ n k hk).obj
      ((T.normalizedProductInductionFunctor
        ((GeneralLinear.BlockShape.binary a b ha hb).rankCast h)).obj
        (Fin.cases A (fun _ => B)))).HasFiniteLength := by
  subst n
  let := T.topology
  have hf : (T.binaryPairFamilyFunctor ha hb).obj (A, B) = Fin.cases A (fun _ => B) := by
    funext i
    fin_cases i <;> rfl
  let eF := (T.normalizedProductInductionFunctor
    (GeneralLinear.BlockShape.binary a b ha hb)).mapIso (eqToIso hf.symm)
  let E := ((T.binaryNormalizedProductPositiveIso ha hb).app (A, B)).symm
  exact derivatives_of_iso T ψ (eF ≪≫ E).symm (binaryProduct_derivatives T ψ A B hA hB)

private theorem transport_symm_cancel {α : Sort*} (P : α → Sort*)
    {a b : α} (h : a = b) (x : P a) : h.symm ▸ (h ▸ x) = x := by
  subst b
  rfl

private theorem singleFamily_eq {n : ℕ} (B : GeneralLinear.BlockShape n)
    (h : B.length = 1)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (fun j => ((B.singleBlock_size h j).symm ▸
      ((B.singleBlock_size h (B.singleBlockIndex h)) ▸ σ (B.singleBlockIndex h)) :
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier))) = σ := by
  let := T.topology
  funext j
  have hj := B.eq_singleBlockIndex h j
  subst j
  exact transport_symm_cancel
    (fun r => SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) _ _

/-- The one-block case: the product is the transported single factor. -/
theorem singletonStep {n : ℕ} (B : GeneralLinear.BlockShape n) (h : B.length = 1)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i k (hk : k ≤ B.size i),
      ((generalLinearDerivative T ψ (B.size i) k hk).obj (σ i)).HasFiniteLength) :
    letI := T.topology
    ∀ k (hk : k ≤ n), ((generalLinearDerivative T ψ n k hk).obj
      ((T.normalizedProductInductionFunctor B).obj σ)).HasFiniteLength := by
  let := T.topology
  let i := B.singleBlockIndex h
  let A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
    (B.singleBlock_size h i) ▸ σ i
  let τ := fun j => ((B.singleBlock_size h j).symm ▸ A :
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size j) F.Carrier))
  let E := Parabolic.equivTrans (T.normalizedProductInductionObjEquiv B τ)
    (T.singleBlockTransportedProductEquiv B h A)
  let eF := (T.normalizedProductInductionFunctor B).mapIso
    (eqToIso (singleFamily_eq T B h σ).symm)
  exact derivatives_of_iso T ψ (eF ≪≫ SmoothRep.mkIso E).symm
    (derivatives_transport T ψ (B.singleBlock_size h i) (σ i) (hσ i))

set_option maxHeartbeats 800000 in
/-- Induction on the number of blocks: all derivatives of a finite normalized
product have finite length when all derivatives of every factor do. -/
theorem product_derivatives (l : ℕ) :
    ∀ {n : ℕ}, 0 < n → ∀ (B : GeneralLinear.BlockShape n), B.length = l →
    ∀ (σ : letI := T.topology;
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (letI := T.topology; ∀ i k (hk : k ≤ B.size i),
      ((generalLinearDerivative T ψ (B.size i) k hk).obj (σ i)).HasFiniteLength) →
    letI := T.topology
    ∀ k (hk : k ≤ n), ((generalLinearDerivative T ψ n k hk).obj
      ((T.normalizedProductInductionFunctor B).obj σ)).HasFiniteLength := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    intro n hn B hB σ hσ
    let := T.topology
    rcases l with _ | l
    · have hempty : IsEmpty (Fin B.length) :=
        ⟨fun i => by have := i.isLt; omega⟩
      have hn0 : n = 0 := by simpa using B.sum_eq.symm
      omega
    rcases l with _ | m
    · exact singletonStep T ψ B hB σ hσ
    · have h : B.length = m + 2 := hB
      have hTail := ih (m + 1) (by omega) (B.tailRank_pos h)
        (B.tailShape h) rfl (fun j => σ (B.tailIndex h j))
        (fun j => hσ (B.tailIndex h j))
      let A : SmoothRep.{0, uF, max uF uV} ℂ
          (GeneralLinear (B.headRank h) F.Carrier) :=
        SmoothRep.universeLift.{uF} (σ (B.headIndex h))
      let P : SmoothRep.{0, uF, max uF uV} ℂ
          (GeneralLinear (B.tailRank h) F.Carrier) :=
        (T.normalizedProductInductionFunctor (B.tailShape h)).obj
          (fun j => σ (B.tailIndex h j))
      have hHead : ∀ k (hk : k ≤ B.headRank h),
          ((generalLinearDerivative T ψ (B.headRank h) k hk).obj A).HasFiniteLength :=
        derivatives_of_iso T ψ
          (SmoothRep.mkIso (SmoothRep.universeLiftEquiv.{uF} (σ (B.headIndex h))))
          (hσ (B.headIndex h))
      have hf : T.headTailProductFactors B h σ = Fin.cases A (fun _ => P) := by
        funext i
        fin_cases i <;> rfl
      let E := T.headTailProductInductionIso B h σ ≪≫
        (T.normalizedProductInductionFunctor (B.headTailShape h)).mapIso
          (eqToIso hf)
      exact derivatives_of_iso T ψ E.symm
        (binaryStep T ψ (a := B.headRank h) (b := B.tailRank h) (n := n)
          (B.headRank_pos h) (B.tailRank_pos h) (B.headRank_add_tailRank h) A P hHead hTail)

/-- BZ77 4.4: every derivative of an irreducible supercuspidal representation has
finite length. -/
theorem supercuspidal_derivatives {m : ℕ} (hm : 0 < m)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier))
    (hA : letI := T.topology;
      A.IsIrreducible ∧ GeneralLinear.IsSupercuspidal A.representation) :
    letI := T.topology
    ∀ k (hk : k ≤ m), ((generalLinearDerivative T ψ m k hk).obj A).HasFiniteLength := by
  let := T.topology
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨hmid, htop⟩ := Classification.supercuspidalDerivatives F T ψ m A hA.1 hA.2
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · have : IsSimpleModule ℂ[GeneralLinear (m + 1) F.Carrier] A.representation.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).mp hA.1
    have hfl : A.HasFiniteLength :=
      isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
    exact hfl
  rcases Nat.lt_or_ge k (m + 1) with hlt | hge
  · have : Subsingleton
        ((generalLinearDerivative T ψ (m + 1) k hk).obj A).representation.asModule :=
      hmid k hk hpos hlt
    exact IsFiniteLength.of_subsingleton
  · obtain rfl : k = m + 1 := le_antisymm hk hge
    have : FiniteDimensional ℂ ((generalLinearDerivative T ψ (m + 1) (m + 1) hk).obj A) :=
      Module.finite_of_finrank_pos (by rw [htop]; exact Nat.one_pos)
    exact isFiniteLength_of_finiteDimensional _

end Smooth

end Langlands.Derivative.ProductDerivativesFiniteLength

namespace Langlands.Derivative

universe uF uV

/-- All derivatives of a finite normalized product of irreducible supercuspidal
representations of positive total rank have finite length. -/
theorem productDerivativesFiniteLength {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (B : GeneralLinear.BlockShape n) (hn : 0 < n)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i, (σ i).IsIrreducible ∧
      GeneralLinear.IsSupercuspidal (σ i).representation)
    (k : ℕ) (hk : k ≤ n) :
    letI := T.topology
    ((generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj
      ((T.normalizedProductInductionFunctor B).obj σ)).HasFiniteLength :=
  ProductDerivativesFiniteLength.product_derivatives T ψ B.length hn B rfl σ
    (fun i => ProductDerivativesFiniteLength.supercuspidal_derivatives T ψ (B.positive i)
      (σ i) (hσ i)) k hk

end Langlands.Derivative

import Langlands.Representation.Classification.LeftCuspidalDerivative.Basic
import Langlands.Representation.Classification.SegmentSocleDerivativesProof
import Langlands.Representation.Tensor.FiniteEquivalences
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Frobenius reciprocity for binary products and tensor contractions

Algebraic contraction lemmas for tensor products with a trivially acted factor and for
two-factor external tensor products, and first adjointness for the binary normalized
product in the form used for left reducedness.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Classification.LeftCuspidalDerivative

universe uF uV uG uX uA uM

section Algebra

variable {G : Type uG} [Group G] {X : Type uX} {A : Type uA} {M : Type uM}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup A] [Module ℂ A] [AddCommGroup M] [Module ℂ M]

/-- Contraction of a trivially acted second tensor factor against a functional. -/
def rightContraction (ρ : Representation ℂ G A) (τ : Representation ℂ G M)
    (hτ : ∀ g, τ g = 1) (φ : Module.Dual ℂ M) :
    (Representation.tprod ρ τ).IntertwiningMap ρ where
  toLinearMap := (TensorProduct.rid ℂ A).toLinearMap ∘ₗ φ.lTensor A
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro a m
    simp [Representation.tprod_apply, hτ g]

theorem rightContraction_apply (ρ : Representation ℂ G A) (τ : Representation ℂ G M)
    (hτ : ∀ g, τ g = 1) (φ : Module.Dual ℂ M) (w : A ⊗[ℂ] M) :
    rightContraction ρ τ hτ φ w = TensorProduct.rid ℂ A (φ.lTensor A w) := rfl

/-- A nonzero tensor survives contraction against some functional on the right factor. -/
theorem exists_dual_rid_lTensor_ne_zero {w : A ⊗[ℂ] M} (hw : w ≠ 0) :
    ∃ φ : Module.Dual ℂ M, TensorProduct.rid ℂ A (φ.lTensor A w) ≠ 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ M
  let e := TensorProduct.equivFinsuppOfBasisRight (R := ℂ) (M := A) b
  have hew : e w ≠ 0 := fun h => hw (e.injective (h.trans (map_zero e).symm))
  obtain ⟨i, hi⟩ : ∃ i, e w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hew (Finsupp.ext h)
  refine ⟨b.coord i, ?_⟩
  have key : ∀ u : A ⊗[ℂ] M, TensorProduct.rid ℂ A ((b.coord i).lTensor A u) = e u i := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul a m =>
      simp [e]
    | add x y hx hy => simp only [map_add, hx, hy, Finsupp.add_apply]
  rw [key]
  exact hi

/-- A nonzero intertwiner into `ρ ⊗ τ`, with `τ` trivially acted, gives a nonzero
intertwiner into `ρ`. -/
theorem exists_ne_zero_of_tprod_trivial (π : Representation ℂ G X) (ρ : Representation ℂ G A)
    (τ : Representation ℂ G M) (hτ : ∀ g, τ g = 1)
    (f : π.IntertwiningMap (Representation.tprod ρ τ)) (hf : f ≠ 0) :
    ∃ g : π.IntertwiningMap ρ, g ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Representation.IntertwiningMap.ext (LinearMap.ext h))
  obtain ⟨φ, hφ⟩ := exists_dual_rid_lTensor_ne_zero hx
  refine ⟨(rightContraction ρ τ hτ φ).comp f, fun h0 => hφ ?_⟩
  have := congrArg (fun g : π.IntertwiningMap ρ => g x) h0
  exact this

/-- A nonzero intertwiner between irreducible representations is an equivalence. -/
theorem nonempty_equiv_of_ne_zero {π : Representation ℂ G X} {ρ : Representation ℂ G A}
    [π.IsIrreducible] [ρ.IsIrreducible] (g : π.IntertwiningMap ρ) (hg : g ≠ 0) :
    Nonempty (π.Equiv ρ) := by
  rcases Representation.IsIrreducible.bijective_or_eq_zero g with h | h
  · exact ⟨Representation.IntertwiningMap.ofBijective g h⟩
  · exact absurd h hg

end Algebra

section External

variable {H : Fin 2 → Type uG} [∀ i, Group (H i)]
  {V : Fin 2 → Type uX} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : Fin 2 → Type uA} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Contraction of the second factor of a two-factor external tensor against a functional;
an intertwiner for the first factor group. -/
def firstSlotContraction (τ : ∀ i, Representation ℂ (H i) (W i))
    (φ : Module.Dual ℂ (PiTensorProduct ℂ (fun j : Fin 1 => W j.succ))) :
    Representation.IntertwiningMap ((FiniteTensor.external τ).comp (MonoidHom.mulSingle H 0))
      (τ 0) where
  toLinearMap := (TensorProduct.rid ℂ (W 0)).toLinearMap ∘ₗ φ.lTensor (W 0) ∘ₗ
    (FiniteTensor.headTailLinearEquiv (r := 1) ℂ W).toLinearMap
  isIntertwining' h := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro u
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, MonoidHom.comp_apply,
      FiniteTensor.external_tprod, LinearEquiv.coe_coe,
      FiniteTensor.headTailLinearEquiv_tprod, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul, map_smul]
    congr 2
    congr 1
    funext j
    rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero j), map_one,
      Module.End.one_apply]

/-- A nonzero intertwiner between two-factor external tensors whose second source factor is
nonzero gives a nonzero intertwiner between the first factors. -/
theorem exists_firstFactor_ne_zero (ρ : ∀ i, Representation ℂ (H i) (V i))
    (τ : ∀ i, Representation ℂ (H i) (W i))
    (f : (FiniteTensor.external ρ).IntertwiningMap (FiniteTensor.external τ)) (hf : f ≠ 0) :
    ∃ g : (ρ 0).IntertwiningMap (τ 0), g ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : ∀ i, V i, f (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    apply Representation.IntertwiningMap.ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, Representation.IntertwiningMap.coe_toLinearMap,
      Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply]
    exact h v
  let L : V 0 →ₗ[ℂ] PiTensorProduct ℂ V := (PiTensorProduct.tprod ℂ).toLinearMap v 0
  have hL : ∀ (h : H 0) (x : V 0),
      L (ρ 0 h x) = FiniteTensor.external ρ (MonoidHom.mulSingle H 0 h) (L x) := by
    intro h x
    simp only [L, MultilinearMap.toLinearMap_apply, FiniteTensor.external_tprod]
    congr 1
    funext i
    by_cases hi : i = 0
    · subst hi
      simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi, MonoidHom.mulSingle_apply,
        Pi.mulSingle_eq_of_ne hi, map_one, Module.End.one_apply]
  let F : Representation.IntertwiningMap (ρ 0)
      ((FiniteTensor.external τ).comp (MonoidHom.mulSingle H 0)) :=
    { toLinearMap := f.toLinearMap ∘ₗ L
      isIntertwining' := by
        intro h
        ext x
        simp only [LinearMap.comp_apply, Representation.IntertwiningMap.coe_toLinearMap,
          MonoidHom.comp_apply, hL]
        exact Representation.IntertwiningMap.isIntertwining _ _ f _ _ }
  have hF : F (v 0) ≠ 0 := by
    change f (L (v 0)) ≠ 0
    simpa [L] using hv
  obtain ⟨φ, hφ⟩ := exists_dual_rid_lTensor_ne_zero
    (w := FiniteTensor.headTailLinearEquiv (r := 1) ℂ W (F (v 0)))
    (fun h0 => hF ((FiniteTensor.headTailLinearEquiv (r := 1) ℂ W).injective
      (h0.trans (map_zero _).symm)))
  refine ⟨(firstSlotContraction τ φ).comp F, fun h0 => hφ ?_⟩
  exact congrArg (fun g : (ρ 0).IntertwiningMap (τ 0) => g (v 0)) h0

end External

section Binary

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- An intertwiner into `ρ ∘ φ`, where `φ` is pointwise the identity, is an intertwiner
into `ρ`. -/
def intertwiningOfCompEq {G : Type uG} [Group G] {X : Type uX} {A : Type uA}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup A] [Module ℂ A]
    {π : Representation ℂ G X} {ρ : Representation ℂ G A} (φ : G →* G) (hφ : ∀ g, φ g = g)
    (f : π.IntertwiningMap (ρ.comp φ)) : π.IntertwiningMap ρ where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    have := f.isIntertwining' g
    simpa [hφ g] using this

/-- Frobenius reciprocity for the binary product in positive ranks: an embedding of a
nonzero `Z` into `A × σ` (after the rank transport `d + k = m`) gives a nonzero
intertwiner from the Jacquet module of `Z` along `(d, k)` to `A ⊗ σ`. -/
theorem exists_jacquet_ne_zero_of_isSubrepresentation {d k m : ℕ} (hd : 0 < d) (hk : 0 < k)
    (h : d + k = m) :
    letI := T.topology
    ∀ (Z : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d F.Carrier))
      (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier)),
      Nontrivial Z →
      SmoothRep.IsSubrepresentation Z
        (T.castRank h ((T.binaryNormalizedProductFunctor d k).obj (A, σ))) →
      ∃ g : (T.normalizedJacquet (BlockShape.ofPair d k hd hk h) Z.representation).IntertwiningMap
          ((BlockShape.ofPair d k hd hk h).blockTensor
            (fun i => (twoBlockFactors hd hk A σ i).representation)),
        g ≠ 0 := by
  subst h
  let _ := T.topology
  intro Z A σ hZ ⟨f, hf⟩
  obtain ⟨e⟩ := SegmentSocleDerivativesProof.nonempty_ofPairProductIso T hd hk A σ
  let B := BlockShape.ofPair d k hd hk rfl
  let ι := f ≫ e.hom
  have hι : Function.Injective (SmoothRep.hom ι) := by
    intro x y hxy
    exact hf (Derivative.LevelCalculus.iso_hom_injective e hxy)
  refine ⟨Parabolic.FirstAdjointness.equiv T B Z.isSmooth (SmoothRep.hom ι), fun h0 => ?_⟩
  have h1 : SmoothRep.hom ι = 0 :=
    (LinearEquiv.map_eq_zero_iff (Parabolic.FirstAdjointness.equiv T B Z.isSmooth)).mp h0
  obtain ⟨x, hx⟩ := exists_ne (0 : Z)
  apply hx
  apply hι
  rw [h1, map_zero]
  rfl

/-- Frobenius reciprocity for the binary product with a rank-zero second factor: an
embedding of a nonzero `Z` into `A × σ`, `σ` on `GL_0`, gives a nonzero intertwiner
`Z → A` after the rank transport. -/
theorem exists_ne_zero_of_isSubrepresentation_rankZero {d m : ℕ} (h : d + 0 = m) :
    letI := T.topology
    ∀ (Z : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d F.Carrier))
      (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier)),
      Nontrivial Z →
      SmoothRep.IsSubrepresentation Z
        (T.castRank h ((T.binaryNormalizedProductFunctor d 0).obj (A, σ))) →
      ∃ g : Z.representation.IntertwiningMap (T.castRank h A).representation, g ≠ 0 := by
  subst h
  let _ := T.topology
  intro Z A σ hZ ⟨f, hf⟩
  let E := T.binaryRightZeroTensorEquiv (a := d) (b := 0) rfl (A, σ)
  let f1 := E.toIntertwiningMap.comp (SmoothRep.hom f)
  have hf1 : f1 ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : Z)
    apply hx
    apply hf
    have := congrArg (fun g : Z.representation.IntertwiningMap _ => g x) h0
    rw [map_zero]
    simp [f1] at this
    exact this
  let φ : GeneralLinear (d + 0) F.Carrier →* GeneralLinear d F.Carrier :=
    (GeneralLinear.reindex (R := F.Carrier) (finCongr (by omega : d + 0 = d))).toMonoidHom
  obtain ⟨g1, hg1⟩ := exists_ne_zero_of_tprod_trivial Z.representation
    (A.representation.comp φ) ((Representation.trivial ℂ _ σ).comp φ) (fun _ => rfl) f1 hf1
  refine ⟨intertwiningOfCompEq (MonoidHom.id _) (fun _ => rfl) g1, ?_⟩
  intro h0
  apply hg1
  ext x
  have := congrArg (fun g : Z.representation.IntertwiningMap _ => g x) h0
  exact this

end Binary

end Langlands.Classification.LeftCuspidalDerivative

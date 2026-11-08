import Langlands.Representation.Classification.InverseTransposeHelpers
import Langlands.Representation.Unitary.ConjugateSpace
import Langlands.Representation.Classification.TadicUnitaryStatement
import Langlands.Representation.Classification.BernsteinUnitaryStatement
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof
import Langlands.Representation.Parabolic.InverseTransposeProductProof
import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.Aubert.General.NormalizedInductionHermitianDuality
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof

/-!
# Speh representations are Hermitian

Tadic 1986, Proposition 5.6(iii), for the Speh representations `u(δ,k)`: every actual
Speh representation `S` of a discrete-series datum admits a nonzero invariant
sesquilinear form. The positive form of `δ` and the Gelfand–Kazhdan theorem give a
conjugate-linear automorphism of `δ` twisted by inverse transpose `θ`; blockwise on the
centered product and with the published inverse-transpose reversal of block products it
makes `S̄ ∘ θ` an irreducible quotient of the centered product, hence isomorphic to `S`.
The Gelfand–Kazhdan theorem for `S` then produces the form.
-/

noncomputable section

set_option linter.style.haveILetI false

open scoped ComplexConjugate

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

section InverseTranspose

variable {N : ℕ}

/-- An irreducible admissible unitarizable representation carries a
conjugate-linear automorphism `J` with `J (ρ (θ g) v) = ρ g (J v)`,
`θ` the inverse transpose. -/
theorem exists_inverseTransposeConj (hN : 0 < N) {V : Type uV} [AddCommGroup V]
    [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup N
    ∀ ρ : Representation ℂ (GeneralLinear N F.Carrier) V,
      IsAdmissible ρ → Representation.IsIrreducible ρ → IsUnitarizable ρ →
      ∃ J : V ≃ₗ⋆[ℂ] V, ∀ g v,
        J (ρ (GeneralLinear.inverseTranspose N F.Carrier g) v) = ρ g (J v) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup N
  intro ρ hadm hirr hu
  obtain ⟨b⟩ := hu
  obtain ⟨E⟩ := hermitianGelfandKazhdanEquiv F T hN ρ hadm hirr
  let H := b.smoothDualEquiv (GeneralLinear.compactOpen_cofinal F T N) hadm
  refine ⟨H.trans E.symm.toLinearEquiv, fun g v => ?_⟩
  have h1 : H (ρ (GeneralLinear.inverseTranspose N F.Carrier g) v) =
      smoothContragredient ρ (GeneralLinear.inverseTranspose N F.Carrier g) (H v) :=
    b.toSmoothDual_apply_action hadm.1 _ v
  change E.symm.toIntertwiningMap (H (ρ (GeneralLinear.inverseTranspose N F.Carrier g) v)) =
    ρ g (E.symm.toIntertwiningMap (H v))
  rw [h1, Representation.IntertwiningMap.isIntertwining]
  change ρ (GeneralLinear.inverseTranspose N F.Carrier
    (GeneralLinear.inverseTranspose N F.Carrier g)) _ = _
  rw [GeneralLinear.inverseTranspose_involutive]

end InverseTranspose

section Blocks

variable {r : ℕ}

/-- A conjugate-linear map `K` with `K (δ g v) = δ (θ g) (K v)` intertwines
`ν^s δ` with the inverse-transpose pullback of `ν^t δ`, `t = -s`: the twisting
scalars are real. -/
theorem segmentFactor_conj_intertwine
    (δ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    ∀ (K : δ ≃ₗ⋆[ℂ] δ), (∀ g v, K (δ.representation g v) =
      δ.representation (GeneralLinear.inverseTranspose r F.Carrier g) (K v)) →
    ∀ (s t : ℝ), t = -s → ∀ (g : GeneralLinear r F.Carrier) (v : δ),
    K ((T.segmentFactor δ s).representation g v) =
      (hermitianItPullback F T (T.segmentFactor δ t)).representation g (K v) := by
  letI := T.topology
  intro K hK s t hst g v
  change K ((realPowerCharacter (T.determinantNorm r) s g : ℂ) • δ.representation g v) =
    (realPowerCharacter (T.determinantNorm r) t
        (GeneralLinear.inverseTranspose r F.Carrier g) : ℂ) •
      δ.representation (GeneralLinear.inverseTranspose r F.Carrier g) (K v)
  rw [map_smulₛₗ, hK]
  congr 1
  have h := congrArg (fun χ : GeneralLinear r F.Carrier →* ℂˣ => (χ g : ℂ))
    (Parabolic.determinantPowerCharacter_inverseTranspose T r t)
  simp only [MonoidHom.comp_apply] at h
  change (realPowerCharacter (T.determinantNorm r) t
      (GeneralLinear.inverseTranspose r F.Carrier g) : ℂ) =
    (realPowerCharacter (T.determinantNorm r) (-t) g : ℂ) at h
  rw [h, hst, neg_neg, coe_realPowerCharacter, starRingEnd_apply]
  exact Complex.conj_ofReal _

/-- On the uniform shape, the blockwise conjugate-linear intertwiners give a
conjugate-linear equivalence from `ν^(a_0) δ × ⋯ × ν^(a_(k-1)) δ` onto the
product of the inverse-transpose pullbacks of the reversed blocks, commuting
with the two actions. -/
theorem exists_productConj (hr : 0 < r) (k : ℕ)
    (δ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (a : Fin k → ℝ) (ha : ∀ i, a i.rev = -a i) :
    letI := T.topology
    ∀ (K : δ ≃ₗ⋆[ℂ] δ), (∀ g v, K (δ.representation g v) =
      δ.representation (GeneralLinear.inverseTranspose r F.Carrier g) (K v)) →
    ∃ N : ((T.normalizedProductInductionFunctor (BlockShape.uniform k r hr)).obj
          (fun i => T.segmentFactor δ (a i))) ≃ₗ⋆[ℂ]
        ((T.normalizedProductInductionFunctor (BlockShape.uniform k r hr)).obj
          (fun i => hermitianItPullback F T (T.segmentFactor δ (a i.rev)))),
      ∀ g f, N (((T.normalizedProductInductionFunctor (BlockShape.uniform k r hr)).obj
          (fun i => T.segmentFactor δ (a i))).representation g f) =
        ((T.normalizedProductInductionFunctor (BlockShape.uniform k r hr)).obj
          (fun i => hermitianItPullback F T (T.segmentFactor δ (a i.rev)))).representation g
          (N f) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k * r)
  have : IsModuleTopology (Padic p) F.Carrier := T.moduleTopology
  have : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  intro K hK
  let B := BlockShape.uniform k r hr
  let σ₁ : ∀ i : Fin B.length, Representation ℂ (GeneralLinear (B.size i) F.Carrier) δ :=
    fun i => (T.segmentFactor δ (a i)).representation
  let σ₂ : ∀ i : Fin B.length, Representation ℂ (GeneralLinear (B.size i) F.Carrier) δ :=
    fun i => (hermitianItPullback F T (T.segmentFactor δ (a i.rev))).representation
  let Tt : PiTensorProduct ℂ (fun _ : Fin B.length => δ) ≃ₗ⋆[ℂ]
      PiTensorProduct ℂ (fun _ : Fin B.length => δ) := tensorConjEquiv (fun _ => K)
  have hlevi : ∀ (m : B.Levi F.Carrier) x,
      Tt (B.blockTensor σ₁ m x) = B.blockTensor σ₂ m (Tt x) := fun m x =>
    tensorConjEquiv_external σ₁ σ₂ (fun _ => K) m
      (fun i v => segmentFactor_conj_intertwine F T δ K hK (a i) (a i.rev) (ha i) (m i) v) x
  have hT : ∀ (q : B.parabolic F.Carrier) x,
      Tt (B.inducingRepresentation (T.leviHalfCharacter B) (B.blockTensor σ₁) q x) =
        B.inducingRepresentation (T.leviHalfCharacter B) (B.blockTensor σ₂) q (Tt x) := by
    intro q x
    change Tt (((T.leviHalfCharacter B).toMonoidHom (B.leviProjection F.Carrier q) : ℂ) •
        B.blockTensor σ₁ (B.leviProjection F.Carrier q) x) =
      ((T.leviHalfCharacter B).toMonoidHom (B.leviProjection F.Carrier q) : ℂ) •
        B.blockTensor σ₂ (B.leviProjection F.Carrier q) (Tt x)
    rw [map_smulₛₗ, hlevi]
    congr 1
    rw [PadicField.TopologicalData.leviHalfCharacter_toMonoidHom,
      PadicField.TopologicalData.leviHalfModulus_apply, starRingEnd_apply]
    exact Complex.conj_ofReal _
  exact ⟨Induction.smoothFunctionsConjEquiv (B.parabolic F.Carrier) Tt hT, fun g f => rfl⟩

/-- Reversing the uniform shape gives the uniform shape. -/
theorem uniform_reverse (k r : ℕ) (hr : 0 < r) :
    (BlockShape.uniform k r hr).reverse = BlockShape.uniform k r hr := rfl

/-- The reversed product over the uniform shape is the product over the uniform shape. -/
theorem uniformReverseProductIso (hr : 0 < r) (k : ℕ)
    (X : letI := T.topology; Fin k → SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor (BlockShape.uniform k r hr).reverse).obj
        (fun i => X i) ≅
      (T.normalizedProductInductionFunctor (BlockShape.uniform k r hr)).obj (fun i => X i)) :=
  hermitianProductFunctor_obj_congr F T (uniform_reverse k r hr) _ _ HEq.rfl

end Blocks

/-- The centered exponents are antisymmetric under reversal. -/
theorem SpehDatum.exponent_rev (d : SpehDatum.{uF, uV} F T) (i : Fin d.length) :
    d.exponent i.rev = -d.exponent i := by
  unfold SpehDatum.exponent
  rw [Fin.val_rev]
  have hi : (i : ℕ) + 1 ≤ d.length := i.isLt
  rw [Nat.cast_sub hi]
  push_cast
  ring

/-- The pairing of a translated smooth functional. -/
theorem smoothDualPairing_contragredient {G : Type uF} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) (ℓ : SmoothDual ρ) (w : V) :
    smoothDualPairing ρ (smoothContragredient ρ g ℓ) (ρ g w) = smoothDualPairing ρ ℓ w := by
  change (ℓ : Module.Dual ℂ V) (ρ g⁻¹ (ρ g w)) = (ℓ : Module.Dual ℂ V) w
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

section ConjugateTwist

variable {N : ℕ}

/-- The conjugate of the inverse-transpose pullback, `S̄ ∘ θ`, on the conjugate space. -/
abbrev conjTwist
    (S : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier) :=
  letI := T.topology
  SmoothRep.of ((ConjSpace.rep S.representation).comp
      (GeneralLinear.inverseTranspose N F.Carrier).toMonoidHom)
    (isSmooth_comp _ (GeneralLinear.continuous_inverseTranspose N F.Carrier)
      (fun v => S.isSmooth v))

/-- A surjective conjugate-linear map `Q : C → S` with `Q (C g f) = S (θ g) (Q f)` makes
the irreducible `S̄ ∘ θ` an irreducible quotient of `C`. -/
theorem isIrreducibleQuotient_conjTwist
    (C S : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)) :
    letI := T.topology
    ∀ (Q : C →ₗ⋆[ℂ] S), (∀ g f, Q (C.representation g f) =
        S.representation (GeneralLinear.inverseTranspose N F.Carrier g) (Q f)) →
      Function.Surjective Q → Representation.IsIrreducible S.representation →
        IsIrreducibleQuotient C.representation (conjTwist F T S).representation := by
  letI := T.topology
  intro Q hQ hQs hSirr
  change IsIrreducibleQuotient C.representation ((ConjSpace.rep S.representation).comp
    (GeneralLinear.inverseTranspose N F.Carrier).toMonoidHom)
  refine ⟨(isIrreducible_conjComp_iff S.representation _
    (GeneralLinear.inverseTranspose N F.Carrier).surjective).mpr hSirr, ?_⟩
  let Q'' : C.representation.IntertwiningMap ((ConjSpace.rep S.representation).comp
      (GeneralLinear.inverseTranspose N F.Carrier).toMonoidHom) :=
    { toLinearMap := ConjSpace.ofConjLinear Q
      isIntertwining' := fun g => by
        ext f
        change ConjSpace.equiv _ (Q (C.representation g f)) =
          ConjSpace.equiv _ (S.representation (GeneralLinear.inverseTranspose N F.Carrier g)
            ((ConjSpace.equiv _).symm (ConjSpace.equiv _ (Q f))))
        rw [hQ, LinearEquiv.symm_apply_apply] }
  refine ⟨Q'', fun y => ?_⟩
  obtain ⟨x, hx⟩ := hQs ((ConjSpace.equiv _).symm y)
  refine ⟨x, ?_⟩
  change ConjSpace.equiv _ (Q x) = y
  rw [hx, LinearEquiv.apply_symm_apply]

/-- If `S̄ ∘ θ ≅ S` for an irreducible admissible `S`, then `S` admits a nonzero invariant
sesquilinear form. -/
theorem hasNonzeroInvariantSesquilinearForm_of_conjTwist (hN : 0 < N)
    (S : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup N
    IsAdmissible S.representation → Representation.IsIrreducible S.representation →
      Nonempty (conjTwist F T S ≅ S) →
        HasNonzeroInvariantSesquilinearForm S.representation := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup N
  intro hadm hirr ⟨e⟩
  let θ := GeneralLinear.inverseTranspose N F.Carrier
  let ψ := SmoothRep.equivOfIso e
  -- `P = ψ ∘ (identity to the conjugate space)`: conjugate linear, `P (S (θ g) v) = S g (P v)`
  let P : S ≃ₗ⋆[ℂ] S := (ConjSpace.equiv _).trans ψ.toLinearEquiv
  have hP : ∀ g v, P (S.representation (θ g) v) = S.representation g (P v) := fun g v =>
    Representation.IntertwiningMap.isIntertwining _ _ ψ.toIntertwiningMap g
      (ConjSpace.equiv _ v)
  have hPs : ∀ g w, P.symm (S.representation g w) = S.representation (θ g) (P.symm w) := by
    intro g w
    apply P.injective
    rw [LinearEquiv.apply_symm_apply, hP, LinearEquiv.apply_symm_apply]
  obtain ⟨E⟩ := hermitianGelfandKazhdanEquiv F T hN S.representation hadm hirr
  let Φ : S ≃ₗ⋆[ℂ] SmoothDual S.representation := P.symm.trans E.toLinearEquiv
  have hΦ : ∀ g v, Φ (S.representation g v) =
      smoothContragredient S.representation g (Φ v) := by
    intro g v
    change E.toIntertwiningMap (P.symm (S.representation g v)) = _
    rw [hPs]
    exact Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g (P.symm v)
  refine ⟨(smoothDualPairing S.representation).comp Φ.toLinearMap, ?_, fun g v w => ?_⟩
  · obtain ⟨v, hv⟩ : ∃ v : S, v ≠ 0 := by
      by_contra hcon
      simp only [ne_eq, not_exists, not_not] at hcon
      have hbt : (⊥ : Subrepresentation S.representation) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        ext x
        change x ∈ (⊥ : Submodule ℂ S) ↔ x ∈ (⊤ : Submodule ℂ S)
        rw [hcon x]
        simp
      exact bot_ne_top hbt
    intro h0
    have hΦv : Φ v ≠ 0 := fun h => hv (Φ.injective (h.trans (map_zero Φ).symm))
    apply hΦv
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    exact LinearMap.congr_fun (LinearMap.congr_fun h0 v) w
  · change smoothDualPairing S.representation (Φ (S.representation g v)) (S.representation g w) =
      smoothDualPairing S.representation (Φ v) w
    rw [hΦ]
    exact smoothDualPairing_contragredient S.representation g (Φ v) w

end ConjugateTwist

/-- **Speh representations are Hermitian.** For a discrete-series datum `d`, every
actual Speh representation `S` admits a nonzero invariant sesquilinear form. -/
theorem SpehDatum.hasNonzeroInvariantSesquilinearForm_of_isSpeh
    (d : SpehDatum.{uF, uV} F T)
    (S : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
    (hS : d.IsSpeh S) :
    letI := T.topology
    HasNonzeroInvariantSesquilinearForm S.representation := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup d.degree
  obtain ⟨hd, ⟨hSirr, q, hq⟩, huniq⟩ := hS
  obtain ⟨hδirr, hδu, hδsq⟩ := hd
  have hr := d.rank_pos
  have hn : 0 < d.degree := Nat.mul_pos d.length_pos d.rank_pos
  let δ := d.delta
  let θ := GeneralLinear.inverseTranspose d.degree F.Carrier
  -- the conjugate-linear automorphism of `δ`
  obtain ⟨J, hJ⟩ := exists_inverseTransposeConj F T hr δ.representation hδsq.isAdmissible
    hδirr hδu
  have hK : ∀ g v, J.symm (δ.representation g v) =
      δ.representation (GeneralLinear.inverseTranspose d.rank F.Carrier g) (J.symm v) := by
    intro g v
    apply J.injective
    rw [LinearEquiv.apply_symm_apply, hJ, LinearEquiv.apply_symm_apply]
  -- the product-level conjugate-linear map and the inverse-transpose identification
  obtain ⟨N, hN⟩ := exists_productConj F T hr d.length δ d.exponent (d.exponent_rev F T)
    J.symm hK
  obtain ⟨e1⟩ := hermitianItPullbackProductIso F T hn (BlockShape.uniform d.length d.rank hr)
    (fun i => T.segmentFactor δ (d.exponent i))
  obtain ⟨e2⟩ := uniformReverseProductIso F T hr d.length
    (fun i => hermitianItPullback F T (T.segmentFactor δ (d.exponent i.rev)))
  let L := e1 ≪≫ e2
  let C' := (T.normalizedProductInductionFunctor (BlockShape.uniform d.length d.rank hr)).obj
    (fun i => T.segmentFactor δ (d.exponent i))
  let q' : C'.representation.IntertwiningMap S.representation := q
  let Q : C' →ₗ⋆[ℂ] S :=
    q'.toLinearMap.comp ((SmoothRep.hom L.inv).toLinearMap.comp N.toLinearMap)
  have hQ : ∀ g f, Q (C'.representation g f) = S.representation (θ g) (Q f) := by
    intro g f
    have h1 := congrArg (fun x => q' (SmoothRep.hom L.inv x)) (hN g f)
    have h2 := Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom L.inv) g (N f)
    have h3 := Representation.IntertwiningMap.isIntertwining _ _ q' (θ g)
      (SmoothRep.hom L.inv (N f))
    exact h1.trans ((congrArg q' h2).trans h3)
  have hQs : Function.Surjective Q := by
    intro y
    obtain ⟨x, hx⟩ := hq y
    refine ⟨N.symm (SmoothRep.hom L.hom x), ?_⟩
    have h1 : N (N.symm (SmoothRep.hom L.hom x)) = SmoothRep.hom L.hom x :=
      N.apply_symm_apply _
    have h2 : SmoothRep.hom L.inv (SmoothRep.hom L.hom x) = x := SmoothRep.hom_inv_hom_apply L x
    change q' (SmoothRep.hom L.inv (N (N.symm (SmoothRep.hom L.hom x)))) = y
    exact ((congrArg (fun z => q' (SmoothRep.hom L.inv z)) h1).trans (congrArg q' h2)).trans hx
  have hquot := isIrreducibleQuotient_conjTwist F T C' S Q hQ hQs hSirr
  obtain ⟨e⟩ := huniq (conjTwist F T S) hquot
  have hSadm : S.IsAdmissible := (CuspidalSupport.cuspidalEmbedding F T d.degree S hSirr).1
  exact hasNonzeroInvariantSesquilinearForm_of_conjTwist F T hn S hSadm hSirr ⟨e⟩

end Langlands.Classification

import Langlands.Representation.Classification.A6iiSilberger
import Langlands.Representation.Exponents.WeylBranchPieceLiftingProof
import Langlands.Representation.Exponents.WeylBranchPiecesAssembly
import Langlands.Representation.CuspidalSupport.BlockPermutationTensor
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Classification.FineTwistRegularityProof

/-!
# A reordered cuspidal tensor in the opposite Jacquet module of a product

Let every factor `π_i` of a normalized product be a quotient of the induction of
a tensor of supercuspidal representations along a refinement of its block. Any
reordering of all the supercuspidal blocks that keeps the order of the blocks
coming from each single factor gives an actual subquotient of the opposite
Jacquet module of the product. This is the whole-Levi piece of the geometric
lemma (`glGeometricPieceLifting`) applied to the embedding of the cuspidal
tensor given by second adjointness inside the product Levi.
-/

noncomputable section

namespace Langlands.Classification.A6ii

open CategoryTheory GeneralLinear Geometric RelativeJacquetMultiplicity WeylBranchPieces

universe uF uV uW

section Subquotient

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- The source of an injective intertwiner is a subquotient of its target. -/
theorem isSubquotient_of_injective {A : Representation ℂ G V} {Y : Representation ℂ G W}
    (j : Y.IntertwiningMap A) (hj : Function.Injective j) : IsSubquotient A Y := by
  let U : Subrepresentation A :=
    { toSubmodule := LinearMap.range j.toLinearMap
      apply_mem_toSubmodule := by
        rintro g _ ⟨w, rfl⟩
        exact ⟨Y g w, Representation.IntertwiningMap.isIntertwining _ _ j g w⟩ }
  let e := LinearEquiv.ofInjective j.toLinearMap hj
  refine ⟨U, LinearMap.intertwiningMap_of_isIntertwiningMap _ _ e.symm.toLinearMap ?_,
    e.symm.surjective⟩
  intro g u
  obtain ⟨w, rfl⟩ := e.surjective u
  change e.symm (U.toRepresentation g (e w)) = Y g (e.symm (e w))
  rw [e.symm_apply_apply, e.symm_apply_eq]
  apply Subtype.ext
  change A g (j w) = j (Y g w)
  exact (Representation.IntertwiningMap.isIntertwining _ _ j g w).symm

end Subquotient

section Piece

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The fine twist with zero exponents is the pullback along the flattened Levi. -/
theorem fineTwist_zero_zero {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)) :
    fineTwist T B S ω 0 0 =
      Rep.of (ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom) := by
  unfold fineTwist
  congr 2
  have : (fun k => -(0 : Fin (B.flatten S).length → ℝ) k +
      (0 : Fin B.length → ℝ) ((B.flattenBlockEquiv S).symm k).1) = 0 := by
    funext k
    simp
  rw [this, T.leviRealPowerTwist_zero]

/-- A reordering of the supercuspidal blocks of the factors, minimal for the outer
shape, gives an actual subquotient of the opposite Jacquet module of the
normalized product. -/
theorem geometricPiece {n : ℕ} (hn : 0 < n) (B : BlockShape n) (S : BlockRefinement B)
    (Y : letI := T.topology
      ∀ q : (i : Fin B.length) × Fin (S i).length,
        SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (S q.1).size q.2))
    (π : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hπi : letI := T.topology; ∀ i, Representation.IsIrreducible (π i).representation)
    (hπa : letI := T.topology; ∀ i, IsAdmissible (π i).representation)
    (qπ : letI := T.topology
      ∀ i, (T.normalizedProductInductionFunctor (S i)).obj (fun j => (Y ⟨i, j⟩).obj) ⟶ π i)
    (hqπ : letI := T.topology; ∀ i, Function.Surjective (SmoothRep.hom (qπ i)))
    (e : Equiv.Perm (Fin (B.flatten S).length))
    (hmin : IsMinimalRepresentative B ((B.flatten S).permute e)
      ((B.flatten S).blockPermutation e)) :
    letI := T.topology
    IsSubquotient
      (CuspidalJacquetMultiplicity.oppositeJacquet T ((B.flatten S).permute e)
        ((T.normalizedProductInductionFunctor B).obj π).obj).ρ
      (((B.flatten S).permute e).blockTensor fun k =>
        (Y ((B.flattenBlockEquiv S).symm (e k))).obj.representation) := by
  let := T.topology
  let P := B.flatten S
  let fS := B.flattenBlockEquiv S
  let fLE := flattenedLeviEquiv F.Carrier B S
  -- the fine cuspidal representation and its pullback to the refined Levi
  obtain ⟨hωi, hωc⟩ := CuspidalSupport.glCuspidalTensor.{uV, uF} p F T n hn P
    (fun k => Y (fS.symm k))
  let ω : Rep.{uV} ℂ (P.Levi F.Carrier) :=
    Rep.of (P.blockTensor fun k => (Y (fS.symm k)).obj.representation)
  obtain ⟨hσi, hσa, -⟩ := fineTwistIrreducibleAdmissible.{uF, uV} p F T n B S ω hωi hωc 0 0
  let σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S) := Rep.of (ω.ρ.comp fLE.symm.toMonoidHom)
  have hσ := fineTwist_zero_zero T B S ω
  rw [hσ] at hσi hσa
  change Representation.IsIrreducible σ.ρ at hσi
  change IsAdmissible σ.ρ at hσa
  -- the coarse tensor of the factors
  let V : Rep.{max uF uV} ℂ (B.Levi F.Carrier) :=
    Rep.of (B.blockTensor fun i => (π i).representation)
  have hVa : IsAdmissible V.ρ := FiniteTensor.isAdmissible_external _ hπa
  have hVi : Representation.IsIrreducible V.ρ :=
    FiniteTensor.isIrreducible_external (fun i => (π i).representation)
      (fun i φ => (admissibleSchur_scalarEndomorphism _ (hπa i) (hπi i) φ).exists)
  let := hVi
  have hVnt : Nontrivial V.V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (B.Levi F.Carrier)) V.ρ.asModule
  -- the surjection from the inner induction of the fine representation
  obtain ⟨EFM⟩ := nonempty_innerInduced_flatten_equiv T B S (fun q => (Y q).obj)
  let qext := FiniteTensor.externalMap (fun i => SmoothRep.hom (qπ i))
  have hqext : Function.Surjective qext :=
    FiniteTensor.externalMapSurjectivity _ _ _ _ _ _ _ (fun i => SmoothRep.hom (qπ i)) hqπ
  let f : (innerInduced T B S σ).ρ.IntertwiningMap V.ρ := qext.comp EFM.toIntertwiningMap
  have hf : Function.Surjective f := hqext.comp EFM.surjective
  have hf0 : f ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := exists_ne (0 : V.V)
    obtain ⟨w, hw⟩ := hf v
    apply hv
    rw [← hw, hz]
    rfl
  -- refined second adjointness
  obtain ⟨E, -, -⟩ := Parabolic.normalizedSecondAdjointness.{uF, uV, max uF uV}.2 p F T n hn B S
  let i := E σ V hσa hVa f
  have hi0 : i ≠ 0 := by
    intro hz
    exact hf0 ((E σ V hσa hVa).injective (hz.trans (map_zero _).symm))
  let := hσi
  have hi : Function.Injective i :=
    (Representation.IsIrreducible.injective_or_eq_zero i).resolve_right hi0
  -- the embedding on the flattened Levi
  let i' : ω.ρ.IntertwiningMap ((innerJacquet T B S V).ρ.comp fLE.toMonoidHom) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap _ _ i.toLinearMap (fun g v => by
      have h := Representation.IntertwiningMap.isIntertwining _ _ i (fLE g) v
      change i (ω.ρ (fLE.symm (fLE g)) v) = _ at h
      rw [MulEquiv.symm_apply_apply] at h
      exact h)
  have hsub := IsSubquotient.transport
    (CuspidalSupport.conjugatesLevi_blockPermutation (F := F.Carrier) P e)
    (isSubquotient_of_injective i' hi)
  have hpiece := glGeometricPieceLifting.{uF, max uF uV} p F T n hn B (P.permute e) S
    (P.blockPermutation e) hmin
    (CuspidalSupport.conjugatesLevi_blockPermutation (F := F.Carrier) P e) V hVa.1
  exact (hpiece.trans hsub).of_equiv_right
    (CuspidalSupport.blockPermutationTensorEquiv P e
      (CuspidalSupport.conjugatesLevi_blockPermutation (F := F.Carrier) P e)
      (fun k => (Y (fS.symm k)).obj.representation))

end Piece

section Cast

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Subquotients given by labelled block tensors move along an equality of
shapes whose block labels correspond. -/
theorem isSubquotient_blockTensor_cast {n : ℕ} {C C' : BlockShape n} (h : C = C')
    (A : Rep.{uW} ℂ (GeneralLinear n F.Carrier)) {Λ : Type*} (rk : Λ → ℕ)
    (atom : letI := T.topology
      ∀ l, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (rk l) F.Carrier))
    (lab : Fin C.length → Λ) (lab' : Fin C'.length → Λ)
    (hs : ∀ k, C.size k = rk (lab k)) (hs' : ∀ k, C'.size k = rk (lab' k))
    (hlab : ∀ k, lab' (Fin.cast (congrArg BlockShape.length h) k) = lab k) :
    letI := T.topology
    IsSubquotient (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ
        (C.blockTensor fun k => ((hs k).symm ▸ atom (lab k)).representation) →
      IsSubquotient (CuspidalJacquetMultiplicity.oppositeJacquet T C' A).ρ
        (C'.blockTensor fun k => ((hs' k).symm ▸ atom (lab' k)).representation) := by
  subst h
  have hl : lab' = lab := funext hlab
  subst hl
  exact id

end Cast

end Langlands.Classification.A6ii

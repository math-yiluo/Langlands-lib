import Langlands.Representation.Unramified.PrincipalSeries
import Langlands.Representation.Parabolic.FlattenedProductInduction
import Langlands.Representation.RankinSelberg.InducedWhittakerQuotient
import Langlands.Representation.Classification.JuxtaposedJacquetImage
import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Tensor.SmoothSubquotients

/-!
# Spherical spectra of subquotients of products of spherical blocks

Let `σ_1, …, σ_k` be irreducible admissible representations of `GL_(m_i + 1)(F)` with
spherical spectra `s_i`, and let `A` be an irreducible admissible representation of
`GL_(r+1)(F)` with a nonzero `GL_(r+1)(O_F)`-fixed vector which is a subquotient of the
normalized induced representation `i(σ_1, …, σ_k)` from the standard upper block parabolic.
Then `A` has the concatenated spectrum `s_1 + ⋯ + s_k`.

The proof: each `σ_i` is a subquotient of an unramified principal series `i(χ_i)`; normalized
product induction carries factorwise subquotients to subquotients (exactness of normalized
induction); induction in stages identifies `i(i(χ_1), …, i(χ_k))` with the principal series of
the concatenated characters; and subquotients compose.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Langlands.Unramified.ProductInducedSpectrum

open Correspondence GeneralLinear Geometric

universe uF uV uW

section Induction

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- **Normalized product induction preserves factorwise subquotients.** If each `π_i` is a
subquotient of `ρ_i` (all smooth), then `i(π_1, …, π_k)` is a subquotient of
`i(ρ_1, …, ρ_k)`. -/
private theorem isSubquotientOf_normalizedProductInduced {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i))
    (hρ : letI := T.topology; ∀ i, IsSmooth (ρ i))
    (hπ : letI := T.topology; ∀ i, IsSmooth (π i))
    (h : ∀ i, IsSubquotientOf (ρ i) (π i)) :
    IsSubquotientOf (T.normalizedProductInduced B ρ) (T.normalizedProductInduced B π) := by
  let := T.topology
  choose U q hq using h
  let ι : ∀ i, (U i).toRepresentation.IntertwiningMap (ρ i) :=
    fun i => WeylBranchPieces.subtypeMap (U i)
  have hι : ∀ i, Function.Injective (ι i) := fun i => Subtype.val_injective
  have hU : ∀ i, IsSmooth (U i).toRepresentation := fun i =>
    isSmooth_of_injective (ι i) (hι i) (hρ i)
  let inducedInclusion := T.normalizedProductInducedMap B ι
  have hInclusion : Function.Injective inducedInclusion :=
    T.normalizedParabolicInducedMap_injective B (FiniteTensor.externalMap ι)
      (FiniteTensor.piTensorMap_injective (fun i => (ι i).toLinearMap) hι)
  let e := Classification.JuxtaposedShuffle.rangeEquivOfInjective inducedInclusion hInclusion
  let inducedQuotient := T.normalizedProductInducedMap B q
  have hQuotient : Function.Surjective inducedQuotient :=
    T.normalizedProductInducedMap_surjective B _ _ hU hπ q hq
  exact ⟨inducedInclusion.range, inducedQuotient.comp e.symm.toIntertwiningMap,
    hQuotient.comp e.symm.surjective⟩

end Induction

section Borel

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A scalar character with open kernel is smooth. -/
private theorem isSmooth_characterRepresentation {G : Type*} [Group G] [TopologicalSpace G]
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) : IsSmooth (characterRepresentation χ) := by
  intro x
  refine ⟨⟨χ.ker, hχ⟩, ?_⟩
  intro k
  change (χ k.val : ℂ) • x = x
  rw [MonoidHom.mem_ker.mp k.property, Units.val_one, one_smul]

/-- The unramified character of `GL_1(F)` with uniformizer value `z`, as a smooth
representation on `ℂ`. -/
private def characterObject (z : ℂˣ) :
    letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, 0} ℂ (GeneralLinear 1 F.Carrier) :=
  letI := F.canonicalTopologicalData.topology
  SmoothRep.of (characterRepresentation (determinantQuasiCharacter F 1 (character F z)))
    (isSmooth_characterRepresentation _ (F.canonicalTopologicalData.isOpen_ker_determinantUnramifiedCharacter 1 z))

/-- A shape of `GL_(r+1)` whose blocks all have size one is the Borel shape, after the
length cast; the induced representations of the same characters agree. -/
private theorem nonempty_borelCast_equiv (r L : ℕ) (hL : L = r + 1)
    (pos : ∀ _ : Fin L, 0 < 1) (sum : ∑ _ : Fin L, 1 = r + 1) (w : Fin L → ℂˣ) :
    letI := F.canonicalTopologicalData.topology
    Nonempty ((principalSeriesOfTuple F (fun q => w (Fin.cast hL.symm q))).Equiv
      (F.canonicalNormalizedProductInduced
        (⟨L, fun _ => 1, pos, sum⟩ : BlockShape (r + 1))
        (fun q => (characterObject F (w q)).representation))) := by
  let := F.canonicalTopologicalData.topology
  subst hL
  exact ⟨Representation.Equiv.refl _⟩

/-- Normalized product induction transports along an equality of shapes together with a
heterogeneous equality of the inducing families. -/
private theorem nonempty_equiv_of_shape_eq (T : F.TopologicalData) {n : ℕ} {B C : BlockShape n}
    (D : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (E : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (h : B = C) (hDE : HEq D E) :
    letI := T.topology
    Nonempty ((T.normalizedProductInduced B (fun i => (D i).representation)).Equiv
      (T.normalizedProductInduced C (fun i => (E i).representation))) := by
  let := T.topology
  subst h
  cases hDE
  exact ⟨Representation.Equiv.refl _⟩

/-- The multiset of a tuple is the sum of its singletons. -/
private theorem coe_ofTuple_eq_sum {n : ℕ} (z : Fin n → ℂˣ) :
    (Eigenvalues.ofTuple z : Multiset ℂˣ) = ∑ q, ({z q} : Multiset ℂˣ) := by
  change ((List.ofFn z : List ℂˣ) : Multiset ℂˣ) = _
  rw [← Fin.univ_val_map, Finset.sum_eq_multiset_sum]
  simpa only [Multiset.map_map, Function.comp_def] using
    (Multiset.sum_map_singleton ((Finset.univ : Finset (Fin n)).val.map z)).symm

/-- **Induction in stages for unramified principal series.** The normalized induction
`i(i(χ_1), …, i(χ_k))` of unramified principal series is equivalent to the principal series
of the concatenated tuple, whose multiset is the sum of the multisets. -/
private theorem exists_principalSeries_equiv_productInduced (r k : ℕ) (m : Fin k → ℕ)
    (hm : ∑ i, (m i + 1) = r + 1) (z : ∀ i, Fin (m i + 1) → ℂˣ) :
    ∃ Z : Fin (r + 1) → ℂˣ,
      (Eigenvalues.ofTuple Z : Multiset ℂˣ) = ∑ i, (Eigenvalues.ofTuple (z i) : Multiset ℂˣ) ∧
      Nonempty ((principalSeriesOfTuple F Z).Equiv
        (F.canonicalNormalizedProductInduced ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
          (fun i => principalSeriesOfTuple F (z i)))) := by
  let T := F.canonicalTopologicalData
  let B : BlockShape (r + 1) := ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
  let S : BlockRefinement B := fun i => borelShape (m i)
  let := T.topology
  let C : ∀ i j, SmoothRep.{0, uF, 0} ℂ (GeneralLinear ((S i).size j) F.Carrier) :=
    fun i j => characterObject F (z i j)
  let e := B.flattenBlockEquiv S
  let w : Fin (B.flatten S).length → ℂˣ := fun q => z (e.symm q).1 (e.symm q).2
  have hL : (B.flatten S).length = r + 1 := hm
  refine ⟨fun q => w (Fin.cast hL.symm q), ?_, ?_⟩
  · rw [coe_ofTuple_eq_sum]
    calc ∑ q : Fin (r + 1), ({w (Fin.cast hL.symm q)} : Multiset ℂˣ)
        = ∑ q : Fin (B.flatten S).length, ({w q} : Multiset ℂˣ) :=
          Fintype.sum_equiv (finCongr hL.symm) _ _ fun _ => rfl
      _ = ∑ x : (i : Fin k) × Fin (m i + 1), ({z x.1 x.2} : Multiset ℂˣ) :=
          Fintype.sum_equiv e.symm _ _ fun _ => rfl
      _ = ∑ i, ∑ j, ({z i j} : Multiset ℂˣ) :=
          Fintype.sum_sigma fun x : (i : Fin k) × Fin (m i + 1) => ({z x.1 x.2} : Multiset ℂˣ)
      _ = ∑ i, (Eigenvalues.ofTuple (z i) : Multiset ℂˣ) :=
          Finset.sum_congr rfl fun i _ => (coe_ofTuple_eq_sum (z i)).symm
  · let B' : BlockShape (r + 1) :=
      ⟨(B.flatten S).length, fun _ => 1, fun _ => Nat.one_pos, (B.flatten S).sum_eq⟩
    let eStages := Parabolic.flattenedProductInducedEquiv F T B S C
    have hFlatten := nonempty_equiv_of_shape_eq F T (B := B') (C := B.flatten S)
      (fun q => characterObject F (w q)) (Parabolic.flattenedSmoothFamily F T B S C) rfl HEq.rfl
    have hCast := nonempty_borelCast_equiv F r (B.flatten S).length hL
      (fun _ => Nat.one_pos) (B.flatten S).sum_eq w
    obtain ⟨eFlatten⟩ := hFlatten
    obtain ⟨eCast⟩ := hCast
    have eblock : ∀ i, (T.normalizedProductInduced (S i)
        (fun j => (C i j).representation)).Equiv (principalSeriesOfTuple F (z i)) :=
      fun i => Representation.Equiv.refl _
    exact ⟨((eCast.trans eFlatten).trans eStages).trans (T.normalizedProductInducedEquiv B eblock)⟩

end Borel

section Main

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance productSpectrumFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance productSpectrumGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- **The spherical spectrum of a subquotient of a product of spherical blocks.** -/
theorem exists_hasSphericalSpectrum_of_isSubquotientOf_productInduced
    (r k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
    (σ : ∀ i, AutomorphicObject.{uF, uV} F (m i).succPNat)
    (s : ∀ i, Eigenvalues (m i + 1))
    (hs : ∀ i, HasSphericalSpectrum F (σ i) (s i))
    (A : AutomorphicObject.{uF, uW} F r.succPNat)
    (hA : fixedVectors A.obj.representation (sphericalSubgroup F r) ≠ ⊥)
    (hsub : IsSubquotientOf
      (F.canonicalNormalizedProductInduced ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
        (fun i => (σ i).obj.representation))
      A.obj.representation) :
    ∃ t : Eigenvalues (r + 1), HasSphericalSpectrum F A t ∧
      (t : Multiset ℂˣ) = ∑ i, (s i : Multiset ℂˣ) := by
  choose z hz hzc using hs
  obtain ⟨Z, hZ, ⟨e⟩⟩ := exists_principalSeries_equiv_productInduced F r k m hm z
  let T := F.canonicalTopologicalData
  let B : BlockShape (r + 1) := ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
  have hps : letI := T.topology; ∀ i, IsSmooth (principalSeriesOfTuple F (z i)) := fun i =>
    T.isSmooth_normalizedProductInduced (borelShape (m i)) _
  have hσ : letI := T.topology; ∀ i, IsSmooth (σ i).obj.representation := fun i =>
    (σ i).obj.isSmooth
  have hstep := isSubquotientOf_normalizedProductInduced T B
    (fun i => principalSeriesOfTuple F (z i)) (fun i => (σ i).obj.representation)
    hps hσ (fun i => (hzc i).2)
  refine ⟨Eigenvalues.ofTuple Z, ⟨Z, rfl, hA, ?_⟩, ?_⟩
  · exact WeylBranchPieces.IsSubquotient.of_equiv_left e
      (WeylBranchPieces.IsSubquotient.trans hstep hsub)
  · rw [hZ]
    exact Finset.sum_congr rfl fun i _ => by rw [hz i]

end Main

end Langlands.Unramified.ProductInducedSpectrum

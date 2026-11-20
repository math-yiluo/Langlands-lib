import Langlands.Global.Factors.CuspidalSupportStatement
import Langlands.Global.FiniteAdelicGL.RestrictedProduct
import Langlands.Automorphic.LocalComponentFinitePlace
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Smooth.SeparatingIntertwiners
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof

/-! The finite-place extraction and sphericality in cuspidal support. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open scoped MonoidAlgebra Topology

namespace Langlands.Global

open Automorphic CompletionPadic Correspondence CuspidalPairFunctionalEquation
open FiniteAdelicGL _root_.Representation TwoFactorExistence

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup
  padicCategoryLocalSpaceAddCommGroup

universe u uE

variable {F : Type u} [Field F] [NumberField F]

local instance quotientAddCommGroup {n : ℕ} (Q : OperatorSubquotient F n) :
    AddCommGroup Q.Space := Submodule.Quotient.addCommGroup _

namespace FiniteAdelicGL

/-- An open subgroup contains the embedded local integral subgroups outside
one finite set of finite places. -/
theorem exists_localIntegral_le (n : ℕ) (L : OpenSubgroup (FiniteAdelicGL F n)) :
    ∃ S : Finset (FinitePlace F), ∀ v ∉ S, ∀ g ∈ localIntegral F n v,
      localInclusion F n v g ∈ L := by
  classical
  let A := fun v => localIntegral F n v
  let R := fun v => FiniteLocalGL F n v
  let C := fun v => (A v : Set (R v))
  let t : (∀ v, A v) → FiniteAdelicGL F n :=
    (restrictedProductEquiv F n).symm ∘ RestrictedProduct.structureMap R C Filter.cofinite
  have ht : Continuous t := (restrictedProductEquiv F n).symm.continuous.comp
    (RestrictedProduct.isEmbedding_structureMap (R := R) (A := C)
      (𝓕 := Filter.cofinite)).continuous
  have ht1 : t 1 = 1 := by
    apply ext_localProjection F n
    intro v
    change localProjection F n v (fromRestrictedProduct F n
      (RestrictedProduct.structureMap R C Filter.cofinite (1 : ∀ v, A v))) =
      localProjection F n v 1
    rw [localProjection_fromRestrictedProduct, map_one]
    rfl
  have h : t ⁻¹' (L : Set (FiniteAdelicGL F n)) ∈ 𝓝 (1 : ∀ v, A v) :=
    (L.isOpen.preimage ht).mem_nhds (show t 1 ∈ L by rw [ht1]; exact L.one_mem)
  rw [nhds_pi] at h
  obtain ⟨S, U, hU, hS⟩ := Filter.mem_pi'.mp h
  refine ⟨S, fun v hv g hg => ?_⟩
  let y : ∀ w, A w := Function.update (1 : ∀ w, A w) v ⟨g, hg⟩
  have hy : y ∈ (S : Set (FinitePlace F)).pi U := by
    intro w hw
    have hne : w ≠ v := fun h => hv (h ▸ hw)
    rw [show y w = 1 from Function.update_of_ne hne _ _]
    exact mem_of_mem_nhds (hU w)
  have hty : t y = localInclusion F n v g := by
    apply ext_localProjection F n
    intro w
    change localProjection F n w (fromRestrictedProduct F n
      (RestrictedProduct.structureMap R C Filter.cofinite y)) =
      localProjection F n w (localInclusion F n v g)
    rw [localProjection_fromRestrictedProduct]
    change (y w : R w) = _
    by_cases hw : w = v
    · subst w
      rw [show y v = ⟨g, hg⟩ from Function.update_self _ _ _, localProjection_localInclusion]
    · rw [show y w = 1 from Function.update_of_ne hw _ _,
        localProjection_localInclusion_of_ne F n v w hw]
      rfl
  have : t y ∈ L := hS hy
  rwa [hty] at this

end FiniteAdelicGL

private theorem exists_nonzero_quotient_vector {r : ℕ} (Q : IrreducibleOperatorSubquotient F r) :
    ∃ x : Q.subquotient.Space, x ≠ 0 := by
  obtain ⟨f, hf⟩ := Q.exists_representative_not_mem_lower
  exact ⟨Q.subquotient.projection f, fun hz => hf ((Q.subquotient.projection_eq_zero_iff f).mp hz)⟩

private theorem exists_spherical_subrepresentations_outside_of_commutant (r : ℕ)
    {X : Type u} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (FiniteAdelicGL F (r + 1)) X) (hρ : IsSmooth ρ)
    (C : FinitePlace F → Set (Module.End ℂ X))
    (hC : ∀ v, JointIsotypic.CommutesWith (ρ.comp (localInclusion F (r + 1) v).toMonoidHom) (C v))
    (hI : ∀ v, JointIsotypic.IsJointlyIrreducible
      (ρ.comp (localInclusion F (r + 1) v).toMonoidHom) (C v))
    (x : X) (hx : x ≠ 0) :
    ∃ S : Finset (FinitePlace F), ∀ v ∉ S,
      ∀ U : Subrepresentation (ρ.comp (localInclusion F (r + 1) v).toMonoidHom), U ≠ ⊥ →
        fixedVectors U.toRepresentation (sphericalSubgroup (padicField v) r) ≠ ⊥ := by
  obtain ⟨L, hL⟩ := hρ x
  obtain ⟨S, hS⟩ := FiniteAdelicGL.exists_localIntegral_le (r + 1) L
  refine ⟨S, fun v hv U hU => ?_⟩
  let j := localInclusion F (r + 1) v
  let K := localIntegral F (r + 1) v
  have hxK : x ∈ fixedVectors (ρ.comp j.toMonoidHom) K.toSubgroup :=
    TwoFactorExistence.mem_fixedVectors_iff.mpr fun g hg =>
      hL ⟨localInclusion F (r + 1) v g, hS v hv g hg⟩
  have hs := isSmooth_comp j.toMonoidHom j.continuous hρ
  obtain ⟨a, ha, ha0, haK⟩ := JointIsotypic.exists_fixed_of_ne_bot (hC v) (hI v)
    hs K (isCompact_localIntegral F (r + 1) v) hx hxK hU
  rw [← localIntegral_eq_sphericalSubgroup F v r]
  intro hbot
  have ha' : (⟨a, ha⟩ : U.toSubmodule) ∈ fixedVectors U.toRepresentation K.toSubgroup :=
    TwoFactorExistence.mem_fixedVectors_iff.mpr fun g hg =>
      Subtype.ext ((TwoFactorExistence.mem_fixedVectors_iff.mp haK) g hg)
  rw [hbot] at ha'
  exact ha0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).mp ha'))

/-- A single finite smooth vector of an irreducible operator subquotient gives
sphericality of every nonzero local subrepresentation outside a finite set. -/
theorem exists_spherical_subrepresentations_outside (r : ℕ)
    (Q : IrreducibleOperatorSubquotient F r) :
    ∃ S : Finset (FinitePlace F), ∀ v ∉ S,
      ∀ U : Subrepresentation (Q.subquotient.localRepresentation v), U ≠ ⊥ →
        fixedVectors U.toRepresentation (sphericalSubgroup (padicField v) r) ≠ ⊥ :=
  (exists_nonzero_quotient_vector Q).elim fun x hx =>
    exists_spherical_subrepresentations_outside_of_commutant r
      Q.subquotient.finiteRepresentation Q.subquotient.finiteRepresentation_isSmooth
      Q.subquotient.localCentralizerOperators Q.subquotient.commutesWith_localCentralizerOperators
      (Q.subquotient.isJointlyIrreducible_localCentralizerOperators Q.irreducible) x hx

private theorem exists_local_constituent_of_subquotient
    {G H : Type u} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    {E : Type uE} [AddCommGroup E] [Module ℂ E]
    {X Y : Type u} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G E} {τ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (j : H →* G) (hj : Continuous j) (hρ : IsSmooth ρ) (hσ : IsAdmissible σ)
    (hArt : IsArtinian ℂ[H] σ.asModule)
    (hsub : IsSubquotientOf ρ τ) (hsep : HasSeparatingIntertwiners (ρ.comp j) σ)
    (x : X) (hx : x ≠ 0) :
    ∃ U : Subrepresentation (τ.comp j), U.toRepresentation.IsIrreducible ∧
      IsSubquotientOf σ U.toRepresentation := by
  obtain ⟨N, q, hq⟩ := hsub
  let qv : IntertwiningMap (N.toRepresentation.comp j) (τ.comp j) :=
    { toLinearMap := q.toLinearMap, isIntertwining' g := q.isIntertwining' (j g) }
  obtain ⟨y, hy⟩ := hq x
  have hs : IsSmooth (N.toRepresentation.comp j) :=
    isSmooth_comp j hj (isSmooth_toRepresentation hρ N)
  have hsepN : HasSeparatingIntertwiners (N.toRepresentation.comp j) σ := by
    intro y hy
    let i : IntertwiningMap (N.toRepresentation.comp j) (ρ.comp j) :=
      { toLinearMap := N.toSubmodule.subtype, isIntertwining' _ := rfl }
    apply Subtype.ext
    exact hsep y.val (fun f => hy (f.comp i))
  exact hsepN.exists_irreducible_subrepresentation hs hσ hArt qv ⟨y, fun hz => hx (hy.symm.trans hz)⟩

private theorem ne_bot_of_irreducible_subrepresentation
    {G X : Type u} [Group G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    (U : Subrepresentation ρ) (hU : U.toRepresentation.IsIrreducible) : U ≠ ⊥ := by
  have : IsSimpleModule ℂ[G] U.toRepresentation.asModule :=
    (irreducible_iff_isSimpleModule_asModule _).mp hU
  have : Nontrivial U.toRepresentation.asModule :=
    IsSimpleModule.nontrivial ℂ[G] U.toRepresentation.asModule
  have : Nontrivial U.toSubmodule :=
    U.toRepresentation.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨x, hx⟩ := exists_ne (0 : U.toSubmodule)
  intro hbot
  apply hx
  apply Subtype.ext
  have hx' : x.val ∈ (⊥ : Subrepresentation ρ) := hbot ▸ x.property
  exact TwoFactorExistence.mem_bot_iff.mp hx'

section LocalProduct

variable (v : FinitePlace F) {n : ℕ} (B : GeneralLinear.BlockShape n)
  {W : Fin B.length → Type u} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) (padicField v).Carrier) (W i))

private theorem isArtinian_localNormalizedProduct (hn : 0 < n)
    (hs : letI := (padicField v).canonicalTopologicalData.topology; ∀ i, IsSmooth (σ i))
    (hi : ∀ i, (σ i).IsIrreducible) :
    IsArtinian ℂ[FiniteLocalGL F n v] ((padicField v).canonicalNormalizedProductInduced B σ).asModule := by
  let D := (padicField v).canonicalTopologicalData
  let := D.topology
  let A (i : Fin B.length) : SmoothRep.{0, u, u} ℂ (GeneralLinear (B.size i) (padicField v).Carrier) :=
    SmoothRep.of (σ i) (hs i)
  have hfin := Classification.irreducibleProductFiniteLength.{u, u} (padicField v) D
    n hn B A hi
  exact (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2

private theorem isAdmissible_localNormalizedProduct
    (hσ : letI := (padicField v).canonicalTopologicalData.topology; ∀ i, IsAdmissible (σ i)) :
    IsAdmissible ((padicField v).canonicalNormalizedProductInduced B σ) := by
  let D := (padicField v).canonicalTopologicalData
  have hadm : @IsAdmissible ℂ (FiniteLocalGL F n v) _ _ _ _ _
      ((padicField v).canonicalGeneralLinearTopology n)
      ((padicField v).canonicalNormalizedProductInduced B σ) := by
    let := D.topology
    exact Parabolic.normalizedInductionAdmissibility (padicField v) D B _ (B.blockTensor σ)
      (FiniteTensor.isAdmissible_external σ hσ)
  exact Eq.mpr (congrArg
    (fun t : TopologicalSpace (FiniteLocalGL F n v) =>
      @IsAdmissible ℂ (FiniteLocalGL F n v) _ _ _ _ _ t
        ((padicField v).canonicalNormalizedProductInduced B σ))
    (localGL_topology_eq F v n)) hadm

end LocalProduct

variable [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ} {T : ∀ i, CuspidalOperatorRealization F (m i)}

/-- The actual normalized induction at `v` of the finite cuspidal block components. -/
abbrev finiteLocalNormalizedInduced (hm : ∑ i, (m i + 1) = r + 1)
    (P : ∀ i, CuspidalSpectralPresentation.{u, u} (T i)) (v : FinitePlace F) :=
  (padicField v).canonicalNormalizedProductInduced
    ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
    (fun i => ((P i).localComponent v).representation)

set_option maxHeartbeats 800000 in
/-- A smooth finite adelic source for the given operator quotient suffices
when its local restrictions have separating intertwiners to the respective
normalized inductions. -/
theorem isFiniteInducedConstituent_of_separatingIntertwiners
    (hm : ∑ i, (m i + 1) = r + 1) (P : ∀ i, CuspidalSpectralPresentation.{u, u} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)) (Q : IrreducibleOperatorSubquotient F r)
    {E : Type uE} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (FiniteAdelicGL F (r + 1)) E) (hρ : IsSmooth ρ)
    (hsub : IsSubquotientOf ρ Q.subquotient.finiteRepresentation)
    (hsep : ∀ v : FinitePlace F,
      HasSeparatingIntertwiners (ρ.comp (localInclusion F (r + 1) v).toMonoidHom)
        (finiteLocalNormalizedInduced hm P v)) :
    IsFiniteInducedConstituent hm P h Q := by
  classical
  refine (exists_nonzero_quotient_vector Q).elim ?_
  intro x hx
  let B : GeneralLinear.BlockShape (r + 1) := ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
  have hArt (v : FinitePlace F) :
      IsArtinian ℂ[FiniteLocalGL F (r + 1) v] (finiteLocalNormalizedInduced hm P v).asModule :=
    isArtinian_localNormalizedProduct v B (fun i => ((P i).localComponent v).representation)
      (Nat.succ_pos _) (fun i => ((P i).localComponent v).isSmooth_canonical) (fun i => (h i v).1)
  have hadm (v : FinitePlace F) : IsAdmissible (finiteLocalNormalizedInduced hm P v) :=
    isAdmissible_localNormalizedProduct v B (fun i => ((P i).localComponent v).representation)
      (fun i => ((P i).localComponent v).isAdmissible_canonical_iff.mpr (h i v).2)
  have hU (v : FinitePlace F) :
      ∃ U : Subrepresentation (Q.subquotient.localRepresentation v),
        U.toRepresentation.IsIrreducible ∧
        IsSubquotientOf (finiteLocalNormalizedInduced hm P v) U.toRepresentation := by
    let j := localInclusion F (r + 1) v
    exact exists_local_constituent_of_subquotient j.toMonoidHom j.continuous hρ
      (hadm v) (hArt v) hsub (hsep v) x hx
  choose U hUirr hUsub using hU
  have hUadm (v : FinitePlace F) : IsAdmissible (U v).toRepresentation := by
    obtain ⟨N', p, hp⟩ := hUsub v
    exact Unramified.SphericalExistence.isAdmissible_of_surjective
      (compactOpen_cofinal F (r + 1) v) p hp
      (isAdmissible_of_injective (subtypeHom N') N'.toSubmodule.injective_subtype (hadm v))
  let A (v : FinitePlace F) : AutomorphicObject.{u, u} (padicField v) r.succPNat :=
    let hcanon := isAdmissible_canonicalTopology (hUadm v)
    ⟨⟨Rep.of (U v).toRepresentation, hcanon.1⟩, hUirr v, hcanon⟩
  obtain ⟨S, hS⟩ := exists_spherical_subrepresentations_outside r Q
  refine ⟨A, S, ?_, ?_, ?_⟩
  · intro v
    change IsSubquotientOf (finiteLocalNormalizedInduced hm P v) (U v).toRepresentation
    exact hUsub v
  · intro v hv
    change fixedVectors (U v).toRepresentation (sphericalSubgroup (padicField v) r) ≠ ⊥
    exact hS v hv (U v) (ne_bot_of_irreducible_subrepresentation (U v) (hUirr v))
  · intro v
    change ∃ f : IntertwiningMap (U v).toRepresentation (Q.subquotient.localRepresentation v),
      Function.Injective f.toLinearMap
    exact ⟨subtypeHom (U v), (U v).toSubmodule.injective_subtype⟩

end Langlands.Global

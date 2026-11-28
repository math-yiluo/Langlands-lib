import Langlands.BushnellKutzko.ZeroDepthNonCuspidalStepStatement
import Langlands.BushnellKutzko.BetaExtensionStatement
import Langlands.BushnellKutzko.ZeroDepthCharacterStepLemmas
import Langlands.BushnellKutzko.LevelZeroLayerReductionSurjective
import Langlands.BushnellKutzko.PrincipalChainResidueDegree
import Langlands.BushnellKutzko.PositiveZeroSplitType
import Langlands.BushnellKutzko.GLSimpleTypes
import Langlands.BushnellKutzko.BetaExtensionTwist.Algebra
import Langlands.BushnellKutzko.MinimalSimpleStratumPolynomialProof
import Langlands.BushnellKutzko.CorestrictionIntegers
import Langlands.Representation.Clifford.TensorFactor
import Langlands.Representation.Clifford.IrreduciblePullback
import Langlands.Representation.FiniteGeneralLinear.FiniteProductIrreducibles
import Langlands.Representation.EquivalencePullback

/-! # Constructions for the depth-zero step of BK93 (8.1.5)

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), proof of
(8.1.5), printed pp. 268–269: an irreducible smooth representation `π` of `GL_N(F)` containing a
simple character `θ` of a simple stratum `[𝔄, n, 0, β]` contains a Heisenberg representation
`η` over `θ` (`exists_heisenberg_constituent`), and, given a `β`-extension `κ` of `η`, a
representation `κ ⊗ ξ` of `J(β, 𝔄)` with `ξ` irreducible and trivial on `J^1(β, 𝔄)`
(`exists_beta_tensor_intertwining`). The restriction of `ξ` to `U(𝔅_β)` is the inflation of an
external tensor product of irreducible representations of the layer groups
(`exists_equiv_classTensor_comp`).

The module also contains the transport of representations of subgroups of `Aut_F(F^N)` to
subgroups of `GL_N(F)` (`matrixSmoothRep`), and generic lemmas on descent through surjections,
layer reductions and smoothness of tensor products used to assemble the step.
-/

open IsLocalRing Module ValuativeRel Representation

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uπ uρ uG uH uW

section Descent

variable {H : Type uH} [Group H] {P : Type uG} [Group P] {W : Type uW} [AddCommGroup W]
  [Module ℂ W]

/-- A representation trivial on the kernel of a surjective homomorphism factors through it. -/
theorem exists_comp_eq_of_surjective (φ : H →* P) (hφ : Function.Surjective φ)
    (ρ : Representation ℂ H W) (hker : ∀ h, φ h = 1 → ρ h = 1) :
    ∃ ρ' : Representation ℂ P W, ρ'.comp φ = ρ := by
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  let ρq : Representation ℂ (H ⧸ φ.ker) W :=
    QuotientGroup.lift φ.ker ρ fun h hh => MonoidHom.mem_ker.mpr (hker h hh)
  refine ⟨ρq.comp e.symm.toMonoidHom, ?_⟩
  ext1 h
  have he : e.symm (φ h) = (h : H ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change ρq (e.symm (φ h)) = ρ h
  rw [he]
  rfl

end Descent

section External

variable {ι : Type} [Fintype ι] {G : ι → Type uG} [∀ i, Group (G i)] [∀ i, Fintype (G i)]

/-- The external tensor product of representatives of irreducible classes `a i` of the factors,
each realized on a coordinate space. -/
def classTensor (a : ∀ i, FiniteRep.IrreducibleClass (G i)) :
    Representation ℂ (∀ i, G i)
      (PiTensorProduct ℂ fun i => Fin (finrank ℂ (FiniteRep.VirtualCharacter.rep (a i))) → ℂ) :=
  (PiTensorProduct.mapMonoidHom (R := ℂ)
    (s := fun i => Fin (finrank ℂ (FiniteRep.VirtualCharacter.rep (a i))) → ℂ)).comp
    (MonoidHom.piMap fun i => Clifford.coordinateRep (FiniteRep.VirtualCharacter.rep (a i)).ρ)

omit [Fintype ι] [∀ i, Fintype (G i)] in
/-- The coordinate realization of a representative of an irreducible class is irreducible. -/
theorem isIrreducible_coordinateRep_rep {H : Type uH} [Group H] [Fintype H]
    (a : FiniteRep.IrreducibleClass H) :
    (Clifford.coordinateRep (FiniteRep.VirtualCharacter.rep a).ρ).IsIrreducible :=
  Clifford.isIrreducible_of_equiv (Clifford.coordinateEquiv _)
    (FiniteRep.VirtualCharacter.isIrreducible_rep a)

omit [Fintype ι] [∀ i, Fintype (G i)] in
/-- For a constant family of classes, `classTensor` is the tensor power of the coordinate
realization of the class. -/
theorem classTensor_const {H : Type uH} [Group H] [Fintype H]
    (c : FiniteRep.IrreducibleClass H) (e : ℕ) :
    classTensor (fun _ : Fin e => c) =
      tensorPowerRepresentation (Clifford.coordinateRep (FiniteRep.VirtualCharacter.rep c).ρ) e :=
  rfl

omit [Fintype ι] [∀ i, Fintype (G i)] in
/-- Transport of an equivalence `ξ ∘ ι ≅ (classTensor (c, …, c)) ∘ φ` along an isomorphism
`ε : H ≃ U` with `ι ∘ ε⁻¹ = ι'`: then `ξ ∘ ι'` is equivalent to the inflation along `φ ∘ ε⁻¹` of
the tensor power of the coordinate realization of `c`. -/
theorem nonempty_equiv_tensorPower_comp {P : Type uH} [Group P] [Fintype P] {H : Type uW}
    [Group H] {U : Type uF} [Group U] {J : Type uG} [Group J] {d m : ℕ}
    (ξ : Representation ℂ J (Fin d → ℂ)) (ι : H →* J) (ε : H ≃* U) (ι' : U →* J)
    (hι : ∀ u, ι (ε.symm u) = ι' u) (c : FiniteRep.IrreducibleClass P) (φ : H →* (Fin m → P))
    (Φ : Representation.Equiv (ξ.comp ι) ((classTensor (fun _ : Fin m => c)).comp φ)) :
    Nonempty (Representation.Equiv (ξ.comp ι')
      ((tensorPowerRepresentation (Clifford.coordinateRep (FiniteRep.VirtualCharacter.rep c).ρ)
        m).comp (φ.comp ε.symm.toMonoidHom))) := by
  have h : (ξ.comp ι).comp ε.symm.toMonoidHom = ξ.comp ι' := by
    ext1 u
    exact congrArg ξ (hι u)
  have Φ' := Cohomology.HyperextAbutment.equivComp Φ ε.symm.toMonoidHom
  rw [h, MonoidHom.comp_assoc, classTensor_const] at Φ'
  exact ⟨Φ'⟩

/-- An irreducible representation of a finite product of finite groups on a coordinate space is
equivalent to the external tensor product of representatives of irreducible classes of the
factors. -/
theorem exists_equiv_classTensor {d : ℕ} (ρ : Representation ℂ (∀ i, G i) (Fin d → ℂ))
    (hρ : ρ.IsIrreducible) :
    ∃ a : ∀ i, FiniteRep.IrreducibleClass (G i),
      Nonempty (Representation.Equiv ρ (classTensor a)) := by
  classical
  obtain ⟨a, ⟨E⟩⟩ := FiniteRep.exists_externalRep_equiv (FDRep.of ρ) hρ
  let V (i : ι) := FiniteRep.VirtualCharacter.rep (a i)
  let C (i : ι) := (Module.finBasis ℂ (V i)).equivFun
  refine ⟨a, ⟨E.trans ?_⟩⟩
  refine Representation.Equiv.mk (PiTensorProduct.congr C) fun g => ?_
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro m
  change PiTensorProduct.congr C (FiniteTensor.external (fun i => (V i).ρ) g
      (PiTensorProduct.tprod ℂ m)) =
    PiTensorProduct.map (fun i => Clifford.coordinateRep (V i).ρ (g i))
      (PiTensorProduct.congr C (PiTensorProduct.tprod ℂ m))
  rw [FiniteTensor.external_tprod, PiTensorProduct.congr_tprod, PiTensorProduct.congr_tprod,
    PiTensorProduct.map_tprod]
  congr 1
  funext i
  change C i ((V i).ρ (g i) (m i)) = C i ((V i).ρ (g i) ((C i).symm (C i (m i))))
  rw [LinearEquiv.symm_apply_apply]

/-- **Layer decomposition.** Let `ξ` be an irreducible representation of `K` on a coordinate
space, `ι : H →* K` a homomorphism whose image acts through all of the image of `ξ`, and
`φ : H →* ∏_i G_i` a surjection onto a finite product of finite groups with `ξ ∘ ι` trivial on
its kernel. Then `ξ ∘ ι` is equivalent to the inflation along `φ` of an external tensor product of
irreducible representations of the factors. -/
theorem exists_equiv_classTensor_comp {H : Type uH} [Group H] {K : Type uW} [Group K] {d : ℕ}
    (ξ : Representation ℂ K (Fin d → ℂ)) (hξ : ξ.IsIrreducible) (ι' : H →* K)
    (hι : ∀ g, ∃ x, ξ g = ξ (ι' x)) (φ : H →* ∀ i, G i) (hφ : Function.Surjective φ)
    (hker : ∀ h, φ h = 1 → ξ (ι' h) = 1) :
    ∃ a : ∀ i, FiniteRep.IrreducibleClass (G i),
      Nonempty (Representation.Equiv (ξ.comp ι') ((classTensor a).comp φ)) := by
  have h1 : Representation.IsIrreducible (ξ.comp ι') := (Clifford.isIrreducible_comp_iff ξ ι' hι).mpr hξ
  obtain ⟨ξ', hξ'⟩ := exists_comp_eq_of_surjective φ hφ (ξ.comp ι') hker
  rw [← hξ'] at h1 ⊢
  have h2 : ξ'.IsIrreducible := FiniteRepresentation.SplitDegree.isIrreducible_of_comp ξ' φ h1
  obtain ⟨a, ⟨E⟩⟩ := exists_equiv_classTensor ξ' h2
  exact ⟨a, ⟨Cohomology.HyperextAbutment.equivComp E φ⟩⟩

end External

section Principal

variable {O : Type*} {K : Type*} {V : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

/-- If every layer `L_i / L_{i+1}`, `0 ≤ i < e`, of a lattice chain has a residue-field basis
indexed by `Fin r`, then every index `(L_j : L_{j+1})` is the number of elements of the
residue-field space of dimension `r`. -/
theorem LatticeChain.relIndex_eq_of_bases (L : LatticeChain O K V) {r : ℕ}
    (b : ∀ i : Fin L.period, Module.Basis (Fin r) (ResidueField O) (L.Layer (i : ℕ))) (j : ℤ) :
    (L.lattice (j + 1)).toAddSubgroup.relIndex (L.lattice j).toAddSubgroup =
      Nat.card (Fin r → ResidueField O) := by
  obtain ⟨s, ⟨e⟩⟩ := L.exists_layer_linearEquiv j
  rw [← L.natCard_interval_eq_relIndex j (j + 1)]
  change Nat.card (L.Layer j) = _
  rw [← Nat.card_congr e.toEquiv]
  exact Nat.card_congr (b s).equivFun.toEquiv

end Principal

section PairIsomorphic

variable {G : Type uG} [Group G] {J₁ J₂ : Subgroup G} {W₁ : Type uW} [AddCommGroup W₁]
  [Module ℂ W₁] {W₂ : Type uH} [AddCommGroup W₂] [Module ℂ W₂]

/-- A pair isomorphic to an irreducible pair is irreducible. -/
theorem IsPairIsomorphic.isIrreducible {ρ₁ : Representation ℂ J₁ W₁}
    {ρ₂ : Representation ℂ J₂ W₂} (h : IsPairIsomorphic ρ₁ ρ₂) (h₂ : ρ₂.IsIrreducible) :
    ρ₁.IsIrreducible := by
  obtain ⟨hJ, ⟨e⟩⟩ := h
  exact FiniteRepresentation.SplitDegree.isIrreducible_of_comp ρ₁ _
    (Clifford.isIrreducible_of_equiv e.symm h₂)

end PairIsomorphic

section Transport

variable {F : Type uF} [Field F] {n : ℕ}

local notation "Aut" => (Module.End F (Fin n → F))ˣ
local notation "toAut" => (Matrix.GeneralLinearGroup.toLin : GeneralLinear n F ≃* Aut)

/-- The subgroup of `GL_n(F)` corresponding to a subgroup of `Aut_F(F^n)`. -/
def matrixSubgroup (J : Subgroup Aut) : Subgroup (GeneralLinear n F) :=
  J.comap (toAut).toMonoidHom

theorem glSubgroupToAut_matrixSubgroup (J : Subgroup Aut) :
    glSubgroupToAut (matrixSubgroup J) = J :=
  Subgroup.map_comap_eq_self_of_surjective (toAut).surjective _

/-- The identification of the matrix subgroup with the subgroup of `Aut_F(F^n)`. -/
def matrixSubgroupHom (J : Subgroup Aut) : matrixSubgroup J →* J :=
  ((toAut).toMonoidHom.comp (matrixSubgroup J).subtype).codRestrict _ fun x => x.2

theorem matrixSubgroupHom_symm (J : Subgroup Aut) (x : glSubgroupToAut (matrixSubgroup J)) :
    ((matrixSubgroupHom J ((glSubgroupToAutEquiv (matrixSubgroup J)).symm x) : J) : Aut) = x :=
  congrArg Subtype.val ((glSubgroupToAutEquiv (matrixSubgroup J)).apply_symm_apply x)

/-- A representation of a subgroup of `Aut_F(F^n)`, transported to the matrix subgroup, on a
carrier lifted to the universe `uρ`. -/
def liftedRep {J : Subgroup Aut} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ J W) : Representation ℂ (matrixSubgroup J) (ULift.{uρ} W) :=
  (MonoidHom.ofClass ((ULift.moduleEquiv : ULift.{uρ} W ≃ₗ[ℂ] W).symm.conjAlgEquiv ℂ)).comp
    (ρ.comp (matrixSubgroupHom J))

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private local instance transportEndTopology : TopologicalSpace (Module.End F (Fin n → F)) :=
  moduleTopology F _

theorem isSmooth_liftedRep {J : Subgroup Aut} {W : Type} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ J W} (hρ : IsSmoothRepresentation ρ) :
    IsSmooth (liftedRep.{uF, uρ} ρ) := by
  obtain ⟨L, m, hL⟩ := hρ
  intro v
  let H : Subgroup (matrixSubgroup J) :=
    (L.unitFiltration m).comap ((toAut).toMonoidHom.comp (matrixSubgroup J).subtype)
  have hH : IsOpen (H : Set (matrixSubgroup J)) :=
    (isOpen_unitFiltration L m).preimage
      ((generalLinearToLinContinuous (F := F) (n := n)).continuous.comp continuous_subtype_val)
  refine ⟨⟨H, hH⟩, ?_⟩
  rw [fixedVectors, Representation.mem_invariants]
  intro g
  have h1 : ρ (matrixSubgroupHom J g) = 1 := hL _ g.2
  change ULift.up (ρ (matrixSubgroupHom J g) v.down) = v
  rw [h1]
  rfl

/-- A smooth representation of a subgroup of `Aut_F(F^n)`, as a smooth representation of the
corresponding matrix subgroup. -/
def matrixSmoothRep {J : Subgroup Aut} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ J W) (hρ : IsSmoothRepresentation ρ) :
    SmoothRep.{0, uF, uρ} ℂ (matrixSubgroup J) :=
  SmoothRep.of (liftedRep.{uF, uρ} ρ) (isSmooth_liftedRep hρ)

theorem isPairIsomorphic_matrixSmoothRep {J : Subgroup Aut} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ J W) (hρ : IsSmoothRepresentation ρ) :
    IsPairIsomorphic (glRepresentationToAut (matrixSmoothRep.{uF, uρ} ρ hρ)) ρ := by
  refine ⟨glSubgroupToAut_matrixSubgroup J, ⟨Representation.Equiv.mk ULift.moduleEquiv
    fun u => ?_⟩⟩
  apply LinearMap.ext
  intro x
  have hu : matrixSubgroupHom J ((glSubgroupToAutEquiv (matrixSubgroup J)).symm
      ((MulEquiv.subgroupCongr (glSubgroupToAut_matrixSubgroup J)).symm u)) = u :=
    Subtype.ext (matrixSubgroupHom_symm J _)
  change ρ (matrixSubgroupHom J ((glSubgroupToAutEquiv (matrixSubgroup J)).symm
      ((MulEquiv.subgroupCongr (glSubgroupToAut_matrixSubgroup J)).symm u))) x.down =
    ρ u x.down
  rw [hu]

theorem containsType_matrixSmoothRep (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
    {J : Subgroup Aut} {W : Type} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ J W} (hρ : IsSmoothRepresentation ρ)
    (f : ρ.IntertwiningMap (π.representation.comp ((toAut).symm.toMonoidHom.comp J.subtype)))
    (hf : f ≠ 0) : ContainsType π (matrixSmoothRep.{uF, uρ} ρ hρ) := by
  refine ⟨⟨f.toLinearMap ∘ₗ ULift.moduleEquiv.toLinearMap, fun k => ?_⟩, ?_⟩
  · apply LinearMap.ext
    intro x
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ f (matrixSubgroupHom J k) x.down
    change f (ρ (matrixSubgroupHom J k) x.down) =
      π.representation ((toAut).symm ((toAut) (k : GeneralLinear n F))) (f x.down) at h1
    rw [MulEquiv.symm_apply_apply] at h1
    exact h1
  · intro h0
    apply hf
    apply Representation.IntertwiningMap.toLinearMap_injective
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap h0)
      (ULift.up x)

end Transport

section Heisenberg

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

local notation "Aut" => (Module.End F (Fin n → F))ˣ
local notation "toAut" => (Matrix.GeneralLinearGroup.toLin : GeneralLinear n F ≃* Aut)

/-- The restriction of a representation of `GL_n(F)` to a subgroup of `Aut_F(F^n)`. -/
abbrev autRestrict (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)) (J : Subgroup Aut) :
    Representation ℂ J π :=
  π.representation.comp ((toAut).symm.toMonoidHom.comp J.subtype)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `U^m(𝔄) ∩ H` is normal in a subgroup `H` of `U(𝔄)`. -/
theorem unitFiltration_subgroupOf_normal (L : LatticeChain 𝒪[F] F (Fin n → F))
    {H : Subgroup Aut} (hH : H ≤ L.unitFiltration 0) (m : ℕ) :
    ((L.unitFiltration m).subgroupOf H).Normal :=
  ⟨fun h hh j => by
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    have := L.inv_mul_mul_mem_unitFiltration (hH (j⁻¹).2) hh
    simpa [mul_assoc] using this⟩

set_option maxHeartbeats 1000000 in
/-- **A Heisenberg representation in `π` (BK93 p. 268).** If `π` contains the character `θ` of
`H^1(β, 𝔄)`, the `J(β, 𝔄)`-span `X` of a `θ`-eigenvector is finite-dimensional, and some
irreducible `J^1(β, 𝔄)`-subrepresentation of `X` lies over `θ`. -/
theorem exists_heisenberg_constituent (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
    (S : Stratum 𝒪[F] F (Fin n → F)) (q : S.DefiningSequenceChoice)
    (θ : simpleHGroup S.chain S.n S.b q.tail 1 →* ℂˣ) (hθ : ContainsAutCharacter π θ) :
    ∃ X : Subrepresentation (autRestrict π (simpleJ S.chain S.n S.b q.tail)),
      FiniteDimensional ℂ X.toSubmodule ∧
      ∃ (dη : ℕ) (η : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) (Fin dη → ℂ)),
        IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η ∧
        ∃ P : η.IntertwiningMap (X.toRepresentation.comp
          (Subgroup.inclusion (simpleJGroup_one_le_simpleJ S.chain S.n S.b q.tail))), P ≠ 0 := by
  classical
  set J := simpleJ S.chain S.n S.b q.tail
  set τ := autRestrict π J
  obtain ⟨v, hv0, hvθ⟩ := hθ
  obtain ⟨K0, hK0⟩ := π.isSmooth v
  obtain ⟨m, hm⟩ := exists_unitFiltration_subset_nhds S.chain
    (K := (K0 : Set (GeneralLinear n F))) K0.mem_nhds_one
  rw [fixedVectors, Representation.mem_invariants] at hK0
  have hfix : ∀ j ∈ (S.chain.unitFiltration m).subgroupOf J, τ j v = v :=
    fun j hj => hK0 ⟨_, hm _ hj⟩
  have := unitFiltration_subgroupOf_normal S.chain
    (simpleJGroup_le_unitFiltration S.chain S.n S.b q.tail 0) m
  have : ((S.chain.unitFiltration m).subgroupOf J).FiniteIndex :=
    finiteIndex_unitFiltration_subgroupOf_simpleJGroup S.chain S.chain S.n S.b q.tail 0 m
  let X := FiniteVectors.orbitSubrepresentation τ v
  have hXfd : FiniteDimensional ℂ X.toSubmodule :=
    Clifford.finiteDimensional_orbitSpan_of_fixed τ _ hfix
  have hXK : ∀ k ∈ (S.chain.unitFiltration m).subgroupOf J, ∀ y ∈ X.toSubmodule, τ k y = y :=
    fun k hk y hy => Clifford.apply_eq_of_mem_orbitSpan τ _ hfix hy hk
  refine ⟨X, hXfd, ?_⟩
  set J1 := simpleJGroup S.chain S.n S.b q.tail 1
  let incl : J1 →* J := Subgroup.inclusion (simpleJGroup_one_le_simpleJ S.chain S.n S.b q.tail)
  let ρ1 : Representation ℂ J1 X.toSubmodule := X.toRepresentation.comp incl
  have := unitFiltration_subgroupOf_normal S.chain
    ((simpleJGroup_le_unitFiltration S.chain S.n S.b q.tail 1).trans
      (S.chain.unitFiltration_antitone (Nat.zero_le 1))) m
  have : ((S.chain.unitFiltration m).subgroupOf J1).FiniteIndex :=
    finiteIndex_unitFiltration_subgroupOf_simpleJGroup S.chain S.chain S.n S.b q.tail 1 m
  have hρ1K : ∀ k ∈ (S.chain.unitFiltration m).subgroupOf J1, ρ1 k = 1 := fun k hk =>
    LinearMap.ext fun y => Subtype.ext (hXK (incl k) hk y y.2)
  have hss : ρ1.IsSemisimpleRepresentation :=
    Clifford.isSemisimpleRepresentation_of_trivial_on_normal ρ1 _ hρ1K
  let ιH : simpleHGroup S.chain S.n S.b q.tail 1 →* J1 :=
    Subgroup.inclusion (simpleHGroup_le_simpleJGroup S.chain S.n S.b q.tail 1)
  let v' : X.toSubmodule := ⟨v, FiniteVectors.self_mem_orbitSpan τ v⟩
  have hv' : v' ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  obtain ⟨Y, hY, w, hwY, hw0, hwθ⟩ := Clifford.exists_isAtom_eigen ρ1 hss ιH θ hv'
    (fun h => Subtype.ext (hvθ h))
  let Yr := Y.toRepresentation
  let C := (Module.finBasis ℂ Y.toSubmodule).equivFun
  have hYirr : Yr.IsIrreducible :=
    FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom Y hY
  let w' : Y.toSubmodule := ⟨w, hwY⟩
  refine ⟨_, Clifford.coordinateRep Yr, ⟨inferInstance,
    ⟨S.chain, m, fun k hk => Clifford.coordinateRep_eq_one ?_⟩,
    Clifford.isIrreducible_of_equiv (Clifford.coordinateEquiv _) hYirr, ?_⟩, ?_⟩
  · exact LinearMap.ext fun y => Subtype.ext (LinearMap.congr_fun (hρ1K k hk) y)
  · refine ⟨⟨LinearMap.toSpanSingleton ℂ _ (C w'), fun h => ?_⟩, ?_⟩
    · apply LinearMap.ext
      intro c
      have hw' : Yr (ιH h) w' = (θ h : ℂ) • w' := Subtype.ext (hwθ h)
      have hC : C.symm (c • C w') = c • w' := by
        rw [LinearEquiv.symm_apply_eq, map_smul]
      change ((θ h : ℂ) • c) • C w' = C (Yr (ιH h) (C.symm (c • C w')))
      rw [hC, map_smul, hw']
      simp only [map_smul, smul_smul, smul_eq_mul, mul_comm]
    · intro h0
      have := LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap h0) 1
      change (1 : ℂ) • C w' = 0 at this
      rw [one_smul, LinearEquiv.map_eq_zero_iff] at this
      exact hw0 (congrArg Subtype.val this)
  · refine ⟨⟨Y.toSubmodule.subtype ∘ₗ C.symm.toLinearMap, fun g => ?_⟩, ?_⟩
    · apply LinearMap.ext
      intro x
      change ((C.symm (C (Yr g (C.symm x))) : Y.toSubmodule) : X.toSubmodule) =
        ρ1 g (C.symm x)
      rw [LinearEquiv.symm_apply_apply]
      rfl
    · intro h0
      have := LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap h0) (C w')
      change ((C.symm (C w') : Y.toSubmodule) : X.toSubmodule) = 0 at this
      rw [LinearEquiv.symm_apply_apply] at this
      exact hw0 this

/-- **`π` contains `κ ⊗ ξ` (BK93 p. 268).** If `π` contains a simple character `θ` of a simple
stratum with `r = 0`, and `β`-extensions exist, then there are a Heisenberg representation `η`
over `θ`, a `β`-extension `κ` of `η` and an irreducible representation `ξ` of `J(β, 𝔄)`,
trivial on `J^1(β, 𝔄)`, such that `π` contains `κ ⊗ ξ`. -/
theorem exists_beta_tensor_intertwining (hV2 : BetaExtensionStatement.{uF, uF, 0, 0, 0})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)) (S : Stratum 𝒪[F] F (Fin n → F))
    (hr : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (θ : simpleHGroup S.chain S.n S.b q.tail 1 →* ℂˣ)
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0) (hπθ : ContainsAutCharacter π θ) :
    ∃ (dη : ℕ) (η : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) (Fin dη → ℂ)),
      IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η ∧
    ∃ (dκ : ℕ) (κ : Representation ℂ (simpleJ S.chain S.n S.b q.tail) (Fin dκ → ℂ)),
      IsBetaExtension S.chain S.n S.b q.tail η κ ∧
    ∃ (dξ : ℕ) (ξ : Representation ℂ (simpleJ S.chain S.n S.b q.tail) (Fin dξ → ℂ)),
      ξ.IsIrreducible ∧
      (∀ j : simpleJ S.chain S.n S.b q.tail,
        (j : Aut) ∈ simpleJGroup S.chain S.n S.b q.tail 1 → ξ j = 1) ∧
      ∃ f : (κ.tprod ξ).IntertwiningMap (autRestrict π (simpleJ S.chain S.n S.b q.tail)),
        f ≠ 0 := by
  obtain ⟨X, hXfd, dη, η, hη, P, hP⟩ := exists_heisenberg_constituent π S q θ hπθ
  obtain ⟨⟨dκ, κ, hκ⟩, -⟩ := hV2 F (Fin n → F) ψF hψ S hr hS q θ hθ (Fin dη → ℂ) η hη
  obtain ⟨e⟩ := hκ.2.2.1
  have hle := simpleJGroup_one_le_simpleJ S.chain S.n S.b q.tail
  have : (Subgroup.inclusion hle).range.Normal := by
    rw [Subgroup.inclusion_range]
    exact simpleJGroup_one_subgroupOf_normal S hr hS q
  have := hXfd
  let P' := P.comp e.toIntertwiningMap
  have hP' : P' ≠ 0 := by
    intro h0
    apply hP
    refine Representation.IntertwiningMap.toLinearMap_injective _ _ (LinearMap.ext fun y => ?_)
    have h1 := congrArg (fun g => g (e.symm y)) h0
    simp only [P', Representation.IntertwiningMap.comp_apply,
      Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply] at h1
    simpa using h1
  obtain ⟨dξ, ξ, hξ, hξ1, -, F', hF'⟩ :=
    Clifford.exists_irreducible_tensor_intertwining (Subgroup.inclusion hle) κ X.toRepresentation
      P' hP'
  refine ⟨dη, η, hη, dκ, κ, hκ, dξ, ξ, hξ, fun j hj => hξ1 ⟨j, hj⟩,
    ⟨X.toSubmodule.subtype ∘ₗ F'.toLinearMap, fun g => ?_⟩, ?_⟩
  · apply LinearMap.ext
    intro x
    exact congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ F' g x)
  · intro h0
    apply hF'
    refine Representation.IntertwiningMap.toLinearMap_injective _ _ (LinearMap.ext fun x => ?_)
    have h1 := LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap h0) x
    exact Subtype.ext h1

end Heisenberg

section CuspidalData

variable {O : Type uG} {K : Type uH} {V : Type uW} [CommRing O] [IsLocalRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

/-- Every layer `L_i / L_{i+1}` of a lattice chain is a finite-dimensional space over the residue
field. -/
theorem LatticeChain.finite_layer (L : LatticeChain O K V) (i : ℤ) :
    Module.Finite (ResidueField O) (L.Layer i) := by
  have : Module.Finite O (L.lattice i) := Module.Finite.iff_fg.mpr (L.fg_lattice i)
  exact Module.Finite.of_restrictScalars_finite O _ _

/-- The cuspidal layer data given by bases of the layers and irreducible cuspidal classes of
the layer groups, with the factors realized in coordinates. -/
def LatticeChain.classCuspidalData (L : LatticeChain O K V) {d : Fin L.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField O) (L.Layer (i : ℕ)))
    [∀ i, Fintype (GeneralLinear (d i) (ResidueField O))]
    (a : ∀ i, FiniteRep.IrreducibleClass (GeneralLinear (d i) (ResidueField O)))
    (hcusp : ∀ i, FiniteGeneralLinear.IsCuspidal (FiniteRep.VirtualCharacter.rep (a i)).ρ) :
    L.CuspidalLayerData where
  rank := d
  dim i := finrank ℂ (FiniteRep.VirtualCharacter.rep (a i))
  basis := b
  factor i := Clifford.coordinateRep (FiniteRep.VirtualCharacter.rep (a i)).ρ
  cuspidal i := ⟨isIrreducible_coordinateRep_rep (a i),
    (hcusp i).of_equiv (Clifford.coordinateEquiv _)⟩

/-- The inflation of `classCuspidalData` is the inflation of `classTensor` along the layer
reduction. -/
theorem LatticeChain.classCuspidalData_inflation (L : LatticeChain O K V)
    {d : Fin L.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField O) (L.Layer (i : ℕ)))
    [∀ i, Fintype (GeneralLinear (d i) (ResidueField O))]
    (a : ∀ i, FiniteRep.IrreducibleClass (GeneralLinear (d i) (ResidueField O)))
    (hcusp : ∀ i, FiniteGeneralLinear.IsCuspidal (FiniteRep.VirtualCharacter.rep (a i)).ρ) :
    (L.classCuspidalData b a hcusp).inflation = (classTensor a).comp (L.layerReduction b) :=
  rfl

end CuspidalData

section LayerTransport

variable {O : Type uG} {K : Type uH} {F : Type uF} {V : Type uW} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field K] [Algebra O K] [Field F]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [Module F V]

/-- Let `U` be a group of `F`-linear automorphisms of `V` preserving the lattices of `L`, and
`ε : U → U(𝔄)` a homomorphism such that `ε(u)` acts on `V` as `u` does. Then the layer reduction
of `U(𝔄)`, composed with `ε`, is a layer reduction of `U` in the same bases. -/
theorem LatticeChain.isLayerReduction_comp (L : LatticeChain O K V)
    (U : Subgroup (Module.End F V)ˣ)
    (hU : ∀ u ∈ U, ∀ (i : ℤ) (v : V), v ∈ L.lattice i → (u : Module.End F V) v ∈ L.lattice i)
    {r : ℕ}
    (b : ∀ i : Fin L.period, Module.Basis (Fin r) (ResidueField O) (L.Layer ((i : ℕ) : ℤ)))
    (ε : U →* L.unitFiltration 0)
    (hε : ∀ (u : U) (v : V), ((ε u : (Module.End K V)ˣ) : Module.End K V) v =
      ((u : (Module.End F V)ˣ) : Module.End F V) v) :
    IsLayerReduction L U hU b ((L.layerReduction b).comp ε) := by
  intro u i v hv
  have key := L.equivFun_layerReduction b (ε u) i v hv
  have h1 : L.intervalMk ((i : ℕ) : ℤ) ((i : ℕ) + 1 : ℤ)
      (((u : (Module.End F V)ˣ) : Module.End F V) v) (hU u u.2 _ v hv) =
      L.intervalMk ((i : ℕ) : ℤ) ((i : ℕ) + 1 : ℤ)
        (((ε u : (Module.End K V)ˣ) : Module.End K V) v) (L.mem_order.mp (ε u).2.1 _ _ hv) := by
    congr 1
    exact (hε u v).symm
  exact (congrArg (b i).equivFun h1).trans key

end LayerTransport

section Smooth

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

local notation "Aut" => (Module.End F (Fin n → F))ˣ

/-- A tensor product of smooth representations is smooth. -/
theorem isSmoothRepresentation_tprod {J : Subgroup Aut} {W₁ : Type uW} {W₂ : Type uH}
    [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    {ρ₁ : Representation ℂ J W₁} {ρ₂ : Representation ℂ J W₂}
    (h₁ : IsSmoothRepresentation ρ₁) (h₂ : IsSmoothRepresentation ρ₂) :
    IsSmoothRepresentation (ρ₁.tprod ρ₂) := by
  obtain ⟨L₁, m₁, h₁⟩ := h₁
  obtain ⟨L₂, m₂, h₂⟩ := h₂
  obtain ⟨k, hk⟩ := exists_unitFiltration_le_unitFiltration L₁ L₂ m₂
  refine ⟨L₁, max m₁ k, fun j hj => ?_⟩
  rw [Representation.tprod_apply, h₁ j (L₁.unitFiltration_antitone (le_max_left _ _) hj),
    h₂ j (hk (L₁.unitFiltration_antitone (le_max_right _ _) hj))]
  exact TensorProduct.map_one

end Smooth

end Langlands.BushnellKutzko

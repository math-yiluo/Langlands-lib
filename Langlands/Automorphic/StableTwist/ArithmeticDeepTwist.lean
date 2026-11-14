import Langlands.Automorphic.ArithmeticStableTwistGammaStatement
import Langlands.Correspondence.SupercuspidalGammaCompatibility
import Langlands.Correspondence.LowerRankWeilFactor
import Langlands.Correspondence.RankOneEpsilonCharacterTransport
import Langlands.Correspondence.ArithmeticEpsilonDirectSum
import Langlands.Global.Factors.RelativeWeilLocalEpsilon
import Langlands.Weil.Representation.RankDeterminantProof
import Langlands.LocalFactor.DeligneHenniartVirtualStabilityProof
import Langlands.LocalFactor.DeligneHenniartDimensionOne
import Langlands.LocalFactor.BrauerKernel.StandaloneBridge
import Langlands.LocalFactor.NonabelianDualityReduction

/-! # Algebra of highly ramified twists of Weil–Deligne pairs

Linear-algebra and pair-level facts used for arithmetic gamma factors after a highly
ramified twist: scalar actions, vanishing invariants, trivial L-ratios and quotient
corrections, and transport of a pair to another carrier universe.
-/

noncomputable section

universe u uV uE uK uG uW

namespace Langlands.ArithmeticStableTwist

open Weil.Local

section Algebra

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- A scalar action of `g` is carried by any equivalence of representations. -/
theorem representation_eq_smul_of_equiv {A : FiniteRepresentation.{uK, uG, uV} K G}
    {B : FiniteRepresentation.{uK, uG, uW} K G} (f : FiniteRepresentation.Equiv A B)
    {g : G} {c : K} (h : A.representation g = c • 1) : B.representation g = c • 1 := by
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := f.toLinearEquiv.surjective v
  have hf : f (A.representation g w) = B.representation g (f w) :=
    Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap g w
  change B.representation g (f w) = (c • (1 : Module.End K B)) (f w)
  rw [← hf, h, LinearMap.smul_apply, Module.End.one_apply, map_smul]
  rfl

/-- If some `g` in `I` acts by a scalar different from one, there are no nonzero
`I`-invariant vectors. -/
theorem invariantSubspace_eq_bot_of_smul (A : FiniteRepresentation.{uK, uG, uV} K G)
    (I : Subgroup G) {g : G} (hg : g ∈ I) {c : K} (hc : c ≠ 1)
    (h : A.representation g = c • 1) :
    FiniteRepresentation.invariantSubspace A I = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have hv' : A.representation g v = v := hv ⟨g, hg⟩
  rw [h, LinearMap.smul_apply, Module.End.one_apply] at hv'
  have h1 : (c - 1) • v = 0 := by rw [sub_smul, hv', one_smul, sub_self]
  rw [Submodule.mem_bot]
  exact (smul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hc)

/-- The tensor product of a scalar action with the identity is that scalar. -/
theorem tensor_representation_eq_smul (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) {g : G} {c : K}
    (hA : A.representation g = c • 1) (hB : B.representation g = 1) :
    (FiniteRepresentation.tensor A B).representation g = c • 1 := by
  change TensorProduct.map (A.representation g) (B.representation g) = c • 1
  rw [hA, hB, TensorProduct.map_smul_left]
  congr 1
  exact TensorProduct.map_one

/-- A twist of a representation on which `g` acts trivially acts by the character value. -/
theorem twist_representation_eq_smul (χ : G →* Kˣ) (A : FiniteRepresentation.{uK, uG, uV} K G)
    {g : G} (h : A.representation g = 1) :
    (FiniteRepresentation.twist χ A).representation g = (χ g : K) • 1 := by
  change (χ g : K) • A.representation g = _
  rw [h]
  rfl

/-- If `g` acts by `c` then `g⁻¹` acts on the contragredient by `c`. -/
theorem dual_representation_eq_smul (A : FiniteRepresentation.{uK, uG, uV} K G)
    {g : G} {c : K} (h : A.representation g⁻¹ = c • 1) :
    (FiniteRepresentation.dual A).representation g = c • 1 := by
  apply LinearMap.ext
  intro ℓ
  change (ℓ : Module.Dual K A) ∘ₗ A.representation g⁻¹ = c • (ℓ : Module.Dual K A)
  rw [h]
  apply LinearMap.ext
  intro v
  exact map_smul (show Module.Dual K A.obj from ℓ) c v

end Algebra

section Transport

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

/-- Conjugation by a linear equivalence, as an algebra equivalence of endomorphisms. -/
def conjAlgEquiv {V : Type uV} {W : Type uW} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (f : V ≃ₗ[K] W) : Module.End K V ≃ₐ[K] Module.End K W :=
  AlgEquiv.ofLinearEquiv f.conj (by
    change f.conj LinearMap.id = LinearMap.id
    rw [LinearEquiv.conj_id]) (fun x y => by
    change f.conj (x ∘ₗ y) = f.conj x ∘ₗ f.conj y
    rw [LinearEquiv.conj_comp])

theorem conjAlgEquiv_apply {V : Type uV} {W : Type uW} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V ≃ₗ[K] W) (x : Module.End K V) :
    conjAlgEquiv f x = f.toLinearMap ∘ₗ x ∘ₗ f.symm.toLinearMap := by
  change f.conj x = _
  rw [LinearEquiv.conj_apply, LinearMap.comp_assoc]

/-- A Weil–Deligne pair moved along a representation equivalence of its Weil part:
the new carrier with the conjugated monodromy. -/
def transportPair (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : FiniteRepresentation.{uK, uG, uW} K G)
    (f : FiniteRepresentation.Equiv A.toFiniteRepresentation B) :
    WeilDeligneRepresentation.{uK, uG, uW} K G ν where
  toFiniteRepresentation := B
  monodromy := conjAlgEquiv f.toLinearEquiv A.monodromy
  nilpotent := A.nilpotent.map (conjAlgEquiv f.toLinearEquiv)
  covariance g := by
    have hg : ∀ h : G, conjAlgEquiv f.toLinearEquiv (A.representation h) =
        B.representation h := by
      intro h
      rw [conjAlgEquiv_apply]
      apply LinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := f.toLinearEquiv.surjective v
      change f (A.representation h (f.toLinearEquiv.symm (f.toLinearEquiv w))) = _
      rw [LinearEquiv.symm_apply_apply]
      exact Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap h w
    rw [← hg g, ← hg g⁻¹, ← map_mul, ← map_mul, A.covariance g, map_smul]

/-- The original pair is equivalent to its transport. -/
def transportPairEquiv (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : FiniteRepresentation.{uK, uG, uW} K G)
    (f : FiniteRepresentation.Equiv A.toFiniteRepresentation B) :
    WeilDeligneRepresentation.Equiv A (transportPair A B f) where
  representationEquiv := f
  comm_monodromy := by
    change f.toLinearMap ∘ₗ A.monodromy = conjAlgEquiv f.toLinearEquiv A.monodromy ∘ₗ f.toLinearMap
    rw [conjAlgEquiv_apply]
    apply LinearMap.ext
    intro v
    change f (A.monodromy v) = f (A.monodromy (f.toLinearEquiv.symm (f.toLinearEquiv v)))
    rw [LinearEquiv.symm_apply_apply]

/-- Restriction of a twisted tensor product: the identity map identifies the tensor of the
restricted twist with the twist of the restricted tensor. -/
def restrictTwistTensorEquiv {H : Type uW} [Group H] (φ : H →* G) (χ : G →* Kˣ)
    (A : FiniteRepresentation.{uK, uG, uV} K G) (B : FiniteRepresentation.{uK, uG, uV} K G) :
    FiniteRepresentation.Equiv
      (FiniteRepresentation.tensor (FiniteRepresentation.restrict φ (FiniteRepresentation.twist χ A))
        (FiniteRepresentation.restrict φ B))
      (FiniteRepresentation.twist (χ.comp φ)
        (FiniteRepresentation.restrict φ (FiniteRepresentation.tensor A B))) where
  toLinearEquiv := LinearEquiv.refl K _
  isIntertwining' h := by
    apply TensorProduct.ext'
    intro x y
    change ((χ (φ h) : K) • A.representation (φ h) x) ⊗ₜ[K] B.representation (φ h) y =
      (χ (φ h) : K) • (A.representation (φ h) x ⊗ₜ[K] B.representation (φ h) y)
    rw [TensorProduct.smul_tmul']

/-- Two twists commute; the underlying map is the identity. -/
def twistCommEquiv (χ η : G →* Kˣ) (A : FiniteRepresentation.{uK, uG, uV} K G) :
    FiniteRepresentation.Equiv (FiniteRepresentation.twist χ (FiniteRepresentation.twist η A))
      (FiniteRepresentation.twist η (FiniteRepresentation.twist χ A)) where
  toLinearEquiv := LinearEquiv.refl K _
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    change (χ h : K) • (η h : K) • A.representation h x = (η h : K) • (χ h : K) • A.representation h x
    rw [smul_comm]

end Transport

end Langlands.ArithmeticStableTwist

namespace Langlands.ArithmeticStableTwist

open Weil.Local LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne
open Correspondence VirtualRepresentation

section BasePair

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

/-- The literal inclusion of the bottom fixing subgroup, as a continuous homomorphism. -/
def baseInclusion : weilSubgroup K (baseExtension K) →ₜ* localWeilGroup K where
  toMonoidHom := (weilSubgroup K (baseExtension K)).subtype
  continuous_toFun := continuous_subtype_val

/-- The bottom-field pair of a local pair: its restriction, moved to the carrier universe
of a common-closure system. -/
def basePair (B : LocalWeilDeligneRepresentation.{u, uV} K) : Pair.{u, uE} K (baseExtension K) :=
  transportPair (WeilDeligneRepresentation.restrict (weilSubgroup K (baseExtension K)).subtype B)
    (FiniteRepresentation.universeModel _) (FiniteRepresentation.universeModelEquiv _)

theorem isBaseRestriction_basePair (B : LocalWeilDeligneRepresentation.{u, uV} K) :
    IsBaseRestriction K (WeilDeligneRepresentation.classOf B) (basePair.{u, uV, uE} K B) :=
  ⟨B, rfl, ⟨transportPairEquiv _ _ _⟩⟩

theorem basePair_isContinuous {B : LocalWeilDeligneRepresentation.{u, uV} K}
    (hB : B.toFiniteRepresentation.IsContinuous) :
    (basePair.{u, uV, uE} K B).toFiniteRepresentation.IsContinuous :=
  (FiniteRepresentation.isContinuous_iff_of_equiv
    (FiniteRepresentation.universeModelEquiv _)).mp
    (FiniteRepresentation.isContinuous_restrict _ continuous_subtype_val hB)

/-- The bottom-field restriction of `B ⊗ B'`, in the carrier universe of the system. -/
def tensorBaseRep (B B' : LocalWeilDeligneRepresentation.{u, uV} K) :
    FiniteRepresentation.{0, u, max u uE} ℂ (weilSubgroup K (baseExtension K)) :=
  FiniteRepresentation.restrict (baseInclusion K).toMonoidHom
    (FiniteRepresentation.universeModel
      (FiniteRepresentation.tensor B.toFiniteRepresentation B'.toFiniteRepresentation))

theorem tensorBaseRep_isContinuous {B B' : LocalWeilDeligneRepresentation.{u, uV} K}
    (hB : B.toFiniteRepresentation.IsContinuous) (hB' : B'.toFiniteRepresentation.IsContinuous) :
    (tensorBaseRep.{u, uV, uE} K B B').IsContinuous :=
  FiniteRepresentation.isContinuous_restrict _ (baseInclusion K).continuous
    ((FiniteRepresentation.isContinuous_iff_of_equiv
      (FiniteRepresentation.universeModelEquiv _)).mp
      (FiniteRepresentation.isContinuous_tensor hB hB'))

/-- Bottom-field data of a twisted first factor and a second factor: their tensor product
is the restricted twist of `tensorBaseRep`. -/
def tensorTwistEquiv (χ : localWeilGroup K →ₜ* ℂˣ) (B B' : LocalWeilDeligneRepresentation.{u, uV} K)
    {P P' : Pair.{u, uE} K (baseExtension K)}
    (fP : WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.restrict
      (weilSubgroup K (baseExtension K)).subtype (WeilDeligneRepresentation.twist χ.toMonoidHom B)) P)
    (fP' : WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.restrict
      (weilSubgroup K (baseExtension K)).subtype B') P') :
    FiniteRepresentation.Equiv (WeilDeligneRepresentation.tensor P P').toFiniteRepresentation
      (FiniteRepresentation.twist (χ.comp (baseInclusion K)).toMonoidHom
        (tensorBaseRep.{u, uV, uE} K B B')) :=
  (FiniteRepresentation.tensorEquivOfEquiv fP.representationEquiv.symm
    fP'.representationEquiv.symm).trans
    ((restrictTwistTensorEquiv (baseInclusion K).toMonoidHom χ.toMonoidHom
      B.toFiniteRepresentation B'.toFiniteRepresentation).trans
      (FiniteRepresentation.twistEquiv _
        (FiniteRepresentation.restrictEquivOfEquiv _ (FiniteRepresentation.universeModelEquiv _))))

end BasePair

section UniverseModel

variable {G : Type uG} [Group G]

theorem determinantCharacter_universeModel (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    FiniteRepresentation.determinantCharacter
        (FiniteRepresentation.universeModel A : FiniteRepresentation.{0, uG, uW} ℂ G) =
      FiniteRepresentation.determinantCharacter A :=
  (FiniteRepresentation.determinantCharacter_eq (FiniteRepresentation.universeModelEquiv A)).symm

theorem rank_universeModel (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    (FiniteRepresentation.universeModel A : FiniteRepresentation.{0, uG, uW} ℂ G).rank = A.rank :=
  (FiniteRepresentation.rank_eq_of_equiv (FiniteRepresentation.universeModelEquiv A)).symm

theorem representation_universeModel_eq_one (A : FiniteRepresentation.{0, uG, uV} ℂ G) {g : G}
    (h : A.representation g = 1) :
    (FiniteRepresentation.universeModel A : FiniteRepresentation.{0, uG, uW} ℂ G).representation g
      = 1 := by
  have h1 : A.representation g = (1 : ℂ) • 1 := by rw [one_smul]; exact h
  rw [representation_eq_smul_of_equiv (FiniteRepresentation.universeModelEquiv A) h1, one_smul]

end UniverseModel

section Inertia

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

/-- Every element of the local Weil group lies in the bottom fixing subgroup. -/
theorem mem_baseWeil (w : localWeilGroup K) : w ∈ weilSubgroup K (baseExtension K) := by
  have h : weilSubgroup K (NonabelianSystem.DeligneHenniart.baseExtension K) = ⊤ :=
    NonabelianSystem.DeligneHenniart.baseWeil_eq_top K
  change w ∈ weilSubgroup K (NonabelianSystem.DeligneHenniart.baseExtension K)
  rw [h]
  exact Subgroup.mem_top w

/-- Upper ramification groups of nonnegative index lie in inertia. -/
theorem upperGroup_le_localInertia {r : ℝ} (hr : 0 ≤ r) :
    LocalWeil.Ramification.upperGroup K r ≤ localInertia K := by
  intro w hw
  have h0 : w ∈ LocalWeil.Ramification.upperGroup K 0 :=
    LocalWeil.Ramification.upperGroup_antitone K hr hw
  rw [localInertia_eq_comap]
  change localProjection K w ∈ K.absoluteInertia K.canonicalTopologicalData
  rw [← Ramification.HerbrandBridge.absoluteUpperInertia K K.canonicalTopologicalData]
  exact h0

/-- Four continuous representations are trivial on one common upper ramification group. -/
theorem exists_common_threshold
    {A₁ A₂ A₃ A₄ : FiniteRepresentation.{0, u, uV} ℂ (localWeilGroup K)}
    (h₁ : A₁.IsContinuous) (h₂ : A₂.IsContinuous) (h₃ : A₃.IsContinuous)
    (h₄ : A₄.IsContinuous) :
    ∃ s : ℝ, 0 ≤ s ∧ ∀ w ∈ LocalWeil.Ramification.upperGroup K s,
      A₁.representation w = 1 ∧ A₂.representation w = 1 ∧ A₃.representation w = 1 ∧
        A₄.representation w = 1 := by
  obtain ⟨r₁, hr₁⟩ := Ramification.HerbrandBridge.weilTrivialityThresholdsNonempty K A₁ h₁
  obtain ⟨r₂, hr₂⟩ := Ramification.HerbrandBridge.weilTrivialityThresholdsNonempty K A₂ h₂
  obtain ⟨r₃, hr₃⟩ := Ramification.HerbrandBridge.weilTrivialityThresholdsNonempty K A₃ h₃
  obtain ⟨r₄, hr₄⟩ := Ramification.HerbrandBridge.weilTrivialityThresholdsNonempty K A₄ h₄
  refine ⟨max (max r₁ r₂) (max r₃ r₄), le_max_of_le_left (le_max_of_le_left hr₁.1),
    fun w hw => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact hr₁.2 w (LocalWeil.Ramification.upperGroup_antitone K
      (le_max_of_le_left (le_max_left _ _)) hw)
  · exact hr₂.2 w (LocalWeil.Ramification.upperGroup_antitone K
      (le_max_of_le_left (le_max_right _ _)) hw)
  · exact hr₃.2 w (LocalWeil.Ramification.upperGroup_antitone K
      (le_max_of_le_right (le_max_left _ _)) hw)
  · exact hr₄.2 w (LocalWeil.Ramification.upperGroup_antitone K
      (le_max_of_le_right (le_max_right _ _)) hw)

/-- The L-ratio of `(B ⊗ χ) ⊗ B'` is one when some inertia element acts trivially on
`B`, `B'` and its inverse, while `χ` is nontrivial on it. -/
theorem rationalLRatio_twist_tensor_eq_one (χ : localWeilGroup K →ₜ* ℂˣ)
    (B B' : LocalWeilDeligneRepresentation.{u, uV} K) {w : localWeilGroup K}
    (hwI : w ∈ localInertia K) (hB : B.representation w = 1) (hB' : B'.representation w = 1)
    (hBi : B.representation w⁻¹ = 1) (hB'i : B'.representation w⁻¹ = 1) (hχ : χ w ≠ 1)
    (g : localWeilGroup K) (c : ℂˣ) :
    LocalFactor.WeilDeligne.rationalLRatio (WeilDeligneRepresentation.tensor
      (WeilDeligneRepresentation.twist χ.toMonoidHom B) B') (localInertia K) g c = 1 := by
  have h1 : (FiniteRepresentation.tensor
      (FiniteRepresentation.twist χ.toMonoidHom B.toFiniteRepresentation)
      B'.toFiniteRepresentation).representation w = (χ w : ℂ) • 1 :=
    tensor_representation_eq_smul _ _ (twist_representation_eq_smul _ _ hB) hB'
  have h2 : (FiniteRepresentation.tensor
      (FiniteRepresentation.twist χ.toMonoidHom B.toFiniteRepresentation)
      B'.toFiniteRepresentation).representation w⁻¹ = (χ w⁻¹ : ℂ) • 1 :=
    tensor_representation_eq_smul _ _ (twist_representation_eq_smul _ _ hBi) hB'i
  have hne : ∀ x : localWeilGroup K, χ x ≠ 1 → (χ x : ℂ) ≠ 1 :=
    fun x hx h => hx (Units.ext h)
  have hinv : χ w⁻¹ ≠ 1 := by
    rw [map_inv]
    exact inv_ne_one.mpr hχ
  rw [LocalFactor.WeilDeligne.rationalLRatio_eq,
    eulerPolynomial_eq_one_of_invariantSubspace_eq_bot K
      (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.twist χ.toMonoidHom B) B')
      (invariantSubspace_eq_bot_of_smul _ _ hwI (hne w hχ) h1),
    eulerPolynomial_eq_one_of_invariantSubspace_eq_bot K
      (WeilDeligneRepresentation.dual
        (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.twist χ.toMonoidHom B) B'))
      (invariantSubspace_eq_bot_of_smul _ _ hwI (hne _ hinv) (dual_representation_eq_smul _ h2))]
  simp

end Inertia

section Quotient

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

/-- A pair without inertia invariants has trivial quotient correction. -/
theorem quotientValue_eq_one {E : Extension K} (A : Pair.{u, uE} K E)
    (hA : FiniteRepresentation.invariantSubspace A.toFiniteRepresentation (inertia K E) = ⊥)
    (Φ : GeometricFrobenius K E) (s : ℂ) : quotientValue K E A Φ s = 1 := by
  apply Units.ext
  rw [quotientValue_det, Units.val_one]
  have : Subsingleton (LocalFactor.WeilDeligne.inertiaRepresentation A (inertia K E)) :=
    ⟨fun x y => by
      apply Subtype.ext
      have hx := x.property
      have hy := y.property
      change x.val ∈ FiniteRepresentation.invariantSubspace A.toFiniteRepresentation
        (inertia K E) at hx
      change y.val ∈ FiniteRepresentation.invariantSubspace A.toFiniteRepresentation
        (inertia K E) at hy
      rw [hA, Submodule.mem_bot] at hx hy
      rw [hx, hy]⟩
  have : Subsingleton (LocalFactor.WeilDeligne.quotientRepresentation A (inertia K E)) :=
    (Submodule.mkQ_surjective (LocalFactor.WeilDeligne.kernelInInvariants A (inertia K E))).subsingleton
  exact LinearMap.det_eq_one_of_subsingleton _

/-- The bottom-field tensor of a twisted first factor has no inertia invariants when some
inertia element acts trivially on both factors and nontrivially through the character. -/
theorem invariantSubspace_tensor_eq_bot (χ : localWeilGroup K →ₜ* ℂˣ)
    {B B' : LocalWeilDeligneRepresentation.{u, uV} K} {P P' : Pair.{u, uE} K (baseExtension K)}
    (fP : WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.restrict
      (weilSubgroup K (baseExtension K)).subtype (WeilDeligneRepresentation.twist χ.toMonoidHom B)) P)
    (fP' : WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.restrict
      (weilSubgroup K (baseExtension K)).subtype B') P')
    {w : localWeilGroup K} (hwI : w ∈ localInertia K) (hB : B.representation w = 1)
    (hB' : B'.representation w = 1) (hχ : χ w ≠ 1) :
    FiniteRepresentation.invariantSubspace
      (WeilDeligneRepresentation.tensor P P').toFiniteRepresentation
      (inertia K (baseExtension K)) = ⊥ := by
  have hmem : w ∈ weilSubgroup K (baseExtension K) := mem_baseWeil K w
  have h1 : (FiniteRepresentation.tensor
      (FiniteRepresentation.restrict (weilSubgroup K (baseExtension K)).subtype
        (FiniteRepresentation.twist χ.toMonoidHom B.toFiniteRepresentation))
      (FiniteRepresentation.restrict (weilSubgroup K (baseExtension K)).subtype
        B'.toFiniteRepresentation)).representation ⟨w, hmem⟩ = (χ w : ℂ) • 1 :=
    tensor_representation_eq_smul _ _
      (twist_representation_eq_smul χ.toMonoidHom B.toFiniteRepresentation hB) hB'
  have h2 := representation_eq_smul_of_equiv
    (FiniteRepresentation.tensorEquivOfEquiv fP.representationEquiv fP'.representationEquiv) h1
  exact invariantSubspace_eq_bot_of_smul _ _ (g := ⟨w, hmem⟩) hwI
    (fun h => hχ (Units.ext h)) h2

end Quotient

section DeepTwist

open LocalFactor.NonabelianSystem

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

/-- Equal-rank, equal-determinant representations trivial on `N` have equal epsilon values
after twisting by a character with an exact witness relative to `N`. -/
theorem value_twist_eq_of_witness {e : ReciprocityFamily K} {ε : Assignment.{u, uE} K}
    (hε : AdditiveRelation K ε) {E : Extension K} {N : Subgroup (weilSubgroup K E)}
    {ψ : AdditiveCharacter K E} {χ : weilSubgroup K E →ₜ* ℂˣ} {γ : E.fieldˣ}
    (hw : DeligneHenniart.ExactWitnessOn K e ε E N ψ
      (ExactGrothendieckGroup.characterClass χ) γ)
    {R R₀ : FiniteRepresentation.{0, u, max u uE} ℂ (weilSubgroup K E)}
    (hR : R.IsContinuous) (hR₀ : R₀.IsContinuous)
    (hN : ∀ n ∈ N, R.representation n = 1) (hN₀ : ∀ n ∈ N, R₀.representation n = 1)
    (hrank : R.rank = R₀.rank)
    (hdet : FiniteRepresentation.determinantCharacter R =
      FiniteRepresentation.determinantCharacter R₀)
    (μ : HaarMeasure K E) :
    ε E ψ μ (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{u, uE} K E)
        ⟨FiniteRepresentation.twist χ.toMonoidHom R,
          FiniteRepresentation.isContinuous_twist χ hR⟩) =
      ε E ψ μ (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{u, uE} K E)
        ⟨FiniteRepresentation.twist χ.toMonoidHom R₀,
          FiniteRepresentation.isContinuous_twist χ hR₀⟩) := by
  obtain ⟨x, hx⟩ : ∃ x, x = ExactGrothendieckGroup.ofRepresentation
      (ContinuousPredicate.{u, uE} K E) ⟨R, hR⟩ := ⟨_, rfl⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = ExactGrothendieckGroup.ofRepresentation
      (ContinuousPredicate.{u, uE} K E) ⟨R₀, hR₀⟩ := ⟨_, rfl⟩
  have hspan : x - x₀ ∈ weilTrivialOnSpan.{u, uE} K E N :=
    Submodule.sub_mem _ (Submodule.subset_span ⟨R, hR, hN, hx⟩)
      (Submodule.subset_span ⟨R₀, hR₀, hN₀, hx₀⟩)
  have hdeg : x - x₀ ∈ DegreeZero.{u, uE} K E := by
    rw [ExactGrothendieckGroup.mem_degreeZero, map_sub, hx, hx₀,
      ExactGrothendieckGroup.degree_ofRepresentation,
      ExactGrothendieckGroup.degree_ofRepresentation]
    change ((R.rank : ℤ) - (R₀.rank : ℤ)) = 0
    rw [hrank, sub_self]
  have hfd : DeligneHenniart.fieldDeterminant K e E (x - x₀) γ = 1 := by
    have hadd := DeligneHenniart.fieldDeterminant_add_apply K e E (x - x₀) x₀ γ
    rw [sub_add_cancel] at hadd
    have heq : DeligneHenniart.fieldDeterminant K e E x γ =
        DeligneHenniart.fieldDeterminant K e E x₀ γ := by
      obtain ⟨g, rfl⟩ := CommonClosure.reciprocityUnits_surjective K e E γ
      rw [DeligneHenniart.fieldDeterminant_reciprocityUnits,
        DeligneHenniart.fieldDeterminant_reciprocityUnits, hx, hx₀,
        ExactGrothendieckGroup.determinantCharacter_ofRepresentation,
        ExactGrothendieckGroup.determinantCharacter_ofRepresentation]
      exact DFunLike.congr_fun hdet g
    rw [heq] at hadd
    exact mul_right_cancel (hadd.symm.trans (one_mul _).symm)
  have h := hw (x - x₀) hspan hdeg μ
  rw [hfd, ExactGrothendieckGroup.continuousTensor_characterClass, map_sub,
    DeligneHenniart.value_sub K hε, hx, hx₀,
    ExactGrothendieckGroup.continuousTwist_ofRepresentation,
    ExactGrothendieckGroup.continuousTwist_ofRepresentation] at h
  exact mul_inv_eq_one.mp h

/-- The Deligne value of a twisted class is the epsilon value of the spectral twist,
written with the two twists in the other order. -/
theorem conditionalDeligneValue_ofRepresentation_twist {e : ReciprocityFamily K}
    {ε : Assignment.{u, uE} K} (hε : IsSystem K e ε) {E : Extension K}
    (ψ : AdditiveCharacter K E) (μ : HaarMeasure K E) (χ : weilSubgroup K E →ₜ* ℂˣ)
    (R : FiniteRepresentation.{0, u, max u uE} ℂ (weilSubgroup K E)) (hR : R.IsContinuous)
    (s : ℂ) :
    CommonClosureSpectral.conditionalDeligneValue K e ε hε E ψ μ
        (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{u, uE} K E)
          ⟨FiniteRepresentation.twist χ.toMonoidHom R,
            FiniteRepresentation.isContinuous_twist χ hR⟩) s =
      ε E ψ μ (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{u, uE} K E)
        ⟨FiniteRepresentation.twist χ.toMonoidHom
            (FiniteRepresentation.twist (CommonClosureSpectral.character K E s).toMonoidHom R),
          FiniteRepresentation.isContinuous_twist χ
            (FiniteRepresentation.isContinuous_twist (CommonClosureSpectral.character K E s)
              hR)⟩) := by
  change ε E ψ μ (ExactGrothendieckGroup.continuousTwist (CommonClosureSpectral.character K E s)
    (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{u, uE} K E)
      ⟨FiniteRepresentation.twist χ.toMonoidHom R,
        FiniteRepresentation.isContinuous_twist χ hR⟩)) = _
  rw [ExactGrothendieckGroup.continuousTwist_ofRepresentation]
  exact congrArg (ε E ψ μ)
    (ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _ (twistCommEquiv _ _ _))

/-- Deligne values of deep twists of two equal-rank, equal-determinant representations
trivial on `N ≤ I_E` agree, given an exact witness of the twisting character on `N`. -/
theorem conditionalDeligneValue_twist_eq {e : ReciprocityFamily K} {ε : Assignment.{u, uE} K}
    (hε : IsSystem K e ε) {E : Extension K} {N : Subgroup (weilSubgroup K E)}
    (hNI : N ≤ inertia K E) {ψ : AdditiveCharacter K E} {χ : weilSubgroup K E →ₜ* ℂˣ}
    {γ : E.fieldˣ}
    (hw : DeligneHenniart.ExactWitnessOn K e ε E N ψ
      (ExactGrothendieckGroup.characterClass χ) γ)
    {T T₀ : FiniteRepresentation.{0, u, max u uE} ℂ (weilSubgroup K E)}
    (hT : T.IsContinuous) (hT₀ : T₀.IsContinuous)
    (hN : ∀ n ∈ N, T.representation n = 1) (hN₀ : ∀ n ∈ N, T₀.representation n = 1)
    (hrank : T.rank = T₀.rank)
    (hdet : FiniteRepresentation.determinantCharacter T =
      FiniteRepresentation.determinantCharacter T₀)
    (μ : HaarMeasure K E) (s : ℂ) :
    CommonClosureSpectral.conditionalDeligneValue K e ε hε E ψ μ
        (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{u, uE} K E)
          ⟨FiniteRepresentation.twist χ.toMonoidHom T,
            FiniteRepresentation.isContinuous_twist χ hT⟩) s =
      CommonClosureSpectral.conditionalDeligneValue K e ε hε E ψ μ
        (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{u, uE} K E)
          ⟨FiniteRepresentation.twist χ.toMonoidHom T₀,
            FiniteRepresentation.isContinuous_twist χ hT₀⟩) s := by
  have hc : ∀ n ∈ N, CommonClosureSpectral.character K E s n = 1 := fun n hn =>
    SpectralTwist.character_on_kernel _ _ _ s (hNI hn)
  have htw : ∀ (R : FiniteRepresentation.{0, u, max u uE} ℂ (weilSubgroup K E)),
      (∀ n ∈ N, R.representation n = 1) → ∀ n ∈ N,
        (FiniteRepresentation.twist (CommonClosureSpectral.character K E s).toMonoidHom
          R).representation n = 1 := by
    intro R hR n hn
    rw [twist_representation_eq_smul _ R (hR n hn)]
    change ((CommonClosureSpectral.character K E s n : ℂˣ) : ℂ) • (1 : Module.End ℂ R) = 1
    rw [hc n hn, Units.val_one, one_smul]
  rw [conditionalDeligneValue_ofRepresentation_twist K hε ψ μ χ T hT s,
    conditionalDeligneValue_ofRepresentation_twist K hε ψ μ χ T₀ hT₀ s]
  apply value_twist_eq_of_witness K hε.2.1 hw (FiniteRepresentation.isContinuous_twist _ hT)
    (FiniteRepresentation.isContinuous_twist _ hT₀)
  · exact htw T hN
  · exact htw T₀ hN₀
  · change T.rank = T₀.rank
    exact hrank
  · apply MonoidHom.ext
    intro g
    apply Units.ext
    change LinearMap.det (((CommonClosureSpectral.character K E s g : ℂˣ) : ℂ) •
        T.representation g) =
      LinearMap.det (((CommonClosureSpectral.character K E s g : ℂˣ) : ℂ) • T₀.representation g)
    rw [LinearMap.det_smul, LinearMap.det_smul]
    change _ ^ T.rank * _ = _ ^ T₀.rank * _
    rw [hrank]
    congr 1
    exact congrArg (fun φ : weilSubgroup K E →* ℂˣ => ((φ g : ℂˣ) : ℂ)) hdet

/-- The conductor of the bottom-field transport of a quasi-character's Weil character. -/
theorem conductor_baseFieldCharacter {e : ReciprocityCandidate K} {eC : ReciprocityFamily K}
    (he : IsBaseReciprocity K e eC) (χ : QuasiCharacter K) :
    (fieldData K (DeligneHenniart.baseExtension K)).multiplicativeConductor
        (DeligneHenniart.baseFieldCharacter K eC (LocalFactor.RankOne.weilCharacter K e χ)) =
      K.canonicalTopologicalData.multiplicativeConductor χ := by
  change (fieldData K (baseExtension K)).multiplicativeConductor
    (CommonClosureSpectralAnalytic.fieldCharacterEquiv K eC (baseExtension K)
      (baseRestrictedWeilCharacter K (LocalFactor.RankOne.weilCharacter K e χ))) = _
  rw [fieldCharacterEquiv_baseRestrictedWeilCharacter K he χ,
    NonabelianBrauer.multiplicativeConductor_baseFieldCharacterEquiv]

/-- A character whose bottom-field transport has conductor `b + 1 ≥ 2`: its class has an
exact witness relative to the upper group of index `b / 2`, and it is nontrivial on every
upper group of index below `b`. -/
theorem deepCharacter_facts {e : ReciprocityFamily K} {ε : Assignment.{u, uE} K}
    (hε : IsSystem K e ε) (χ : localWeilGroup K →ₜ* ℂˣ) {b : ℕ} (hb : 1 ≤ b)
    (hcond : (fieldData K (DeligneHenniart.baseExtension K)).multiplicativeConductor
      (DeligneHenniart.baseFieldCharacter K e χ) = b + 1) :
    (∀ ψ' : AdditiveCharacter K (DeligneHenniart.baseExtension K),
      ∃ γ : (DeligneHenniart.baseExtension K).fieldˣ,
        DeligneHenniart.ExactWitnessOn K e ε (DeligneHenniart.baseExtension K)
          (DeligneHenniart.baseUpperGroup K ((b : ℝ) / 2)) ψ'
          (ExactGrothendieckGroup.characterClass
            (χ.comp (DeligneHenniart.baseWeilInclusion K))) γ) ∧
      ∀ r : ℝ, 0 ≤ r → r < b → ∃ w ∈ LocalWeil.Ramification.upperGroup K r, χ w ≠ 1 := by
  have hreal := (LocalClassField.absoluteUpperReciprocityTheorems_of_finiteRealImages
      (LocalClassField.finiteReciprocityRealUnitImages_of_normCardinality
        LocalClassField.NormUnitImage.finiteAbelianNormUnitImageCardinality.{u, u})).2.2.1
  have hinert := Ramification.HerbrandBridge.absoluteUpperInertia K K.canonicalTopologicalData
  have hcmp := LocalClassField.unitFiltrationComparison.{u}
  have hgeo := LocalClassField.commonClosureGeometricProof.{u, u}
  have hWK := fun (s : ℝ) (hs : 0 ≤ s) =>
    DeligneHenniart.baseUpperGroup_map_reciprocityUnits K hreal hinert hcmp e
      (DeligneHenniart.geometric_baseReciprocityCandidate K hgeo e hε.1) hs
  have hWL := fun (L : Extension K) (s : ℝ) (hs : 0 ≤ s) =>
    DeligneHenniart.intermediateUpperGroup_map_reciprocityUnits K hreal hcmp e L
      (Ramification.HerbrandBridge.absoluteUpperInertia _ _)
      (DeligneHenniart.intermediateGeometricProof.{u} p K e hε.1 L) hs
  have htop := DeligneHenniart.TopLayer.topLayerNormTrace.{u, u, u}
  have hlab : LocalWeil.Ramification.breakLabel K
      (DeligneHenniart.lineBasis.{u, max u uE} χ) = b :=
    DeligneHenniart.breakLabel_lineBasis K χ hcond hWK
  have hline : LocalWeil.Ramification.lastBreak K
      (FiniteRepresentation.characterLine.{u, max u uE} χ.toMonoidHom) = b := hlab
  refine ⟨fun ψ' => ?_, fun r hr hrb => ?_⟩
  · have hsupp : ∀ c, VirtualRepresentation.generator
        (DeligneHenniart.lineBasis.{u, max u uE} χ) c ≠ 0 →
          c = DeligneHenniart.lineBasis.{u, max u uE} χ := by
      intro c hc
      by_contra hne
      apply hc
      rw [VirtualRepresentation.generator, Finsupp.single_eq_of_ne hne]
    have hpos : LocalWeil.Ramification.PositiveBreakSupport K
        (VirtualRepresentation.generator (DeligneHenniart.lineBasis.{u, max u uE} χ)) := by
      intro c hc
      rw [hsupp c hc, hlab]
      exact_mod_cast (show 0 < b by omega)
    have ha : LocalWeil.Ramification.AllBreaksAtLeast K
        (VirtualRepresentation.generator (DeligneHenniart.lineBasis.{u, max u uE} χ))
        (b : ℝ) := by
      intro c hc
      rw [hsupp c hc, hlab]
    obtain ⟨γ, -, hex, -⟩ :=
      DeligneHenniart.exists_witness_lattice K hε hWK hWL htop ψ' _ hpos ha
    refine ⟨γ, ?_⟩
    rw [DeligneHenniart.realizeAtBase_generator_lineBasis K e χ, CommonClosure.characterClass,
      DeligneHenniart.baseFieldCharacter,
      CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv] at hex
    exact hex
  · by_contra hcon
    push Not at hcon
    have hthr : r ∈ LocalWeil.Ramification.trivialityThresholds K
        (FiniteRepresentation.characterLine.{u, max u uE} χ.toMonoidHom) :=
      ⟨hr, (DeligneHenniart.isTrivialAt_characterLine_iff K χ r).mpr hcon⟩
    have h1 := LocalWeil.Ramification.lastBreak_le_of_mem K _ hthr
    rw [hline] at h1
    linarith

end DeepTwist

section Main

open LocalFactor.NonabelianSystem

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

/-- The restriction of a pair to the bottom fixing subgroup is equivalent to its bottom-field
pair. -/
def basePairEquiv (B : LocalWeilDeligneRepresentation.{u, uV} K) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup K (baseExtension K)).subtype B)
      (basePair.{u, uV, uE} K B) :=
  transportPairEquiv _ _ _

/-- An element acting trivially on both factors acts trivially on `tensorBaseRep`. -/
theorem tensorBaseRep_trivial {B B' : LocalWeilDeligneRepresentation.{u, uV} K}
    {g : weilSubgroup K (baseExtension K)} (hB : B.representation g.val = 1)
    (hB' : B'.representation g.val = 1) :
    (tensorBaseRep.{u, uV, uE} K B B').representation g = 1 := by
  change (FiniteRepresentation.universeModel
      (FiniteRepresentation.tensor B.toFiniteRepresentation B'.toFiniteRepresentation) :
      FiniteRepresentation.{0, u, max u uE} ℂ (localWeilGroup K)).representation g.val = 1
  apply representation_universeModel_eq_one
  have h1 : B.toFiniteRepresentation.representation g.val = (1 : ℂ) • 1 := by
    rw [one_smul]
    exact hB
  have h := tensor_representation_eq_smul B.toFiniteRepresentation B'.toFiniteRepresentation
    h1 hB'
  rw [one_smul] at h
  exact h

/-- The rank of `tensorBaseRep` is the product of the ranks. -/
theorem tensorBaseRep_rank (B B' : LocalWeilDeligneRepresentation.{u, uV} K) :
    (tensorBaseRep.{u, uV, uE} K B B').rank = B.rank * B'.rank := by
  change (FiniteRepresentation.universeModel
      (FiniteRepresentation.tensor B.toFiniteRepresentation B'.toFiniteRepresentation) :
      FiniteRepresentation.{0, u, max u uE} ℂ (localWeilGroup K)).rank = _
  rw [rank_universeModel]
  exact Module.finrank_tensorProduct

/-- The determinant of `tensorBaseRep` in terms of the determinants and ranks of the
factors. -/
theorem determinantCharacter_tensorBaseRep_apply (B B' : LocalWeilDeligneRepresentation.{u, uV} K)
    (g : weilSubgroup K (baseExtension K)) :
    (FiniteRepresentation.determinantCharacter (tensorBaseRep.{u, uV, uE} K B B') g : ℂ) =
      (FiniteRepresentation.determinantCharacter B.toFiniteRepresentation g.val : ℂ) ^ B'.rank *
        (FiniteRepresentation.determinantCharacter B'.toFiniteRepresentation g.val : ℂ) ^
          B.rank := by
  change (FiniteRepresentation.determinantCharacter (FiniteRepresentation.universeModel
      (FiniteRepresentation.tensor B.toFiniteRepresentation B'.toFiniteRepresentation) :
      FiniteRepresentation.{0, u, max u uE} ℂ (localWeilGroup K)) g.val : ℂ) = _
  rw [determinantCharacter_universeModel, FiniteRepresentation.determinantCharacter_apply,
    FiniteRepresentation.determinantCharacter_apply, FiniteRepresentation.determinantCharacter_apply]
  exact Langlands.det_tensorProduct_map _ _

/-- Equal ranks and determinants of the factors give equal determinants of the bottom-field
tensor representations. -/
theorem tensorBaseRep_det_eq {B B₀ B' B₀' : LocalWeilDeligneRepresentation.{u, uV} K}
    (hr : B.rank = B₀.rank) (hr' : B'.rank = B₀'.rank)
    (hd : FiniteRepresentation.determinantCharacter B.toFiniteRepresentation =
      FiniteRepresentation.determinantCharacter B₀.toFiniteRepresentation)
    (hd' : FiniteRepresentation.determinantCharacter B'.toFiniteRepresentation =
      FiniteRepresentation.determinantCharacter B₀'.toFiniteRepresentation) :
    FiniteRepresentation.determinantCharacter (tensorBaseRep.{u, uV, uE} K B B') =
      FiniteRepresentation.determinantCharacter (tensorBaseRep.{u, uV, uE} K B₀ B₀') := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  rw [determinantCharacter_tensorBaseRep_apply, determinantCharacter_tensorBaseRep_apply, hd, hd',
    hr, hr']

/-- When some inertia element acts trivially on both factors and nontrivially through `χ`,
the pair epsilon value of bottom-field data for `(B ⊗ χ, B')` is the Deligne value of the
twisted bottom-field tensor representation. -/
theorem conditionalPairEpsilonValue_eq_deligne {e : ReciprocityFamily K}
    {ε : Assignment.{u, uE} K} (hε : IsSystem K e ε) (ψ' : AdditiveCharacter K (baseExtension K))
    (μ : HaarMeasure K (baseExtension K)) (χ : localWeilGroup K →ₜ* ℂˣ)
    {B B' : LocalWeilDeligneRepresentation.{u, uV} K} (hB : B.toFiniteRepresentation.IsContinuous)
    (hB' : B'.toFiniteRepresentation.IsContinuous) {P P' : Pair.{u, uE} K (baseExtension K)}
    (fP : WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.restrict
      (weilSubgroup K (baseExtension K)).subtype (WeilDeligneRepresentation.twist χ.toMonoidHom B)) P)
    (fP' : WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.restrict
      (weilSubgroup K (baseExtension K)).subtype B') P')
    (hP : P.toFiniteRepresentation.IsContinuous) (hP' : P'.toFiniteRepresentation.IsContinuous)
    {w : localWeilGroup K} (hwI : w ∈ localInertia K) (hBw : B.representation w = 1)
    (hB'w : B'.representation w = 1) (hχ : χ w ≠ 1)
    (Φ : GeometricFrobenius K (baseExtension K)) (s : ℂ) :
    CommonClosureGamma.conditionalPairEpsilonValue K e ε hε (baseExtension K) ψ' μ P P' hP hP' Φ s =
      CommonClosureSpectral.conditionalDeligneValue K e ε hε (baseExtension K) ψ' μ
        (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{u, uE} K (baseExtension K))
          ⟨FiniteRepresentation.twist (χ.comp (baseInclusion K)).toMonoidHom
            (tensorBaseRep.{u, uV, uE} K B B'),
            FiniteRepresentation.isContinuous_twist _ (tensorBaseRep_isContinuous K hB hB')⟩) s := by
  unfold CommonClosureGamma.conditionalPairEpsilonValue conditionalEpsilonValue
  rw [quotientValue_eq_one K _ (invariantSubspace_tensor_eq_bot K χ fP fP' hwI hBw hB'w hχ),
    mul_one]
  exact congrArg
    (fun x => CommonClosureSpectral.conditionalDeligneValue K e ε hε (baseExtension K) ψ' μ x s)
    (ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _ (tensorTwistEquiv K χ B B' fP fP'))

end Main

section Theorem

open LocalFactor.NonabelianSystem

/-- Arithmetic pair gamma factors of `(X ⊗ χ) ⊗ Y` and `(X₀ ⊗ χ) ⊗ Y₀` agree for all
sufficiently ramified `χ` (Deligne–Henniart stability; Henniart 1986, Lemma 4.2). -/
theorem arithmeticStableTwistGamma :
    ClassField.Global.RelativeWeilGroup.ArithmeticStableTwistGammaStatement.{u, uV, uE} := by
  intro p _ K eC ε hε e he ψ r t ω ω' X X₀ Y Y₀ hX hX₀ hY hY₀
  obtain ⟨B, rfl, hBr, hBc, hBd⟩ := hX
  obtain ⟨B₀, rfl, hB₀r, hB₀c, hB₀d⟩ := hX₀
  obtain ⟨B', rfl, hB'r, hB'c, hB'd⟩ := hY
  obtain ⟨B₀', rfl, hB₀'r, hB₀'c, hB₀'d⟩ := hY₀
  obtain ⟨s₀, hs₀, htriv⟩ := exists_common_threshold K hBc hB₀c hB'c hB₀'c
  refine ⟨⌈2 * s₀⌉₊ + 3, fun χ hχ G hG => ?_⟩
  obtain ⟨c, m, hEps₀, rfl⟩ := hG
  obtain ⟨χW, hχW⟩ : ∃ χW, χW = LocalFactor.RankOne.weilCharacter K e χ := ⟨_, rfl⟩
  have hWχ : Correspondence.weilCharacter K e χ = χW.toMonoidHom := by
    rw [hχW]
    rfl
  rw [hWχ] at hEps₀ ⊢
  obtain ⟨b, hb⟩ : ∃ b : ℕ, K.canonicalTopologicalData.multiplicativeConductor χ = b + 1 :=
    ⟨K.canonicalTopologicalData.multiplicativeConductor χ - 1, by omega⟩
  have hbA : ⌈2 * s₀⌉₊ + 2 ≤ b := by omega
  have hcond : (fieldData K (DeligneHenniart.baseExtension K)).multiplicativeConductor
      (DeligneHenniart.baseFieldCharacter K eC χW) = b + 1 := by
    rw [hχW, conductor_baseFieldCharacter K he χ, hb]
  obtain ⟨hwit, hnontriv⟩ := deepCharacter_facts K hε χW (by omega : 1 ≤ b) hcond
  have h2s : 2 * s₀ < b := by
    have h1 := Nat.le_ceil (2 * s₀)
    have h2 : ((⌈2 * s₀⌉₊ : ℕ) : ℝ) + 2 ≤ b := by exact_mod_cast hbA
    linarith
  obtain ⟨w, hw, hχw⟩ := hnontriv s₀ hs₀ (by linarith)
  obtain ⟨hBw, hB₀w, hB'w, hB₀'w⟩ := htriv w hw
  obtain ⟨hBi, hB₀i, hB'i, hB₀'i⟩ := htriv w⁻¹ (Subgroup.inv_mem _ hw)
  have hwI : w ∈ localInertia K := upperGroup_le_localInertia K hs₀ hw
  have hb0 : (0 : ℝ) ≤ (b : ℝ) / 2 := by positivity
  have hNI := DeligneHenniart.baseUpperGroup_le_inertia K
    (Ramification.HerbrandBridge.absoluteUpperInertia K K.canonicalTopologicalData) hb0
  have hNs : ∀ n ∈ DeligneHenniart.baseUpperGroup K ((b : ℝ) / 2),
      n.val ∈ LocalWeil.Ramification.upperGroup K s₀ := fun n hn =>
    LocalWeil.Ramification.upperGroup_antitone K (by linarith)
      ((DeligneHenniart.mem_baseUpperGroup K n).mp hn)
  have hT : ∀ n ∈ DeligneHenniart.baseUpperGroup K ((b : ℝ) / 2),
      (tensorBaseRep.{u, uV, uE} K B B').representation n = 1 := fun n hn =>
    tensorBaseRep_trivial K (htriv n.val (hNs n hn)).1 (htriv n.val (hNs n hn)).2.2.1
  have hT₀ : ∀ n ∈ DeligneHenniart.baseUpperGroup K ((b : ℝ) / 2),
      (tensorBaseRep.{u, uV, uE} K B₀ B₀').representation n = 1 := fun n hn =>
    tensorBaseRep_trivial K (htriv n.val (hNs n hn)).2.1 (htriv n.val (hNs n hn)).2.2.2
  have hrank : (tensorBaseRep.{u, uV, uE} K B B').rank =
      (tensorBaseRep.{u, uV, uE} K B₀ B₀').rank := by
    rw [tensorBaseRep_rank, tensorBaseRep_rank, hBr, hB₀r, hB'r, hB₀'r]
  have hdet := tensorBaseRep_det_eq.{u, uV, uE} K (hBr.trans hB₀r.symm) (hB'r.trans hB₀'r.symm)
    (hBd.trans hB₀d.symm) (hB'd.trans hB₀'d.symm)
  have hcontB : (WeilDeligneRepresentation.twist χW.toMonoidHom B).toFiniteRepresentation.IsContinuous :=
    FiniteRepresentation.isContinuous_twist χW hBc
  have hcontB₀ :
      (WeilDeligneRepresentation.twist χW.toMonoidHom B₀).toFiniteRepresentation.IsContinuous :=
    FiniteRepresentation.isContinuous_twist χW hB₀c
  obtain ⟨⟨ψ₀, μ₀, A₀, A₀', ⟨hψ₀, hμ₀, -, -⟩, -, -⟩, hΦ, hval⟩ := hEps₀
  refine ⟨c, m, ⟨⟨ψ₀, μ₀, basePair K (WeilDeligneRepresentation.twist χW.toMonoidHom B),
    basePair K B', ⟨hψ₀, hμ₀, isBaseRestriction_basePair K _, isBaseRestriction_basePair K _⟩,
    basePair_isContinuous K hcontB, basePair_isContinuous K hB'c⟩, hΦ, ?_⟩, ?_⟩
  · intro ψ' μ P P' hdat hP hP' Φ s
    obtain ⟨fP⟩ := IsBaseRestriction.nonempty_equiv K
      (A := WeilDeligneRepresentation.twist χW.toMonoidHom B) rfl hdat.2.2.1
    obtain ⟨fP'⟩ := IsBaseRestriction.nonempty_equiv K (A := B') rfl hdat.2.2.2
    have hP₀ : (basePair.{u, uV, uE} K
        (WeilDeligneRepresentation.twist χW.toMonoidHom B₀)).toFiniteRepresentation.IsContinuous :=
      basePair_isContinuous K hcontB₀
    have hP₀' : (basePair.{u, uV, uE} K B₀').toFiniteRepresentation.IsContinuous :=
      basePair_isContinuous K hB₀'c
    rw [← hval ψ' μ _ _ ⟨hdat.1, hdat.2.1, isBaseRestriction_basePair K _,
      isBaseRestriction_basePair K _⟩ hP₀ hP₀' Φ s]
    congr 1
    obtain ⟨γ, hγ⟩ := hwit ψ'
    rw [conditionalPairEpsilonValue_eq_deligne K hε ψ' μ χW hBc hB'c fP fP' hP hP' hwI hBw hB'w
        hχw Φ s,
      conditionalPairEpsilonValue_eq_deligne K hε ψ' μ χW hB₀c hB₀'c (basePairEquiv K _)
        (basePairEquiv K _) hP₀ hP₀' hwI hB₀w hB₀'w hχw Φ s]
    exact conditionalDeligneValue_twist_eq K hε hNI hγ (tensorBaseRep_isContinuous K hBc hB'c)
      (tensorBaseRep_isContinuous K hB₀c hB₀'c) hT hT₀ hrank hdet μ s
  · congr 1
    exact (rationalLRatio_twist_tensor_eq_one K χW B₀ B₀' hwI hB₀w hB₀'w hB₀i hB₀'i hχw _ _).trans
      (rationalLRatio_twist_tensor_eq_one K χW B B' hwI hBw hB'w hBi hB'i hχw _ _).symm

end Theorem

end Langlands.ArithmeticStableTwist

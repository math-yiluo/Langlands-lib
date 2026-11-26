import Langlands.Correspondence.HenniartGaloisDictionaryStatement
import Langlands.Weil.Local.SepClosedTopology
import Langlands.Weil.Representation.UnramifiedReductionProof
import Langlands.Weil.Representation.FiniteImageExtensionProof
import Langlands.Weil.Representation.ContinuityBridgeProof
import Langlands.Weil.Representation.ContinuityProof

/-!
# Pullback of continuous irreducible Galois classes to the local Weil group

For a nonarchimedean local field `K` and a separable closure `Ω`, this file compares
rank-tagged continuous irreducible complex classes of `Ω ≃ₐ[K] Ω` with those of the Weil
group `localWeilGroup K Ω` through restriction along `localProjection K Ω`.
-/

noncomputable section

namespace Langlands.Henniart.LocalNumerical

open Langlands.VirtualRepresentation Langlands.FiniteRepresentation
open Langlands.Weil.Local.SepClosed

universe uG uH uV uK uΩ

section Generic

/-- Precomposition preserves and reflects irreducibility when every operator of the original
representation is attained on the image of the homomorphism. -/
theorem isIrreducible_comp_iff_of_forall_exists {G : Type uG} {H : Type uH} [Monoid G]
    [Monoid H] {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (f : G →* H) (hf : ∀ h, ∃ g, ρ (f g) = ρ h) :
    Representation.IsIrreducible (ρ.comp f) ↔ ρ.IsIrreducible := by
  let e : Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun h v hv => by
        obtain ⟨g, hg⟩ := hf h
        rw [← hg]
        exact S.apply_mem_toSubmodule g hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact OrderIso.isSimpleOrder_iff e

/-- The carrier of an irreducible representation is nontrivial. -/
theorem nontrivial_of_isIrreducible {G : Type uG} [Monoid G] {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have := h
  exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

/-- Restriction of classes commutes with twisting by a character. -/
theorem restrictClass_twistClass {G : Type uG} {H : Type uH} [Group G] [Group H]
    (f : H →* G) (χ : G →* ℂˣ) (c : IsomorphismClasses.{0, uG, uV} ℂ G) :
    restrictClass f (twistClass χ c) = twistClass (χ.comp f) (restrictClass f c) := by
  refine Quotient.inductionOn c fun A => ?_
  exact Quotient.sound ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun _ => rfl⟩

private theorem map_pow_sub_eq_one {G N : Type*} [Group G] [Monoid N] (σ : G →* N) (g : G)
    {a b : ℕ} (hab : a ≤ b) (h : σ (g ^ a) = σ (g ^ b)) : σ (g ^ (b - a)) = 1 := by
  rw [pow_sub g hab, map_mul, ← h, ← map_mul, mul_inv_cancel, map_one]

/-- Two group elements of finite image under two homomorphisms have a common positive power
in both kernels. -/
theorem exists_pow_eq_one_of_finite_range {G : Type uG} {M M' : Type*} [Group G] [Monoid M]
    [Monoid M'] (ρ : G →* M) (ρ' : G →* M') (h : (Set.range ρ).Finite) (h' : (Set.range ρ').Finite) (g : G) :
    ∃ m : ℕ, 0 < m ∧ ρ (g ^ m) = 1 ∧ ρ' (g ^ m) = 1 := by
  have := h.to_subtype
  have := h'.to_subtype
  obtain ⟨i, j, hij, hf⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => ((⟨ρ (g ^ n), g ^ n, rfl⟩ : Set.range ρ),
      (⟨ρ' (g ^ n), g ^ n, rfl⟩ : Set.range ρ')))
  have h1 : ρ (g ^ i) = ρ (g ^ j) := congrArg (fun x => (x.1 : M)) hf
  have h2 : ρ' (g ^ i) = ρ' (g ^ j) := congrArg (fun x => (x.2 : M')) hf
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact ⟨j - i, Nat.sub_pos_of_lt hlt, map_pow_sub_eq_one ρ g hlt.le h1,
      map_pow_sub_eq_one ρ' g hlt.le h2⟩
  · exact ⟨i - j, Nat.sub_pos_of_lt hlt, map_pow_sub_eq_one ρ g hlt.le h1.symm,
      map_pow_sub_eq_one ρ' g hlt.le h2.symm⟩

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A rank-tagged continuous irreducible class is determined by its underlying isomorphism
class. -/
theorem underlyingClass_injective :
    Function.Injective (Weil.underlyingClass.{uG, uV} G) := by
  rintro ⟨n, x⟩ ⟨n', x'⟩ h
  have hn : n = n' := by
    apply PNat.coe_injective
    have hr := congrArg classRank h
    exact x.property.symm.trans (hr.trans x'.property)
  subst hn
  have hx : x = x' := Subtype.ext (forgetPropertyClass_injective _ h)
  subst hx
  rfl

/-- Rank-tagged classes of the same rank are equal exactly when their classes are. -/
theorem irreducibleBasis_mk_injective {n : ℕ+}
    {x y : ContinuousIrreducibleClasses.{uG, uV} G n}
    (h : (⟨n, x⟩ : Weil.IrreducibleBasis.{uG, uV} G) = ⟨n, y⟩) : x = y :=
  eq_of_heq (Sigma.mk.inj_iff.mp h).2

/-- Every rank-tagged continuous irreducible class has a continuous irreducible
representative. -/
theorem exists_classOf_eq_underlyingClass (b : Weil.IrreducibleBasis.{uG, uV} G) :
    ∃ A : FiniteRepresentation.{0, uG, uV} ℂ G,
      A.IsContinuous ∧ A.IsIrreducible ∧ classOf A = Weil.underlyingClass G b := by
  obtain ⟨⟨A, hc, hi⟩, hA⟩ := Quotient.exists_rep b.2.val
  refine ⟨A, hc, hi, ?_⟩
  change classOf A = forgetPropertyClass _ b.2.val
  rw [← hA]
  rfl

omit [TopologicalSpace G] in
/-- The rank of an irreducible representation is positive. -/
theorem rank_pos_of_isIrreducible (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hi : A.IsIrreducible) : 0 < A.rank := by
  have := nontrivial_of_isIrreducible A.representation hi
  exact Module.finrank_pos

/-- The rank-tagged class of a continuous irreducible representation. -/
def irreducibleBasisOf (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hc : A.IsContinuous)
    (hi : A.IsIrreducible) : Weil.IrreducibleBasis.{uG, uV} G :=
  ⟨⟨A.rank, rank_pos_of_isIrreducible A hi⟩, ⟨Quotient.mk _ ⟨A, hc, hi⟩, rfl⟩⟩

@[simp]
theorem underlyingClass_irreducibleBasisOf (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hc : A.IsContinuous) (hi : A.IsIrreducible) :
    Weil.underlyingClass G (irreducibleBasisOf A hc hi) = classOf A := rfl

/-- The kernel of a continuous complex representation of a nonarchimedean group is open. -/
theorem isOpen_ker_of_isContinuous [NonarchimedeanGroup G]
    (B : FiniteRepresentation.{0, uG, uV} ℂ G) (hB : B.IsContinuous) :
    IsOpen (B.representation.ker : Set G) := by
  let := B.carrierNormedAddCommGroup
  let := B.carrierNormedSpace
  exact Weil.open_kernel_of_continuous_nonarchimedean_representation B.representation
    ((FiniteRepresentation.isContinuous_of_iff _).mp hB)

/-- A continuous complex representation of a compact nonarchimedean group has finite image. -/
theorem finite_range_of_isContinuous [NonarchimedeanGroup G] [CompactSpace G]
    (B : FiniteRepresentation.{0, uG, uV} ℂ G) (hB : B.IsContinuous) :
    (Set.range B.representation).Finite := by
  let := B.carrierNormedAddCommGroup
  let := B.carrierNormedSpace
  exact Weil.continuous_compact_nonarchimedean_representation_finite_range G B
    B.representation ((FiniteRepresentation.isContinuous_of_iff _).mp hB)

end Generic

section Local

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]

local notation "Γ" => (Ω ≃ₐ[K] Ω)

/-- A rank-tagged continuous irreducible Weil class is the restriction of a rank-tagged
continuous irreducible Galois class along the projection `localProjection K Ω`. -/
def IsGaloisPullbackBasis (b : Weil.IrreducibleBasis.{uΩ, uV} (localWeilGroup K Ω))
    (c : Weil.IrreducibleBasis.{uΩ, uV} Γ) : Prop :=
  Weil.underlyingClass _ b =
    restrictClass (localProjection K Ω).toMonoidHom (Weil.underlyingClass Γ c)

/-- Two continuous representations of `Ω ≃ₐ[K] Ω` take, at a projected Weil element, the
same values as at any prescribed Galois element. -/
theorem exists_localProjection_eq (B B' : FiniteRepresentation.{0, uΩ, uV} ℂ Γ)
    (hB : B.IsContinuous) (hB' : B'.IsContinuous) (g : Γ) :
    ∃ w : localWeilGroup K Ω, B.representation (localProjection K Ω w) = B.representation g ∧
      B'.representation (localProjection K Ω w) = B'.representation g := by
  have := absoluteGalois_nonarchimedean K Ω
  let N : Subgroup Γ := B.representation.ker ⊓ B'.representation.ker
  have hN : IsOpen (N : Set Γ) :=
    (isOpen_ker_of_isContinuous B hB).inter (isOpen_ker_of_isContinuous B' hB')
  have hU : IsOpen ((fun x : Γ => g⁻¹ * x) ⁻¹' (N : Set Γ)) :=
    hN.preimage (continuous_const.mul continuous_id)
  have hg : g ∈ (fun x : Γ => g⁻¹ * x) ⁻¹' (N : Set Γ) := by
    change g⁻¹ * g ∈ N
    rw [inv_mul_cancel]
    exact N.one_mem
  obtain ⟨w, hw⟩ := (localProjection_denseRange K Ω).exists_mem_open hU ⟨g, hg⟩
  have hw' : g⁻¹ * localProjection K Ω w ∈ N := hw
  have h1 : B.representation (g⁻¹ * localProjection K Ω w) = 1 := hw'.1
  have h2 : B'.representation (g⁻¹ * localProjection K Ω w) = 1 := hw'.2
  refine ⟨w, ?_, ?_⟩
  · rw [← mul_inv_cancel_left g (localProjection K Ω w), map_mul, h1, mul_one]
  · rw [← mul_inv_cancel_left g (localProjection K Ω w), map_mul, h2, mul_one]

/-- Restriction to the Weil group preserves and reflects irreducibility of continuous
representations of `Ω ≃ₐ[K] Ω`. -/
theorem isIrreducible_restrict_iff (B : FiniteRepresentation.{0, uΩ, uV} ℂ Γ)
    (hB : B.IsContinuous) :
    (restrict (localProjection K Ω).toMonoidHom B).IsIrreducible ↔ B.IsIrreducible :=
  isIrreducible_comp_iff_of_forall_exists B.representation _ fun g => by
    obtain ⟨w, hw, -⟩ := exists_localProjection_eq K Ω B B hB hB g
    exact ⟨w, hw⟩

/-- Restriction to the Weil group preserves continuity. -/
theorem isContinuous_restrict (B : FiniteRepresentation.{0, uΩ, uV} ℂ Γ)
    (hB : B.IsContinuous) : (restrict (localProjection K Ω).toMonoidHom B).IsContinuous := by
  let : TopologicalSpace (Module.End ℂ B) := moduleTopology ℂ (Module.End ℂ B)
  have h : Continuous B.representation := hB
  exact h.comp (localProjection K Ω).continuous

/-- Every Galois class has a Weil pullback. -/
theorem exists_isGaloisPullbackBasis (c : Weil.IrreducibleBasis.{uΩ, uV} Γ) :
    ∃ b, IsGaloisPullbackBasis K Ω b c := by
  obtain ⟨B, hBc, hBi, hB⟩ := exists_classOf_eq_underlyingClass c
  refine ⟨irreducibleBasisOf _ (isContinuous_restrict K Ω B hBc)
    ((isIrreducible_restrict_iff K Ω B hBc).mpr hBi), ?_⟩
  rw [IsGaloisPullbackBasis, underlyingClass_irreducibleBasisOf, ← hB]
  rfl

/-- A Weil pullback of a Galois class is unique. -/
theorem IsGaloisPullbackBasis.weil_unique {b b' : Weil.IrreducibleBasis.{uΩ, uV}
    (localWeilGroup K Ω)} {c : Weil.IrreducibleBasis.{uΩ, uV} Γ}
    (h : IsGaloisPullbackBasis K Ω b c) (h' : IsGaloisPullbackBasis K Ω b' c) : b = b' :=
  underlyingClass_injective (h.trans h'.symm)

/-- Restriction to the Weil group is injective on continuous irreducible Galois classes. -/
theorem galoisBasis_eq_of_restrictClass_eq {c c' : Weil.IrreducibleBasis.{uΩ, uV} Γ}
    (h : restrictClass (localProjection K Ω).toMonoidHom (Weil.underlyingClass Γ c) =
      restrictClass (localProjection K Ω).toMonoidHom (Weil.underlyingClass Γ c')) :
    c = c' := by
  obtain ⟨B, hBc, -, hB⟩ := exists_classOf_eq_underlyingClass c
  obtain ⟨B', hB'c, -, hB'⟩ := exists_classOf_eq_underlyingClass c'
  rw [← hB, ← hB'] at h
  obtain ⟨e⟩ := (classOf_eq_iff _ _).mp h
  apply underlyingClass_injective
  rw [← hB, ← hB']
  refine (classOf_eq_iff _ _).mpr ⟨Representation.Equiv.mk e.toLinearEquiv fun g => ?_⟩
  obtain ⟨w, hw, hw'⟩ := exists_localProjection_eq K Ω B B' hBc hB'c g
  rw [← hw, ← hw']
  exact e.isIntertwining' w

/-- A Weil class is the pullback of at most one Galois class. -/
theorem IsGaloisPullbackBasis.galois_unique {b : Weil.IrreducibleBasis.{uΩ, uV}
    (localWeilGroup K Ω)} {c c' : Weil.IrreducibleBasis.{uΩ, uV} Γ}
    (h : IsGaloisPullbackBasis K Ω b c) (h' : IsGaloisPullbackBasis K Ω b c') : c = c' :=
  galoisBasis_eq_of_restrictClass_eq K Ω (h.symm.trans h')

/-- Every irreducible Weil class has an unramified twist that is the pullback of a Galois
class (Henniart 1980, §2.3, Corollary 3). -/
theorem exists_twist_isGaloisPullbackBasis
    (b : Weil.IrreducibleBasis.{uΩ, uV} (localWeilGroup K Ω)) :
    ∃ (z : ℂˣ) (c : Weil.IrreducibleBasis.{uΩ, uV} Γ),
      IsGaloisPullbackBasis K Ω (Weil.twistBasisEquiv (localUnramifiedCharacter K Ω z) b) c := by
  obtain ⟨A, hAc, hAi, hA⟩ := exists_classOf_eq_underlyingClass b
  have : CompactSpace (localDegree K Ω).toMonoidHom.ker :=
    isCompact_iff_compactSpace.mp (localInertia_isCompact K Ω)
  have := localWeilGroup_nonarchimedean K Ω
  have := absoluteGalois_nonarchimedean K Ω
  have := absoluteGalois_t2Space K Ω
  let := A.carrierNormedAddCommGroup
  let := A.carrierNormedSpace
  obtain ⟨⟨χ, σ, -, hχi, hσc, hσf, hσirr, heq⟩, -⟩ :=
    (Weil.unramifiedReduction (localWeilGroup K Ω) (localDegree K Ω).toMonoidHom
      (localDegree_surjective K Ω) (localInertia_isOpen K Ω) A A.representation
      ((FiniteRepresentation.isContinuous_of_iff _).mp hAc)).2 hAi
  set z := χ (localGeometricFrobenius K Ω) with hz
  have hχ : (localUnramifiedCharacter K Ω z).toMonoidHom = χ :=
    localUnramifiedCharacter_eq_of_on_inertia K Ω χ fun w hw => hχi ⟨w, hw⟩
  obtain ⟨τ, ⟨hτc, hτr⟩, -⟩ :=
    (Weil.finiteImageExtension Γ (localResidueDegree K Ω) (localResidueDegree_surjective K Ω)
      A σ hσc).mp hσf
  have hτc' : (FiniteRepresentation.of τ).IsContinuous :=
    (FiniteRepresentation.isContinuous_of_iff τ).mpr hτc
  have hτi : (FiniteRepresentation.of τ).IsIrreducible := by
    rw [← isIrreducible_restrict_iff K Ω _ hτc']
    change Representation.IsIrreducible (τ.comp (localProjection K Ω).toMonoidHom)
    rw [show τ.comp (localProjection K Ω).toMonoidHom = σ from hτr]
    exact hσirr
  refine ⟨z⁻¹, irreducibleBasisOf _ hτc' hτi, ?_⟩
  rw [IsGaloisPullbackBasis, Weil.underlyingClass_twistBasisEquiv, ← hA,
    underlyingClass_irreducibleBasisOf, twistClass_classOf]
  refine (classOf_eq_iff _ _).mpr ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun w => ?_⟩
  apply LinearMap.ext
  intro v
  have hτw : τ (localProjection K Ω w) = σ w := DFunLike.congr_fun hτr w
  have hAw : A.representation w = Langlands.twist χ σ w := DFunLike.congr_fun heq w
  have hχw : χ w = localUnramifiedCharacter K Ω z w := (DFunLike.congr_fun hχ w).symm
  change ((localUnramifiedCharacter K Ω z⁻¹ w : ℂˣ) : ℂ) •
      A.representation w v = τ (localProjection K Ω w) v
  rw [hτw, hAw]
  change ((localUnramifiedCharacter K Ω z⁻¹ w : ℂˣ) : ℂ) • (((χ w : ℂˣ) : ℂ) • σ w v) = σ w v
  rw [hχw, smul_smul, ← Units.val_mul]
  have hone : localUnramifiedCharacter K Ω z⁻¹ w * localUnramifiedCharacter K Ω z w = 1 := by
    simp only [localUnramifiedCharacter, Weil.Local.unramifiedCharacter_apply, ← mul_zpow,
      inv_mul_cancel, one_zpow]
  rw [hone, Units.val_one, one_smul]

/-- The pullback of a continuous character of `Ω ≃ₐ[K] Ω` that is trivial on absolute
inertia is the unramified character given by its value at the projected geometric
Frobenius. -/
theorem galoisUnramifiedCharacter_comp_localProjection (χ : galoisUnramifiedCharacters K Ω) :
    (χ : Γ →ₜ* ℂˣ).comp (localProjection K Ω) =
      localUnramifiedCharacter K Ω (χ.val (localProjection K Ω (localGeometricFrobenius K Ω))) := by
  have h := localUnramifiedCharacter_eq_of_on_inertia K Ω
    ((χ : Γ →ₜ* ℂˣ).comp (localProjection K Ω)).toMonoidHom fun w hw =>
      χ.property ⟨_, localProjection_mem_absoluteInertia K Ω hw⟩
  ext w
  exact congrArg (fun f : localWeilGroup K Ω →* ℂˣ => (f w : ℂ)) h.symm

/-- Twisting a Galois class by an unramified Galois character twists its pullback by the
corresponding Weil unramified character. -/
theorem IsGaloisPullbackBasis.twist {b : Weil.IrreducibleBasis.{uΩ, uV} (localWeilGroup K Ω)}
    {c : Weil.IrreducibleBasis.{uΩ, uV} Γ} (h : IsGaloisPullbackBasis K Ω b c)
    (χ : galoisUnramifiedCharacters K Ω) :
    IsGaloisPullbackBasis K Ω
      (Weil.twistBasisEquiv (localUnramifiedCharacter K Ω
        (χ.val (localProjection K Ω (localGeometricFrobenius K Ω)))) b)
      (Weil.twistBasisEquiv χ.val c) := by
  rw [IsGaloisPullbackBasis, Weil.underlyingClass_twistBasisEquiv,
    Weil.underlyingClass_twistBasisEquiv, restrictClass_twistClass, ← h,
    ← galoisUnramifiedCharacter_comp_localProjection]
  rfl

/-- A continuous character of the Weil group with finite image is the pullback of a
continuous character of `Ω ≃ₐ[K] Ω`. -/
theorem exists_galoisCharacter_comp_eq (ψ : localWeilGroup K Ω →ₜ* ℂˣ)
    (hψ : (Set.range ψ).Finite) :
    ∃ χ : Γ →ₜ* ℂˣ, χ.comp (localProjection K Ω) = ψ := by
  have := absoluteGalois_nonarchimedean K Ω
  have := absoluteGalois_t2Space K Ω
  let ρ : Representation ℂ (localWeilGroup K Ω) ℂ :=
    Langlands.characterRepresentation ψ.toMonoidHom
  have hρ : ∀ w v, ρ w v = (ψ w : ℂ) * v := fun _ _ => rfl
  have hcont : Continuous (fun w => (ρ w).toContinuousLinearMap) := by
    have heq : (fun w => (ρ w).toContinuousLinearMap) =
        fun w => (ψ w : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
      funext w
      ext
      simp [hρ]
    rw [heq]
    exact (Units.continuous_val.comp ψ.continuous).smul continuous_const
  have hfin : (Set.range ρ).Finite := by
    refine (hψ.image fun u : ℂˣ => ((u : ℂ) • (1 : Module.End ℂ ℂ))).subset ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨ψ w, ⟨w, rfl⟩, rfl⟩
  obtain ⟨τ, ⟨hτc, hτr⟩, -⟩ :=
    (Weil.finiteImageExtension Γ (localResidueDegree K Ω) (localResidueDegree_surjective K Ω)
      ℂ ρ hcont).mp hfin
  have hlin : ∀ (g : Γ) (c : ℂ), τ g c = c * τ g 1 := by
    intro g c
    simpa [smul_eq_mul] using (τ g).map_smul c 1
  let f : Γ →* ℂ :=
    { toFun := fun g => τ g 1
      map_one' := by simp
      map_mul' := fun a b => by
        change τ (a * b) 1 = τ a 1 * τ b 1
        rw [map_mul, Module.End.mul_apply, hlin a (τ b 1), mul_comm] }
  have hf : Continuous fun g : Γ => τ g 1 := by
    have := hτc.clm_apply (continuous_const (y := (1 : ℂ)))
    simpa using this
  refine ⟨{ toMonoidHom := f.toHomUnits
            continuous_toFun := Units.continuous_iff.mpr ⟨hf, ?_⟩ }, ?_⟩
  · refine (hf.comp continuous_inv).congr fun g => ?_
    change τ g⁻¹ 1 = (((f.toHomUnits g)⁻¹ : ℂˣ) : ℂ)
    rw [← map_inv]
    rfl
  · ext w
    change τ (localProjection K Ω w) 1 = (ψ w : ℂ)
    have := DFunLike.congr_fun hτr w
    change τ (localProjection K Ω w) = ρ w at this
    rw [this, hρ, mul_one]

/-- If a Weil pullback differs from another by an unramified twist, the twisting parameter is
a root of unity. -/
theorem exists_pow_eq_one_of_twist_restrict (B B' : FiniteRepresentation.{0, uΩ, uV} ℂ Γ)
    (hB : B.IsContinuous) (hB' : B'.IsContinuous) (hBi : B.IsIrreducible) (z : ℂˣ)
    (e : FiniteRepresentation.Equiv (restrict (localProjection K Ω).toMonoidHom B')
      (FiniteRepresentation.twist (localUnramifiedCharacter K Ω z).toMonoidHom
        (restrict (localProjection K Ω).toMonoidHom B))) :
    ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  have := absoluteGalois_nonarchimedean K Ω
  obtain ⟨m, hm, h1, h1'⟩ := exists_pow_eq_one_of_finite_range B.representation
    B'.representation (finite_range_of_isContinuous B hB) (finite_range_of_isContinuous B' hB')
    (localProjection K Ω (localGeometricFrobenius K Ω))
  refine ⟨m, hm, ?_⟩
  have := nontrivial_of_isIrreducible B.representation hBi
  obtain ⟨v, hv⟩ := exists_ne (0 : B)
  let w := localGeometricFrobenius K Ω ^ m
  have hpw : localProjection K Ω w = localProjection K Ω (localGeometricFrobenius K Ω) ^ m :=
    map_pow _ _ _
  have hzw : localUnramifiedCharacter K Ω z w = z ^ m := by
    rw [map_pow, localUnramifiedCharacter_geometricFrobenius]
  have hint := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap w
    (e.symm v)
  change e (B'.representation (localProjection K Ω w) (e.symm v)) =
    ((localUnramifiedCharacter K Ω z w : ℂˣ) : ℂ) •
      B.representation (localProjection K Ω w) (e (e.symm v)) at hint
  rw [hpw, h1, h1', hzw] at hint
  have hev : e (e.symm v) = v := EquivLike.apply_inv_apply e v
  change e (e.symm v) = ((z ^ m : ℂˣ) : ℂ) • e (e.symm v) at hint
  rw [hev] at hint
  have h0 : (((z ^ m : ℂˣ) : ℂ) - 1) • v = 0 := by
    rw [sub_smul, one_smul]
    exact sub_eq_zero.mpr hint.symm
  rcases smul_eq_zero.mp h0 with hz | hz
  · exact Units.ext (sub_eq_zero.mp hz)
  · exact absurd hz hv

/-- If two Weil pullbacks differ by an unramified twist, their Galois classes differ by an
unramified Galois character whose pullback is that twist (Henniart 1988, Proposition 2.2(a)
and §4.2). -/
theorem IsGaloisPullbackBasis.exists_galoisUnramified_of_twist
    {b b' : Weil.IrreducibleBasis.{uΩ, uV} (localWeilGroup K Ω)}
    {c c' : Weil.IrreducibleBasis.{uΩ, uV} Γ} (h : IsGaloisPullbackBasis K Ω b c)
    (h' : IsGaloisPullbackBasis K Ω b' c') (z : ℂˣ)
    (hz : b' = Weil.twistBasisEquiv (localUnramifiedCharacter K Ω z) b) :
    ∃ χ : galoisUnramifiedCharacters K Ω,
      (χ : Γ →ₜ* ℂˣ).comp (localProjection K Ω) = localUnramifiedCharacter K Ω z ∧
        c' = Weil.twistBasisEquiv χ.val c := by
  obtain ⟨B, hBc, hBi, hB⟩ := exists_classOf_eq_underlyingClass c
  obtain ⟨B', hB'c, -, hB'⟩ := exists_classOf_eq_underlyingClass c'
  have hclass : classOf (restrict (localProjection K Ω).toMonoidHom B') =
      classOf (FiniteRepresentation.twist (localUnramifiedCharacter K Ω z).toMonoidHom
        (restrict (localProjection K Ω).toMonoidHom B)) := by
    change restrictClass (localProjection K Ω).toMonoidHom (classOf B') =
      twistClass (localUnramifiedCharacter K Ω z).toMonoidHom
        (restrictClass (localProjection K Ω).toMonoidHom (classOf B))
    rw [hB, hB', ← h, ← h', hz, Weil.underlyingClass_twistBasisEquiv]
  obtain ⟨e⟩ := (classOf_eq_iff _ _).mp hclass
  obtain ⟨m, hm, hzm⟩ := exists_pow_eq_one_of_twist_restrict K Ω B B' hBc hB'c hBi z e
  have hfin : (Set.range (localUnramifiedCharacter K Ω z)).Finite := by
    have : NeZero m := ⟨hm.ne'⟩
    have hS : ({ζ : ℂˣ | ζ ^ m = 1} : Set ℂˣ).Finite := by
      have hset : ({ζ : ℂˣ | ζ ^ m = 1} : Set ℂˣ) =
          ((rootsOfUnity m ℂ : Subgroup ℂˣ) : Set ℂˣ) := by
        ext ζ
        simp [mem_rootsOfUnity]
      rw [hset]
      exact Set.finite_coe_iff.mp (inferInstanceAs (Finite (rootsOfUnity m ℂ)))
    refine hS.subset ?_
    rintro _ ⟨w, rfl⟩
    change (z ^ (localDegree K Ω w).toAdd) ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzm, one_zpow]
  obtain ⟨χ, hχ⟩ := exists_galoisCharacter_comp_eq K Ω _ hfin
  have hχi : χ ∈ galoisUnramifiedCharacters K Ω := by
    intro i
    change (χ.comp (localProjection K Ω)) (localInertiaInclusion K Ω i) = 1
    rw [hχ]
    exact localUnramifiedCharacter_on_inertia K Ω z (localInertiaInclusion_mem K Ω i)
  refine ⟨⟨χ, hχi⟩, hχ, ?_⟩
  apply galoisBasis_eq_of_restrictClass_eq K Ω
  rw [← h', Weil.underlyingClass_twistBasisEquiv, restrictClass_twistClass, ← h, hz,
    Weil.underlyingClass_twistBasisEquiv]
  have hχ' : (χ : Γ →* ℂˣ).comp (localProjection K Ω).toMonoidHom =
      (localUnramifiedCharacter K Ω z).toMonoidHom :=
    congrArg ContinuousMonoidHom.toMonoidHom hχ
  exact congrArg (fun φ => twistClass φ (Weil.underlyingClass (localWeilGroup K Ω) b)) hχ'.symm

end Local

end Langlands.Henniart.LocalNumerical

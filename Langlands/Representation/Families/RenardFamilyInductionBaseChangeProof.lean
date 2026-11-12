import Langlands.Representation.Families.RenardFamilyParabolicStatements
import Langlands.Representation.Families.RenardFamilyFixedTensorProof
import Langlands.Representation.Induction.FixedVectorModel
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Twist.SmoothProof
import Langlands.Representation.Exponents.ArbitraryParabolicFiniteSupportReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Renard VI.8.2: base change commutes with induction of families

Smooth induction from a closed subgroup with compact coset space commutes with base change
of the coefficient ring (`exists_inducedBaseChangeEquiv`). Applied to a represented
parabolic, whose quotient `P(F)\G(F)` is compact by the published structural theorems,
this proves the VI.8.2 Proposition `InductionBaseChangeStatement` (`inductionBaseChange`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

universe u uB uC uG uE uH uV

section CompactOpen

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- Every open subgroup of a locally compact nonarchimedean group contains a compact open
subgroup. -/
theorem exists_isCompact_openSubgroup_subset (L : OpenSubgroup G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ L := by
  obtain ⟨S, hS, hSn⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨K, hK⟩ := NonarchimedeanGroup.is_nonarchimedean (S ∩ (L : Set G))
    (Filter.inter_mem hSn L.mem_nhds_one)
  exact ⟨K, hS.of_isClosed_subset K.isClosed (hK.trans Set.inter_subset_left),
    hK.trans Set.inter_subset_right⟩

/-- A smooth vector is fixed by a compact open subgroup. -/
theorem exists_isCompact_fixedVectors {R : Type uB} [CommRing R] {V : Type uV} [AddCommGroup V]
    [Module R V] {ρ : Representation R G V} {v : V} (hv : IsSmoothVector ρ v) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ v ∈ fixedVectors ρ K.toSubgroup := by
  obtain ⟨L, hL⟩ := hv
  obtain ⟨K, hKc, hKL⟩ := exists_isCompact_openSubgroup_subset L
  exact ⟨K, hKc, fun k => hL ⟨k, hKL k.2⟩⟩

omit [LocallyCompactSpace G] in
/-- For a closed subgroup `P` and a compact open `K`, the subgroup `P ∩ i K i⁻¹` of `P` is
compact. -/
theorem isCompact_conjOpenSubgroup {P : Subgroup G} (hP : IsClosed (P : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (i : G) :
    IsCompact ((Induction.conjOpenSubgroup P K i : OpenSubgroup P) : Set P) := by
  have hS : IsCompact ((fun k => i * k * i⁻¹) '' (K : Set G)) :=
    hK.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hset : ((Induction.conjOpenSubgroup P K i : OpenSubgroup P) : Set P) =
      Subtype.val ⁻¹' ((fun k => i * k * i⁻¹) '' (K : Set G)) := by
    ext p
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_image]
    rw [Induction.mem_conjOpenSubgroup]
    constructor
    · intro h
      exact ⟨_, h, by group⟩
    · rintro ⟨k, hk, he⟩
      rw [← he]
      simpa [mul_assoc] using hk
  rw [hset]
  exact hP.isClosedEmbedding_subtypeVal.isCompact_preimage hS

end CompactOpen

section BaseChangeTensor

variable {B : Type uB} [CommRing B] (C : Type uC) [CommRing C] [Algebra B C]
  {H : Type uH} [Group H] {V : Type uV} [AddCommGroup V] [Module B V]

/-- The base change of a family acts on `C ⊗[B] V` as the tensor product with the trivial
action on `C`. -/
theorem tprod_trivial_apply (ρ : Representation B H V) (h : H) (x : C ⊗[B] V) :
    (Representation.trivial B H C).tprod ρ h x = baseChange C ρ h x := by
  induction x using TensorProduct.inductionOn with
  | tmul c v => rfl
  | add x z hx hz => rw [map_add, map_add, hx, hz]

/-- A `C`-linear action agreeing with `1 ⊗ ρ` on pure tensors is the tensor product with the
trivial action. -/
theorem tprod_trivial_apply_of (ρ : Representation B H V)
    (ρC : Representation C H (C ⊗[B] V))
    (hρC : ∀ (h : H) (c : C) (v : V), ρC h (c ⊗ₜ v) = c ⊗ₜ ρ h v) (h : H) (x : C ⊗[B] V) :
    (Representation.trivial B H C).tprod ρ h x = ρC h x := by
  induction x using TensorProduct.inductionOn with
  | tmul c v => exact (hρC h c v).symm
  | add x z hx hz => rw [map_add, map_add, hx, hz]

/-- The image of `C ⊗[B] V^K` in `C ⊗[B] V` is fixed by `K` under base change. -/
theorem lTensor_subtype_mem_fixedVectors (ρ : Representation B H V) (K : Subgroup H)
    (y : C ⊗[B] fixedVectors ρ K) :
    (fixedVectors ρ K).subtype.lTensor C y ∈ fixedVectors (baseChange C ρ) K := by
  induction y using TensorProduct.inductionOn with
  | tmul c v =>
    intro k
    exact congrArg (c ⊗ₜ[B] ·) (v.2 k)
  | add y z hy hz => rw [map_add]; exact add_mem hy hz

/-- Twisting by a constant character commutes with base change. -/
theorem twist_constantCharacter_baseChange_tmul [Algebra ℂ B] [Algebra ℂ C]
    [IsScalarTower ℂ B C] (ψ : H →* ℂˣ) (ρ : Representation B H V) (h : H) (c : C) (v : V) :
    Langlands.twist (constantCharacter C ψ) (baseChange C ρ) h (c ⊗ₜ[B] v) =
      c ⊗ₜ[B] Langlands.twist (constantCharacter B ψ) ρ h v := by
  change algebraMap ℂ C (ψ h : ℂ) • (c ⊗ₜ[B] ρ h v) =
    c ⊗ₜ[B] (algebraMap ℂ B (ψ h : ℂ) • ρ h v)
  rw [TensorProduct.tmul_smul, IsScalarTower.algebraMap_apply ℂ B C, algebraMap_smul]

/-- Base change preserves smoothness. -/
theorem isSmooth_baseChange [TopologicalSpace H] (ρ : Representation B H V) (hρ : IsSmooth ρ) :
    IsSmooth (baseChange C ρ) := by
  intro x
  obtain ⟨K, hK⟩ := trivialTensor_isSmooth (E := C) ρ hρ x
  refine ⟨K, fun k => ?_⟩
  have := hK k
  change (Representation.trivial B H C).tprod ρ k x = x at this
  change baseChange C ρ k x = x
  rwa [← tprod_trivial_apply]

end BaseChangeTensor

section InductionBaseChange

variable {B : Type uB} [CommRing B] (C : Type uC) [CommRing C] [Algebra B C]
  {G : Type uG} [Group G] [TopologicalSpace G]
  (P : Subgroup G) {E : Type uE} [AddCommGroup E] [Module B E] (τ : Representation B P E)

/-- Evaluation of smooth induced functions at a point, as a linear map. -/
def inducedEval (g : G) : Induction.SmoothFunctions P τ →ₗ[B] E where
  toFun f := Induction.eval P τ f g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The functions `g ↦ (1 ⊗ ev_g)(x)` attached to tensors `x`, formula (VI.8.2.2). -/
def inducedBaseChangePi : C ⊗[B] Induction.SmoothFunctions P τ →ₗ[C] (G → C ⊗[B] E) :=
  LinearMap.pi fun g => (inducedEval P τ g).baseChange C

@[simp] theorem inducedBaseChangePi_apply (x : C ⊗[B] Induction.SmoothFunctions P τ) (g : G) :
    inducedBaseChangePi C P τ x g = (inducedEval P τ g).baseChange C x :=
  rfl

theorem inducedBaseChangePi_tmul (c : C) (f : Induction.SmoothFunctions P τ) (g : G) :
    inducedBaseChangePi C P τ (c ⊗ₜ f) g = c ⊗ₜ Induction.eval P τ f g :=
  rfl

variable {C P τ}

theorem inducedBaseChangePi_covariant (τC : Representation C P (C ⊗[B] E))
    (hτC : ∀ (p : P) (c : C) (v : E), τC p (c ⊗ₜ v) = c ⊗ₜ τ p v)
    (x : C ⊗[B] Induction.SmoothFunctions P τ) (p : P) (y : G) :
    inducedBaseChangePi C P τ x ((p : G) * y) = τC p (inducedBaseChangePi C P τ x y) := by
  induction x using TensorProduct.inductionOn with
  | tmul c f =>
    rw [inducedBaseChangePi_tmul, inducedBaseChangePi_tmul, hτC, Induction.eval_covariant]
  | add x z hx hz => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hz, map_add]

variable (C P τ)

theorem inducedBaseChangePi_exists_openSubgroup (x : C ⊗[B] Induction.SmoothFunctions P τ) :
    ∃ K : OpenSubgroup G, ∀ (k : K) (y : G),
      inducedBaseChangePi C P τ x (y * k) = inducedBaseChangePi C P τ x y := by
  induction x using TensorProduct.inductionOn with
  | tmul c f =>
    obtain ⟨K, hK⟩ := f.property
    refine ⟨K, fun k y => ?_⟩
    rw [inducedBaseChangePi_tmul, inducedBaseChangePi_tmul]
    exact congrArg (fun F : Induction.EquivariantFunctions P τ => c ⊗ₜ[B] F.1 y) (hK ⟨k, k.2⟩)
  | add x z hx hz =>
    obtain ⟨K, hK⟩ := hx
    obtain ⟨L, hL⟩ := hz
    refine ⟨K ⊓ L, fun k y => ?_⟩
    rw [map_add, Pi.add_apply, Pi.add_apply, hK ⟨k, k.2.1⟩, hL ⟨k, k.2.2⟩]

variable {C P τ}

/-- The base-change comparison `C ⊗[B] i(E) → i(C ⊗[B] E)`, `c ⊗ f ↦ (g ↦ c ⊗ f(g))`. -/
def inducedBaseChange (τC : Representation C P (C ⊗[B] E))
    (hτC : ∀ (p : P) (c : C) (v : E), τC p (c ⊗ₜ v) = c ⊗ₜ τ p v) :
    C ⊗[B] Induction.SmoothFunctions P τ →ₗ[C] Induction.SmoothFunctions P τC where
  toFun x := Induction.smoothFunctionOf P τC (inducedBaseChangePi C P τ x)
    (inducedBaseChangePi_covariant τC hτC x)
    (inducedBaseChangePi_exists_openSubgroup C P τ x).choose
    (inducedBaseChangePi_exists_openSubgroup C P τ x).choose_spec
  map_add' x z := Subtype.ext (Subtype.ext (map_add (inducedBaseChangePi C P τ) x z))
  map_smul' c x := Subtype.ext (Subtype.ext (map_smul (inducedBaseChangePi C P τ) c x))

variable (τC : Representation C P (C ⊗[B] E))
  (hτC : ∀ (p : P) (c : C) (v : E), τC p (c ⊗ₜ v) = c ⊗ₜ τ p v)

@[simp] theorem eval_inducedBaseChange (x : C ⊗[B] Induction.SmoothFunctions P τ) (g : G) :
    Induction.eval P τC (inducedBaseChange τC hτC x) g = (inducedEval P τ g).baseChange C x :=
  rfl

theorem eval_inducedBaseChange_tmul (c : C) (f : Induction.SmoothFunctions P τ) (g : G) :
    Induction.eval P τC (inducedBaseChange τC hτC (c ⊗ₜ f)) g = c ⊗ₜ Induction.eval P τ f g :=
  rfl

variable [IsTopologicalGroup G] in
/-- The comparison intertwines `1 ⊗ i(σ)` with `i(1 ⊗ σ)`. -/
theorem inducedBaseChange_equivariant (g : G) (x : C ⊗[B] Induction.SmoothFunctions P τ) :
    inducedBaseChange τC hτC (baseChange C (Induction.smoothInduced P τ) g x) =
      Induction.smoothInduced P τC g (inducedBaseChange τC hτC x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c f =>
    apply Subtype.ext
    apply Subtype.ext
    funext y
    rfl
  | add x z hx hz => simp only [map_add, hx, hz]

end InductionBaseChange

section Bijective

variable {B : Type uB} [CommRing B] {C : Type uC} [CommRing C] [Algebra B C]
  {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {P : Subgroup G} {E : Type uE} [AddCommGroup E] [Module B E] {τ : Representation B P E}

/-- On `K`-fixed vectors, evaluation on a finite double-coset transversal commutes with
tensoring by `C`: it identifies `C ⊗[B] i(E)^K` with `∏ᵢ C ⊗[B] E^{P ∩ i K i⁻¹}`. -/
theorem exists_lTensor_fixedEvaluation (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (t : Finset G) (hcover : ∀ x : G, ∃ i ∈ t, ∃ p ∈ P, ∃ k ∈ K, x = p * i * k)
    (hdistinct : Function.Injective (fun i : t => DoubleCoset.mk P K.toSubgroup (i : G))) :
    ∃ Θ : C ⊗[B] fixedVectors (Induction.smoothInduced P τ) K.toSubgroup ≃ₗ[C]
        ((i : t) → C ⊗[B] fixedVectors τ (Induction.conjOpenSubgroup P K i).toSubgroup),
      ∀ (y : C ⊗[B] fixedVectors (Induction.smoothInduced P τ) K.toSubgroup) (i : t),
        (fixedVectors τ (Induction.conjOpenSubgroup P K i).toSubgroup).subtype.lTensor C
            (Θ y i) =
          (inducedEval P τ i).lTensor C
            ((fixedVectors (Induction.smoothInduced P τ) K.toSubgroup).subtype.lTensor C y) := by
  classical
  refine ⟨((Induction.fixedEvaluationEquiv P τ K hK t hcover hdistinct).baseChange B C _ _).trans
    (piRight B C C fun i : t => fixedVectors τ (Induction.conjOpenSubgroup P K i).toSubgroup),
    fun y i => ?_⟩
  induction y using TensorProduct.inductionOn with
  | tmul c f => rfl
  | add y z hy hz => simp only [map_add, Pi.add_apply, hy, hz]

variable [Algebra ℂ B] [LocallyCompactSpace G]

omit [LocallyCompactSpace G] in
/-- By VI.8.1, a `K`-fixed vector of `C ⊗[B] i(E)` lies in the image of `C ⊗[B] i(E)^K`. -/
theorem exists_lTensor_fixedVectors_eq (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    {x : C ⊗[B] Induction.SmoothFunctions P τ}
    (hx : x ∈ fixedVectors (baseChange C (Induction.smoothInduced P τ)) K.toSubgroup) :
    ∃ y, (fixedVectors (Induction.smoothInduced P τ) K.toSubgroup).subtype.lTensor C y = x := by
  have hx' : x ∈ fixedVectors ((Representation.trivial B G C).tprod
      (Induction.smoothInduced P τ)) K.toSubgroup := by
    intro k
    have hk := hx k
    change baseChange C (Induction.smoothInduced P τ) (k : G) x = x at hk
    change (Representation.trivial B G C).tprod (Induction.smoothInduced P τ) (k : G) x = x
    rw [tprod_trivial_apply]
    exact hk
  rw [← (fixedTensorComparison_of_smooth (E := C) _ (Induction.smoothInduced_smooth P τ)
    K hK).2] at hx'
  exact hx'

variable [CompactSpace (Induction.LeftQuotient P)] (τC : Representation C P (C ⊗[B] E))
  (hτC : ∀ (p : P) (c : C) (v : E), τC p (c ⊗ₜ v) = c ⊗ₜ τ p v)

/-- The base-change comparison is injective. -/
theorem inducedBaseChange_injective (hP : IsClosed (P : Set G)) (hτ : IsSmooth τ) :
    Function.Injective (inducedBaseChange τC hτC) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨K, hKc, hxK⟩ := exists_isCompact_fixedVectors
    (isSmooth_baseChange C _ (Induction.smoothInduced_smooth P τ) x)
  obtain ⟨y, rfl⟩ := exists_lTensor_fixedVectors_eq K hKc hxK
  obtain ⟨t, hcover, hdistinct⟩ := Induction.exists_finset_doubleCoset_representatives P K
  obtain ⟨Θ, hΘ⟩ := exists_lTensor_fixedEvaluation (C := C) (τ := τ) K hKc t hcover hdistinct
  have hy : Θ y = 0 := by
    funext i
    apply (fixedTensorComparison_of_smooth (E := C) τ hτ _
      (isCompact_conjOpenSubgroup hP K hKc i)).1
    rw [hΘ, Pi.zero_apply, map_zero]
    exact congrArg (fun f => Induction.eval P τC f i) hx
  rw [Θ.map_eq_zero_iff.mp hy, map_zero]

/-- The base-change comparison is surjective. -/
theorem inducedBaseChange_surjective (hP : IsClosed (P : Set G)) (hτ : IsSmooth τ) :
    Function.Surjective (inducedBaseChange τC hτC) := by
  intro f
  obtain ⟨K, hKc, hfK⟩ := exists_isCompact_fixedVectors (Induction.smoothInduced_smooth P τC f)
  obtain ⟨t, hcover, hdistinct⟩ := Induction.exists_finset_doubleCoset_representatives P K
  obtain ⟨Θ, hΘ⟩ := exists_lTensor_fixedEvaluation (C := C) (τ := τ) K hKc t hcover hdistinct
  have hz : ∀ i : t, ∃ z,
      (fixedVectors τ (Induction.conjOpenSubgroup P K i).toSubgroup).subtype.lTensor C z =
        Induction.eval P τC f i := by
    intro i
    have hmem := Induction.eval_mem_fixedVectors P τC K i hfK
    have hmem' : Induction.eval P τC f i ∈ fixedVectors
        ((Representation.trivial B P C).tprod τ) (Induction.conjOpenSubgroup P K i).toSubgroup := by
      intro p
      have hp := hmem p
      change τC (p : P) (Induction.eval P τC f i) = Induction.eval P τC f i at hp
      change (Representation.trivial B P C).tprod τ (p : P) (Induction.eval P τC f i) =
        Induction.eval P τC f i
      rw [tprod_trivial_apply_of C τ τC hτC]
      exact hp
    rw [← (fixedTensorComparison_of_smooth (E := C) τ hτ _
      (isCompact_conjOpenSubgroup hP K hKc i)).2] at hmem'
    exact hmem'
  choose z hz using hz
  obtain ⟨x, hxz⟩ : ∃ x, (fixedVectors (Induction.smoothInduced P τ) K.toSubgroup).subtype.lTensor
      C (Θ.symm z) = x := ⟨_, rfl⟩
  refine ⟨x, ?_⟩
  have hx : x ∈ fixedVectors (baseChange C (Induction.smoothInduced P τ)) K.toSubgroup :=
    hxz ▸ lTensor_subtype_mem_fixedVectors C _ _ _
  have hΦ : inducedBaseChange τC hτC x ∈
      fixedVectors (Induction.smoothInduced P τC) K.toSubgroup := by
    intro k
    change Induction.smoothInduced P τC k (inducedBaseChange τC hτC x) = _
    rw [← inducedBaseChange_equivariant]
    exact congrArg _ (hx k)
  have heq : Induction.fixedEvaluation P τC K t ⟨_, hΦ⟩ =
      Induction.fixedEvaluation P τC K t ⟨f, hfK⟩ := by
    funext i
    apply Subtype.ext
    change (inducedEval P τ i).lTensor C x = Induction.eval P τC f i
    rw [← hxz, ← hΘ, LinearEquiv.apply_symm_apply, hz]
  exact congrArg Subtype.val (Induction.fixedEvaluation_injective P τC K t hcover heq)

include hτC in
/-- Base change commutes with smooth induction from a closed subgroup with compact coset
space: the comparison `c ⊗ f ↦ (g ↦ c ⊗ f(g))` is a `G`-equivariant isomorphism. -/
theorem exists_inducedBaseChangeEquiv (hP : IsClosed (P : Set G)) (hτ : IsSmooth τ) :
    ∃ e : C ⊗[B] Induction.SmoothFunctions P τ ≃ₗ[C] Induction.SmoothFunctions P τC,
      (∀ (g : G) (x : C ⊗[B] Induction.SmoothFunctions P τ),
        e (baseChange C (Induction.smoothInduced P τ) g x) =
          Induction.smoothInduced P τC g (e x)) ∧
      ∀ (c : C) (f : Induction.SmoothFunctions P τ) (g : G),
        Induction.eval P τC (e (c ⊗ₜ[B] f)) g = c ⊗ₜ[B] Induction.eval P τ f g :=
  ⟨LinearEquiv.ofBijective (inducedBaseChange τC hτC)
      ⟨inducedBaseChange_injective τC hτC hP hτ, inducedBaseChange_surjective τC hτC hP hτ⟩,
    inducedBaseChange_equivariant τC hτC, eval_inducedBaseChange_tmul τC hτC⟩

end Bijective

section Represented

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance compactReductionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- The inducing representation of a smooth Levi family is smooth. -/
theorem isSmooth_leviInducingRepresentation (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    {B : Type uB} [CommRing B] [Algebra ℂ B]
    {E : Type uE} [AddCommGroup E] [Module B E] (σ : Representation B (rationalPoints M) E)
    (hσ : letI := leviPointTopology l hl; IsSmooth σ) :
    IsSmooth (inducingRepresentation
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (leviImageRepresentation p l hp hl σ)) := by
  let := leviPointTopology l hl
  have h1 : IsSmooth (leviImageRepresentation p l hp hl σ) :=
    isSmooth_comp _ (leviPointsEquiv p l hp hl).symm.continuous hσ
  have h2 := (isSmooth_twist_iff _ _
    (inductionCharacter B _ _
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr
        hmul).levi_le_normalizer).isOpen_ker).mpr h1
  exact isSmooth_comp _ (continuous_projection_pointImage p l r hp hl hr hmul) h2

/-- The inducing representation of the base change acts as `1 ⊗ τ` on pure tensors. -/
theorem leviInducingRepresentation_baseChange_tmul (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    {B : Type uB} [CommRing B] [Algebra ℂ B]
    (C : Type uC) [CommRing C] [Algebra ℂ C] [Algebra B C] [IsScalarTower ℂ B C]
    {E : Type uE} [AddCommGroup E] [Module B E] (σ : Representation B (rationalPoints M) E)
    (q : pointImage p) (c : C) (v : E) :
    inducingRepresentation
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (leviImageRepresentation p l hp hl (baseChange C σ)) q (c ⊗ₜ[B] v) =
    c ⊗ₜ[B] inducingRepresentation
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (leviImageRepresentation p l hp hl σ) q v :=
  twist_constantCharacter_baseChange_tmul C
    (HaarModulus.closedHalfCharacter _
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup) _
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).levi_le_normalizer)
    (leviImageRepresentation p l hp hl σ)
    ((isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).projection q) c v

/-- VI.8.2 for a represented parabolic whose quotient `P(F)\G(F)` is compact. -/
theorem exists_leviInducedBaseChangeEquiv (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    {B : Type uB} [CommRing B] [Algebra ℂ B]
    (C : Type uC) [CommRing C] [Algebra ℂ C] [Algebra B C] [IsScalarTower ℂ B C]
    {E : Type uE} [AddCommGroup E] [Module B E] (σ : Representation B (rationalPoints M) E)
    (hσ : letI := leviPointTopology l hl; IsSmooth σ) :
    ∃ e : C ⊗[B] LeviInduced p l r hp hr hl hmul σ ≃ₗ[C]
        LeviInduced p l r hp hr hl hmul (baseChange C σ),
      (∀ (g : rationalPoints G) (x : C ⊗[B] LeviInduced p l r hp hr hl hmul σ),
        e (baseChange C (leviInducedRepresentation p l r hp hr hl hmul σ) g x) =
          leviInducedRepresentation p l r hp hr hl hmul (baseChange C σ) g (e x)) ∧
      ∀ (c : C) (f : LeviInduced p l r hp hr hl hmul σ) (g : rationalPoints G),
        Induction.eval _ _ (e (c ⊗ₜ[B] f)) g = c ⊗ₜ[B] Induction.eval _ _ f g :=
  exists_inducedBaseChangeEquiv _
    (leviInducingRepresentation_baseChange_tmul p l r hp hl hr hmul C σ)
    (isClosed_pointImage p hp.isClosedSubgroup)
    (isSmooth_leviInducingRepresentation p l r hp hl hr hmul σ hσ)

end Represented

section Statement

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

/-- Renard VI.8.2 Proposition: base change commutes with normalized parabolic induction of
families. -/
theorem inductionBaseChange : InductionBaseChangeStatement.{u, uB, uC, uE} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul B _ _ _ _ _ C _ _ _ _ _ _ E _ _ σ hσ _
  let := compactSpace_leftQuotient_pointImage_of_dynamic parabolicDynamic
    BruhatTits.dynamicParabolicQuotientCompact hG p hp
  exact exists_leviInducedBaseChangeEquiv p l r hp hl hr hmul C σ hσ

end Statement

end Langlands.Renard.AlgebraicFamily

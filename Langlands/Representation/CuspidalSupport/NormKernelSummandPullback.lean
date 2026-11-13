import Langlands.Representation.Induction.CompactAutomorphism
import Langlands.Representation.Induction.OpenAdjunction
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Exponents.SelectedWeightSplitting
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelTwistEquivalenceProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.Category.Twist

/-!
# Pulling back the compact induction of a norm-kernel summand along an automorphism

Let `H` be an open normal subgroup of a topological group `G`, `e` an automorphism of `G`
preserving `H`, `π` a smooth representation of `G` and `ρ ↪ π|_H`. We compare the pullback
along `e` of `Π = c-ind_H^G ρ` with `Π` itself:

* `compactInductionPullbackIsoOfEquiv`: if `ρ ∘ e|_H` is equivalent to an inverse conjugate
  of `ρ`, then `e^* Π ≅ Π`;
* `exists_intertwining_ne_zero_of_pullback_hom`: a nonzero map `e^* Π → Π` gives a nonzero
  `H`-map `ρ ∘ e|_H → π|_H`;
* `exists_restriction_intertwining_ne_zero`: if moreover `(π ∘ e)|_H` is semisimple, this
  gives a nonzero `H`-map `(π ∘ e)|_H → π|_H`.

For the rational points of a connected reductive group and its common norm kernel, with
`π` and `ρ` irreducible, the orbit statement (Renard VI.3.2(i)), the finite restriction
statement (VI.3.2(ii)) and the twist equivalence (VI.3.2(iii)) turn these into:

* `nonempty_pullback_rationalNormKernelSummandInduction_iso`: if `e^* π` is an unramified
  twist of `π`, then `e^* Π ≅ Π`;
* `exists_pullback_iso_twist_of_hom_ne_zero`: if there is a nonzero map `e^* Π → Π`, then
  `e^* π` is an unramified twist of `π`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uG uV uF

section Algebra

variable {k : Type*} [Field k] {Γ : Type*} [Monoid Γ] {V : Type*} [AddCommGroup V]
  [Module k V] {W : Type*} [AddCommGroup W] [Module k W]

/-- An injective intertwiner identifies its source with its range. -/
def intertwiningRangeEquiv {σ : Representation k Γ V} {τ : Representation k Γ W}
    (J : σ.IntertwiningMap τ) (hJ : Function.Injective J) :
    σ.Equiv J.range.toRepresentation :=
  Representation.Equiv.mk (LinearEquiv.ofInjective J.toLinearMap hJ) fun g => by
    ext w
    exact Representation.IntertwiningMap.isIntertwining _ _ J g w

theorem intertwiningRangeEquiv_apply {σ : Representation k Γ V} {τ : Representation k Γ W}
    (J : σ.IntertwiningMap τ) (hJ : Function.Injective J) (v : V) :
    ((intertwiningRangeEquiv J hJ v : J.range.toSubmodule) : W) = J v :=
  rfl

/-- Irreducibility is invariant under equivalence of representations. -/
theorem isIrreducible_of_representationEquiv {σ : Representation k Γ V} {τ : Representation k Γ W}
    (E : σ.Equiv τ) (hσ : σ.IsIrreducible) : τ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at hσ ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule σ τ E.toIntertwiningMap)
    E.bijective).mp hσ

/-- In a semisimple representation, an intertwiner out of a subrepresentation embedded by an
injective intertwiner `J` extends along `J`: a nonzero intertwiner `T` out of the source of
`J` gives a nonzero intertwiner out of the ambient representation. -/
theorem exists_intertwining_ne_zero_of_semisimple {U : Type*} [AddCommGroup U] [Module k U]
    {σ : Representation k Γ V} {τ : Representation k Γ W} {υ : Representation k Γ U}
    (hτ : Representation.IsSemisimpleRepresentation τ)
    (J : σ.IntertwiningMap τ) (hJ : Function.Injective J)
    (T : σ.IntertwiningMap υ) (hT : T ≠ 0) :
    ∃ U' : τ.IntertwiningMap υ, U' ≠ 0 := by
  obtain ⟨S', hS⟩ := exists_isCompl J.range
  have hS' : IsCompl J.range.toSubmodule S'.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule (disjoint_iff.mp hS.disjoint)
    · rw [codisjoint_iff]
      exact congrArg Subrepresentation.toSubmodule (codisjoint_iff.mp hS.codisjoint)
  let p := Langlands.subrepresentationProjection J.range S' hS'
  let r := (intertwiningRangeEquiv J hJ).symm
  refine ⟨T.comp (r.toIntertwiningMap.comp p), fun h0 => hT ?_⟩
  ext v
  have hmem : J v ∈ J.range.toSubmodule := LinearMap.mem_range_self J.toLinearMap v
  have hp : p (J v) = intertwiningRangeEquiv J hJ v := by
    apply Subtype.ext
    rw [subrepresentationProjection_apply, intertwiningRangeEquiv_apply,
      Submodule.projection_apply_of_mem_left hS' hmem]
  have h1 := congrArg (fun φ : τ.IntertwiningMap υ => φ (J v)) h0
  simp only [Representation.IntertwiningMap.comp_apply, Representation.IntertwiningMap.coe_zero,
    Pi.zero_apply] at h1
  rw [hp] at h1
  change T (r (intertwiningRangeEquiv J hJ v)) = 0 at h1
  rw [show r (intertwiningRangeEquiv J hJ v) = v from
    (intertwiningRangeEquiv J hJ).symm_apply_apply v] at h1
  simpa using h1

end Algebra

section General

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Inverse conjugation `x ↦ g⁻¹ x g`, as a topological group automorphism. -/
def inverseConjugation (g : G) : G ≃ₜ* G where
  toFun x := g⁻¹ * x * g
  invFun x := g * x * g⁻¹
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const

@[simp]
theorem inverseConjugation_apply (g x : G) : inverseConjugation g x = g⁻¹ * x * g :=
  rfl

/-- Acting by `g` identifies the pullback along inverse conjugation by `g` with the original
smooth representation. -/
def pullbackInverseConjugationIso (g : G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    SmoothRep.pullback (inverseConjugation g) A ≅ A :=
  SmoothRep.mkIso
    { toLinearMap := A.representation g
      invFun := A.representation g⁻¹
      left_inv := fun v => by
        change (A.representation g⁻¹ * A.representation g) v = v
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := fun v => by
        change (A.representation g * A.representation g⁻¹) v = v
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl
      isIntertwining' := fun h => by
        change A.representation g * A.representation (g⁻¹ * h * g) =
          A.representation h * A.representation g
        rw [← map_mul, ← map_mul]
        congr 1
        group }

variable (H : Subgroup G) [H.Normal]

theorem inverseConjugation_mem_iff (g x : G) : inverseConjugation g x ∈ H ↔ x ∈ H := by
  constructor
  · intro hx
    have := Subgroup.Normal.conj_mem inferInstance _ hx g
    simpa [mul_assoc] using this
  · intro hx
    exact Subgroup.Normal.conj_mem' inferInstance _ hx g

/-- Pulling compact induction back along an automorphism `e` preserving `H` is compact
induction of the inducing representation pulled back along `e|_H` (precomposition by `e`). -/
def compactInductionPullbackIso (e : G ≃ₜ* G) (he : ∀ x, e x ∈ H ↔ x ∈ H)
    (σ : Rep.{uV} ℂ H) :
    SmoothRep.pullback e ((Induction.compactInductionFunctor H).obj σ) ≅
      (Induction.compactInductionFunctor H).obj
        (Rep.of (Induction.automorphismInducing H e he σ.ρ)) :=
  SmoothRep.mkIso (Induction.precomposeCompactInducedEquiv H e he σ.ρ)

/-- Compact induction of an inverse conjugate of `σ` is isomorphic to compact induction
of `σ`. -/
def compactInductionInverseConjugateIso (g : G) (σ : Rep.{uV} ℂ H) :
    (Induction.compactInductionFunctor H).obj
        (Rep.of (σ.ρ.comp (SmoothRep.normalSubgroupInverseConjugation H g).toMonoidHom)) ≅
      (Induction.compactInductionFunctor H).obj σ :=
  (Induction.compactInductionFunctor H).mapIso
      (Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ σ) fun _ => rfl)) ≪≫
    (compactInductionPullbackIso H (inverseConjugation g) (inverseConjugation_mem_iff H g)
      σ).symm ≪≫
    pullbackInverseConjugationIso g _

/-- If the pullback of `σ` along `e|_H` is equivalent to the inverse conjugate of `σ` by
`g`, then the pullback of `c-ind_H^G σ` along `e` is isomorphic to `c-ind_H^G σ`. -/
def compactInductionPullbackIsoOfEquiv (e : G ≃ₜ* G) (he : ∀ x, e x ∈ H ↔ x ∈ H)
    (σ : Rep.{uV} ℂ H) (g : G)
    (E : (Induction.automorphismInducing H e he σ.ρ).Equiv
      (σ.ρ.comp (SmoothRep.normalSubgroupInverseConjugation H g).toMonoidHom)) :
    SmoothRep.pullback e ((Induction.compactInductionFunctor H).obj σ) ≅
      (Induction.compactInductionFunctor H).obj σ :=
  compactInductionPullbackIso H e he σ ≪≫
    (Induction.compactInductionFunctor H).mapIso (Rep.mkIso E) ≪≫
    compactInductionInverseConjugateIso H g σ

/-- Evaluation at `x` followed by `j` and `π(x⁻¹)`: the `H`-intertwiner
`F ↦ π(x⁻¹) j(F(x))` from the restriction of `c-ind_H^G σ` to the restriction of `π`. -/
def compactInducedEvaluationMap {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H V)
    (π : Representation ℂ G W) (j : σ.IntertwiningMap (π.comp H.subtype)) (x : G) :
    Representation.IntertwiningMap ((Induction.compactInduced H σ).comp H.subtype)
      (π.comp H.subtype) where
  toFun F := π x⁻¹ (j (Induction.eval H σ F.1 x))
  map_add' F F' := by
    change π x⁻¹ (j (Induction.eval H σ F.1 x + Induction.eval H σ F'.1 x)) = _
    rw [map_add, map_add]
  map_smul' c F := by
    change π x⁻¹ (j (c • Induction.eval H σ F.1 x)) = _
    rw [map_smul, map_smul]
    rfl
  isIntertwining' h := LinearMap.ext fun F => by
    have hk : x * (h : G) * x⁻¹ ∈ H := Subgroup.Normal.conj_mem inferInstance _ h.2 x
    have hcov := F.1.1.2 ⟨x * (h : G) * x⁻¹, hk⟩ x
    rw [Subgroup.coe_subtype, inv_mul_cancel_right] at hcov
    change π x⁻¹ (j (F.1.1.1 (x * (h : G)))) = π h (π x⁻¹ (j (F.1.1.1 x)))
    rw [hcov, Representation.IntertwiningMap.isIntertwining]
    change π x⁻¹ (π (x * (h : G) * x⁻¹) (j (F.1.1.1 x))) = π h (π x⁻¹ (j (F.1.1.1 x)))
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group

theorem compactInducedEvaluationMap_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H V)
    (π : Representation ℂ G W) (j : σ.IntertwiningMap (π.comp H.subtype)) (x : G)
    (F : Induction.CompactFunctions H σ) :
    compactInducedEvaluationMap H σ π j x F = π x⁻¹ (j (Induction.eval H σ F.1 x)) :=
  rfl

/-- A nonzero morphism from the pullback along `e` of `c-ind_H^G ρ` to `c-ind_H^G ρ`, with
`H` open and `j : ρ ↪ π|_H`, gives a nonzero `H`-intertwiner from `ρ ∘ e|_H` to `π|_H`. -/
theorem exists_intertwining_ne_zero_of_pullback_hom (hH : IsOpen (H : Set G))
    (e : G ≃ₜ* G) (he : ∀ x, e x ∈ H ↔ x ∈ H)
    (ρ : SmoothRep.{0, uG, uV} ℂ H) (π : SmoothRep.{0, uG, uV} ℂ G)
    (j : ρ ⟶ SmoothRep.restrictSubgroup H π) (hj : Function.Injective (SmoothRep.hom j))
    (f : SmoothRep.pullback e ((Induction.compactInductionFunctor H).obj (SmoothRep.toRep.obj ρ)) ⟶
      (Induction.compactInductionFunctor H).obj (SmoothRep.toRep.obj ρ))
    (hf : f ≠ 0) :
    ∃ T : (Induction.automorphismInducing H e he ρ.representation).IntertwiningMap
        (π.representation.comp H.subtype), T ≠ 0 := by
  classical
  let σ := ρ.representation
  let σ' := Induction.automorphismInducing H e he σ
  have hσ' : IsSmooth σ' :=
    isSmooth_comp (QuotientIntegration.subgroupAutomorphism H e he).toMonoidHom
      (QuotientIntegration.subgroupAutomorphism H e he).continuous ρ.isSmooth
  let Ψ := Induction.precomposeCompactInducedEquiv H e he σ
  let f' : (Induction.compactInduced H σ').IntertwiningMap (Induction.compactInduced H σ) :=
    (SmoothRep.hom f).comp Ψ.symm.toIntertwiningMap
  let φ := (Induction.resIntertwining H (Induction.compactInduced H σ) f').comp
    (Induction.unitMap H hH σ' hσ')
  have hφ : φ ≠ 0 := by
    intro h0
    apply hf
    have hzero : ∀ F : Induction.CompactFunctions H σ, SmoothRep.hom f F = 0 := by
      intro F
      have h1 := Induction.cosetSum_resIntertwining_comp H hH (Induction.compactInduced H σ)
        σ' f' (Induction.unitMap H hH σ' hσ') (Ψ F)
      rw [Induction.cosetSum_unitMap] at h1
      have h2 : f' (Ψ F) = SmoothRep.hom f F :=
        congrArg (SmoothRep.hom f) (Ψ.symm_apply_apply F)
      rw [← h2, ← h1]
      change Induction.cosetSum H hH (Induction.compactInduced H σ) σ' φ (Ψ F) = 0
      rw [h0, Induction.cosetSum_apply]
      refine (finsum_congr fun q => ?_).trans finsum_zero
      obtain ⟨y, rfl⟩ := Quotient.exists_rep q
      change Induction.compactInduced H σ y⁻¹
        ((0 : σ'.IntertwiningMap ((Induction.compactInduced H σ).comp H.subtype)) _) = 0
      rw [Representation.IntertwiningMap.coe_zero, Pi.zero_apply, map_zero]
    ext F
    exact hzero F
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ (Representation.IntertwiningMap.ext (LinearMap.ext hcon))
  obtain ⟨x, hx⟩ : ∃ x, Induction.eval H σ (φ v).1 x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (Induction.compactFunctions_ext H σ fun x => hcon x)
  refine ⟨(compactInducedEvaluationMap H σ π.representation (SmoothRep.hom j) x).comp φ,
    fun h0 => ?_⟩
  have h1 := congrArg (fun T : σ'.IntertwiningMap (π.representation.comp H.subtype) => T v) h0
  change π.representation x⁻¹ (SmoothRep.hom j (Induction.eval H σ (φ v).1 x)) = 0 at h1
  have hinv : ∀ w, π.representation x (π.representation x⁻¹ w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h2 : SmoothRep.hom j (Induction.eval H σ (φ v).1 x) = 0 :=
    (hinv _).symm.trans ((congrArg (π.representation x) h1).trans (map_zero _))
  exact hx (hj (h2.trans (map_zero _).symm))

omit [IsTopologicalGroup G] [H.Normal] in
/-- With `j : ρ ↪ π|_H` and `(π ∘ e)|_H` semisimple, a nonzero `H`-intertwiner
`ρ ∘ e|_H → π|_H` gives a nonzero `H`-intertwiner `(π ∘ e)|_H → π|_H`. -/
theorem exists_restriction_intertwining_ne_zero
    (e : G ≃ₜ* G) (he : ∀ x, e x ∈ H ↔ x ∈ H)
    (ρ : SmoothRep.{0, uG, uV} ℂ H) (π : SmoothRep.{0, uG, uV} ℂ G)
    (j : ρ ⟶ SmoothRep.restrictSubgroup H π) (hj : Function.Injective (SmoothRep.hom j))
    (hss : Representation.IsSemisimpleRepresentation
      ((π.representation.comp e.toMonoidHom).comp H.subtype))
    (T : (Induction.automorphismInducing H e he ρ.representation).IntertwiningMap
      (π.representation.comp H.subtype)) (hT : T ≠ 0) :
    ∃ U : Representation.IntertwiningMap
        ((π.representation.comp e.toMonoidHom).comp H.subtype)
        (π.representation.comp H.subtype), U ≠ 0 := by
  let J : (Induction.automorphismInducing H e he ρ.representation).IntertwiningMap
      ((π.representation.comp e.toMonoidHom).comp H.subtype) :=
    { toLinearMap := (SmoothRep.hom j).toLinearMap
      isIntertwining' := fun h =>
        (SmoothRep.hom j).isIntertwining' (QuotientIntegration.subgroupAutomorphism H e he h) }
  exact exists_intertwining_ne_zero_of_semisimple hss J hj T hT

end General

section Rational

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G)
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance normKernelSummandPullbackTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance normKernelSummandPullbackTopologicalGroup :
    IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

include hG in
/-- The assertion `w·Π_D ≃ Π_D` for `w ∈ W(D)`, made without proof in the proof of the Lemma of
Renard VI.10.4: let `e` be an automorphism of the rational points preserving the common norm
kernel `⁰G`, `π` irreducible, `ρ` an irreducible summand of `π|_{⁰G}` and
`Π = c-ind_{⁰G}^G ρ`. If `π ∘ e` is an unramified twist of `π`, then the pullback of `Π` along
`e` is isomorphic to `Π`. -/
theorem nonempty_pullback_rationalNormKernelSummandInduction_iso
    (e : GroupScheme.rationalPoints G ≃ₜ* GroupScheme.rationalPoints G)
    (he : ∀ x, e x ∈ rationalCommonNormKernel G ↔ x ∈ rationalCommonNormKernel G)
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) (hπ : π.IsIrreducible)
    (ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G)) (hρ : ρ.IsIrreducible)
    (j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π)
    (hj : Function.Injective (SmoothRep.hom j))
    (χ : unramifiedCharacters
      (fun χ : GroupScheme.rationalCharacters G => (rationalNormCharacters G χ).toMul))
    (hχ : IsOpen (χ.val.toMonoidHom.ker : Set (GroupScheme.rationalPoints G)))
    (ψ : SmoothRep.pullback e π ≅ π.twist χ.val.toMonoidHom hχ) :
    Nonempty (SmoothRep.pullback e (rationalNormKernelSummandInduction G ρ) ≅
      rationalNormKernelSummandInduction G ρ) := by
  classical
  let H := rationalCommonNormKernel G
  have hχH : ∀ h : H, χ.val.toMonoidHom h = 1 := fun h => χ.property h.property
  let J₁ : ρ.representation.IntertwiningMap (π.representation.comp H.subtype) := SmoothRep.hom j
  have hψ : Function.LeftInverse (SmoothRep.hom ψ.inv) (SmoothRep.hom ψ.hom) := fun w =>
    congrArg (fun φ => SmoothRep.hom φ w) ψ.hom_inv_id
  let J₂ : (Induction.automorphismInducing H e he ρ.representation).IntertwiningMap
      (π.representation.comp H.subtype) :=
    { toLinearMap := (SmoothRep.hom ψ.hom).toLinearMap ∘ₗ (SmoothRep.hom j).toLinearMap
      isIntertwining' := fun h => LinearMap.ext fun v => by
        change SmoothRep.hom ψ.hom (SmoothRep.hom j
            (ρ.representation (QuotientIntegration.subgroupAutomorphism H e he h) v)) =
          π.representation h (SmoothRep.hom ψ.hom (SmoothRep.hom j v))
        have h1 := Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom j)
          (QuotientIntegration.subgroupAutomorphism H e he h) v
        have h2 := Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom ψ.hom)
          (h : GroupScheme.rationalPoints G) (SmoothRep.hom j v)
        refine (congrArg (SmoothRep.hom ψ.hom) h1).trans (h2.trans ?_)
        change ((χ.val.toMonoidHom h : ℂˣ) : ℂ) • π.representation h _ = _
        rw [hχH h, Units.val_one, one_smul] }
  have hJ₂ : Function.Injective J₂ := fun v w hvw => hj (hψ.injective hvw)
  have hρ' : (Induction.automorphismInducing H e he ρ.representation).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff ρ.representation
      (QuotientIntegration.subgroupAutomorphism H e he)).mpr hρ
  have hW₁ : J₁.range.toRepresentation.IsIrreducible :=
    isIrreducible_of_representationEquiv (intertwiningRangeEquiv J₁ hj) hρ
  have hW₂ : J₂.range.toRepresentation.IsIrreducible :=
    isIrreducible_of_representationEquiv (intertwiningRangeEquiv J₂ hJ₂) hρ'
  obtain ⟨g, ⟨E₀⟩⟩ := (rationalNormKernelOrbit F G hG π hπ).2.2 J₁.range J₂.range hW₁ hW₂
  let E : (Induction.automorphismInducing H e he ρ.representation).Equiv
      (ρ.representation.comp (SmoothRep.normalSubgroupInverseConjugation H g).toMonoidHom) :=
    (intertwiningRangeEquiv J₂ hJ₂).trans (E₀.symm.trans
      (equivComp (intertwiningRangeEquiv J₁ hj).symm
        (SmoothRep.normalSubgroupInverseConjugation H g).toMonoidHom))
  exact ⟨compactInductionPullbackIsoOfEquiv H e he (SmoothRep.toRep.obj ρ) g E⟩

include hG in
/-- With the data of `nonempty_pullback_rationalNormKernelSummandInduction_iso`, a nonzero
morphism from the pullback of `Π` along `e` to `Π` forces `π ∘ e` to be an unramified twist of
`π`. Renard's proof of the Lemma of VI.10.4 discards the pieces with `w ∉ W(D)` by the block
projection instead; this is the author's replacement for that step. -/
theorem exists_pullback_iso_twist_of_hom_ne_zero
    (e : GroupScheme.rationalPoints G ≃ₜ* GroupScheme.rationalPoints G)
    (he : ∀ x, e x ∈ rationalCommonNormKernel G ↔ x ∈ rationalCommonNormKernel G)
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) (hπ : π.IsIrreducible)
    (ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G))
    (j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π)
    (hj : Function.Injective (SmoothRep.hom j))
    (f : SmoothRep.pullback e (rationalNormKernelSummandInduction G ρ) ⟶
      rationalNormKernelSummandInduction G ρ) (hf : f ≠ 0) :
    ∃ χ : unramifiedCharacters
        (fun χ : GroupScheme.rationalCharacters G => (rationalNormCharacters G χ).toMul),
      ∀ hχ : IsOpen (χ.val.toMonoidHom.ker : Set (GroupScheme.rationalPoints G)),
        Nonempty (SmoothRep.pullback e π ≅ π.twist χ.val.toMonoidHom hχ) := by
  let H := rationalCommonNormKernel G
  obtain ⟨T, hT⟩ := exists_intertwining_ne_zero_of_pullback_hom H
    (isOpen_rationalCommonNormKernel G) e he ρ π j hj f hf
  have hπe : (SmoothRep.pullback e π).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff π.representation e).mpr hπ
  have hss := (rationalNormKernelFiniteRestriction F G hG (SmoothRep.pullback e π) hπe).1
  obtain ⟨U, hU⟩ := exists_restriction_intertwining_ne_zero H e he ρ π j hj hss T hT
  obtain ⟨E⟩ := ((rationalNormKernelTwistEquivalence F G hG (SmoothRep.pullback e π) π
    hπe hπ).2).mpr ⟨U, hU⟩
  obtain ⟨χ, ⟨E'⟩⟩ := ((rationalNormKernelTwistEquivalence F G hG π (SmoothRep.pullback e π)
    hπ hπe).1).mp ⟨E.symm⟩
  exact ⟨χ, fun hχ => ⟨(SmoothRep.mkIso (A := π.twist χ.val.toMonoidHom hχ) E').symm⟩⟩

end Rational

end Langlands.CuspidalSupport

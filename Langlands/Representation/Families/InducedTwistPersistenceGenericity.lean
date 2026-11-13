import Langlands.Representation.Families.InducedTwistPersistencePieces
import Langlands.Representation.Families.InducedTwistExclusionGenericity
import Langlands.Representation.Families.RenardGenericIrreducibilityStatements
import Langlands.Representation.Plancherel.WallUnramifiedTwistSurjectivityStatement
import Langlands.Representation.Plancherel.RationalUnramifiedRestriction
import Langlands.Representation.Families.UnramifiedPolynomialWitness
import Langlands.Representation.CuspidalSupport.RationalNormKernelCentralFiniteIndex
import Langlands.Representation.CuspidalSupport.RationalInertia
import Langlands.Representation.Exponents.MaximalLeviTwistReduction
import Langlands.Representation.Exponents.ExactClassCentralSpectrumProof
import Langlands.Representation.LanglandsClassification.RegularOppositeLanglandsHead

/-! # Genericity at one rank-one wall -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.InducedTwistPersistence

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

section Pullback

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {M L M₁ : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffine M.X.left] [IsAffine L.X.left] [IsAffine M₁.X.left]

local instance persistenceGenericityTopology (H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine H.X.left] : TopologicalSpace (rationalPoints H) := rationalPointTopology k H.X

/-- Regular functions on `X(L)` pull back to regular functions on `X(M)` along
`ψ ↦ φ₀ · ψ|_L · χ₀|_L`. -/
theorem comp_restrict_mul_mem_unramifiedRegularFunctions (f₁ : L ⟶ M) (f₂ : L ⟶ M₁)
    (φ₀ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters L c).toMul))
    (χ₀ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M₁ c).toMul))
    {b : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters L c).toMul) → ℂ}
    (hb : b ∈ Plancherel.unramifiedRegularFunctions
      (fun c => (Plancherel.rationalNormCharacters L c).toMul)) :
    (fun ψ => b (φ₀ * Plancherel.rationalUnramifiedCharacterRestrict f₁ ψ *
        Plancherel.rationalUnramifiedCharacterRestrict f₂ χ₀)) ∈
      Plancherel.unramifiedRegularFunctions
        (fun c => (Plancherel.rationalNormCharacters M c).toMul) := by
  let T : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul) →
      Plancherel.unramifiedCharacters
        (fun c => (Plancherel.rationalNormCharacters L c).toMul) := fun ψ =>
    φ₀ * Plancherel.rationalUnramifiedCharacterRestrict f₁ ψ *
      Plancherel.rationalUnramifiedCharacterRestrict f₂ χ₀
  let pre : (Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters L c).toMul) → ℂ) →ₐ[ℂ]
      (Plancherel.unramifiedCharacters
        (fun c => (Plancherel.rationalNormCharacters M c).toMul) → ℂ) :=
    { toFun := fun b => b ∘ T
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hle : Plancherel.unramifiedRegularFunctions
      (fun c => (Plancherel.rationalNormCharacters L c).toMul) ≤
      (Plancherel.unramifiedRegularFunctions
        (fun c => (Plancherel.rationalNormCharacters M c).toMul)).comap pre := by
    apply Algebra.adjoin_le
    rintro _ ⟨y, rfl⟩
    have heq : pre (Plancherel.unramifiedEvaluation
        (fun c => (Plancherel.rationalNormCharacters L c).toMul) y) =
        algebraMap ℂ _ ((φ₀.val y : ℂ) *
          (χ₀.val (rationalPoints.map f₂ y) : ℂ)) *
          Plancherel.unramifiedEvaluation
            (fun c => (Plancherel.rationalNormCharacters M c).toMul)
            (rationalPoints.map f₁ y) := by
      funext ψ
      change (((φ₀ * Plancherel.rationalUnramifiedCharacterRestrict f₁ ψ *
        Plancherel.rationalUnramifiedCharacterRestrict f₂ χ₀).val y : ℂˣ) : ℂ) =
          (φ₀.val y : ℂ) * (χ₀.val (rationalPoints.map f₂ y) : ℂ) *
            (ψ.val (rationalPoints.map f₁ y) : ℂ)
      simp only [Subgroup.coe_mul, ContinuousMonoidHom.mul_apply, Units.val_mul,
        Plancherel.rationalUnramifiedCharacterRestrict_apply]
      ring
    rw [SetLike.mem_coe, Subalgebra.mem_comap, heq]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Algebra.subset_adjoin ⟨_, rfl⟩)
  exact hle hb

variable [LocallyOfFiniteType M.X.hom] [LocallyOfFiniteType L.X.hom]

/-- **Polynomial pullback across a wall.** If restriction gives a surjection
`X(M) × X(M₁) → X(L)`, then for every nonzero polynomial `f` on `X(L)` and every
`φ₀ ∈ X(L)` there is a nonzero polynomial `g` on `X(M)` such that for every `ψ` off the
zero set of `g` some `χ ∈ X(M₁)` puts `φ₀ · ψ|_L · χ|_L` off the zero set of `f`. -/
theorem exists_polynomial_restrict_mul_mem (hM : IsConnectedReductive M)
    (hL : IsConnectedReductive L) (f₁ : L ⟶ M) (f₂ : L ⟶ M₁)
    (hsurj : ∀ φ : Plancherel.unramifiedCharacters
        (fun c => (Plancherel.rationalNormCharacters L c).toMul),
      ∃ (ψ : Plancherel.unramifiedCharacters
          (fun c => (Plancherel.rationalNormCharacters M c).toMul))
        (χ : Plancherel.unramifiedCharacters
          (fun c => (Plancherel.rationalNormCharacters M₁ c).toMul)),
        φ = Plancherel.rationalUnramifiedCharacterRestrict f₁ ψ *
          Plancherel.rationalUnramifiedCharacterRestrict f₂ χ)
    (φ₀ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters L c).toMul))
    (f : MvPolynomial (Fin (Plancherel.rationalImageRank L)) ℂ) (hf : f ≠ 0) :
    ∃ g : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, g ≠ 0 ∧
      ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hM g,
        ∃ χ : Plancherel.unramifiedCharacters
            (fun c => (Plancherel.rationalNormCharacters M₁ c).toMul),
          φ₀ * Plancherel.rationalUnramifiedCharacterRestrict f₁ ψ *
              Plancherel.rationalUnramifiedCharacterRestrict f₂ χ ∈
            Plancherel.rationalUnramifiedPrincipalOpen L hL f := by
  -- the regular function of `f`
  let F := Plancherel.rationalCanonicalUnramifiedLaurentAlgebraEquiv L hL
    (Renard.AlgebraicFamily.UnramifiedPolynomialWitness.polynomialToLaurent _ f)
  have hF : ∀ φ, φ ∈ Plancherel.rationalUnramifiedPrincipalOpen L hL f ↔ F.val φ ≠ 0 := by
    intro φ
    rw [Plancherel.mem_rationalUnramifiedPrincipalOpen,
      Renard.AlgebraicFamily.UnramifiedPolynomialWitness.canonicalLaurent_eval,
      Renard.AlgebraicFamily.UnramifiedPolynomialWitness.polynomialToLaurent_eval]
  -- a point of the principal open set of `f`, written through the surjection
  obtain ⟨φ₁, hφ₁⟩ := (Plancherel.dense_rationalUnramifiedPrincipalOpen L hL f hf).nonempty
  obtain ⟨ψ₁, χ₁, hψχ⟩ := hsurj (φ₀⁻¹ * φ₁)
  let h : Plancherel.unramifiedRegularFunctions
      (fun c => (Plancherel.rationalNormCharacters M c).toMul) :=
    ⟨_, comp_restrict_mul_mem_unramifiedRegularFunctions f₁ f₂ φ₀ χ₁ F.property⟩
  have hh : ∀ ψ, h.val ψ = F.val (φ₀ * Plancherel.rationalUnramifiedCharacterRestrict f₁ ψ *
      Plancherel.rationalUnramifiedCharacterRestrict f₂ χ₁) := fun ψ => rfl
  have hiff := Renard.AlgebraicFamily.UnramifiedPolynomialWitness.rationalRegularPolynomial_eval_ne_zero_iff
    M hM h
  refine ⟨Renard.AlgebraicFamily.UnramifiedPolynomialWitness.rationalRegularPolynomial M hM h,
    ?_, ?_⟩
  · intro h0
    have e := hiff ψ₁
    rw [h0, map_zero, ne_self_iff_false, false_iff, not_not, hh, mul_assoc, ← hψχ,
      mul_inv_cancel_left] at e
    exact (hF φ₁).mp hφ₁ e
  · intro ψ hψ
    refine ⟨χ₁, (hF _).mpr ?_⟩
    rw [← hh]
    exact (hiff ψ).mp ((Plancherel.mem_rationalUnramifiedPrincipalOpen _ _ _ ψ).mp hψ)

end Pullback

section Divisibility

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {M L : GroupScheme (Spec (CommRingCat.of k))} [IsAffine M.X.left]

local instance persistenceDivisibilityTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology k M.X

/-- **Divisibility.** Let `f : L → M` and `φ : L → L`. If every unramified character `ψ`
of `M(k)` satisfies `ψ(f(φ(x))) = ψ(f(x))` for all `x` in the split component of `L`, then
the same holds for all `x ∈ L(k)`. The ratio of the two sides is trivial on the common norm
kernel of `L(k)` and on the split component, which together have finite index, and the
group of unramified characters of `M(k)` is divisible. -/
theorem unramified_apply_map_eq_of_splitComponent (hM : IsConnectedReductive M)
    (hL : IsConnectedReductive L) (f : L ⟶ M) (φ : L ⟶ L)
    {B : CommGroupScheme (Spec (CommRingCat.of k))} {bL : B.toGrp ⟶ L}
    (hbL : IsSplitComponent bL)
    (hD : ∀ (ψ : Plancherel.unramifiedCharacters
        (fun c => (Plancherel.rationalNormCharacters M c).toMul))
      (a : rationalPoints B.toGrp),
      ψ.val (rationalPoints.map f (rationalPoints.map φ (rationalPoints.map bL a))) =
        ψ.val (rationalPoints.map f (rationalPoints.map bL a)))
    (ψ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul))
    (z : rationalPoints L) :
    ψ.val (rationalPoints.map f (rationalPoints.map φ z)) =
      ψ.val (rationalPoints.map f z) := by
  -- the common norm kernel joined with the split component has finite index
  have hindex : (Plancherel.RenardCartan.splitValuationImage bL).FiniteIndex :=
    Plancherel.RenardCartan.finiteIndex_splitValuationImage_of_injective hL bL hbL
      (GroupScheme.characterRestriction k L hL B bL hbL).1
  have := Plancherel.finite_rationalCentralQuotient bL hbL.isCentralSplitTorus.isCentral hindex
  let H := Plancherel.rationalCommonNormKernel L ⊔ (rationalPoints.map bL).range
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : (rationalPoints.map bL).range.Normal :=
    (rationalPoints.map bL).range.normal_of_le_center hbL.isCentralSplitTorus.range_le_center
  -- an `index`-th root of `ψ`
  obtain ⟨ψ', rfl⟩ := exists_pow_eq_of_mulEquiv
    (Plancherel.rationalCanonicalUnramifiedCharacterCoordinates M hM).toMulEquiv ψ H.index
    Subgroup.FiniteIndex.index_ne_zero
  let α : rationalPoints L →* ℂˣ :=
    ψ'.val.toMonoidHom.comp ((rationalPoints.map f).comp (rationalPoints.map φ))
  let β : rationalPoints L →* ℂˣ := ψ'.val.toMonoidHom.comp (rationalPoints.map f)
  have hH : H ≤ MonoidHom.eqLocus α β := by
    refine sup_le ?_ ?_
    · intro h hh
      have h1 := Plancherel.rationalCommonNormKernel_le_comap f
        (Plancherel.rationalCommonNormKernel_le_comap φ hh)
      have h2 := Plancherel.rationalCommonNormKernel_le_comap f hh
      have e1 : ψ'.val (rationalPoints.map f (rationalPoints.map φ h)) = 1 := ψ'.property h1
      have e2 : ψ'.val (rationalPoints.map f h) = 1 := ψ'.property h2
      change ψ'.val (rationalPoints.map f (rationalPoints.map φ h)) =
        ψ'.val (rationalPoints.map f h)
      rw [e1, e2]
    · rintro _ ⟨a, rfl⟩
      exact hD ψ' a
  have hz : α (z ^ H.index) = β (z ^ H.index) := hH (Subgroup.pow_index_mem H z)
  rw [map_pow, map_pow] at hz
  rw [SubgroupClass.coe_pow, ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.pow_apply]
  exact hz

end Divisibility

section Twist

universe uΓ v₁ v₂ v₃

/-- An irreducible representation over `ℂ` has a nonzero carrier. -/
theorem nontrivial_of_isIrreducible {Γ : Type uΓ} [Group Γ] {W : Type v₃} [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ Γ W} (h : ρ.IsIrreducible) : Nontrivial W := by
  have := (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp h
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ Γ) ρ.asModule

/-- Let `A` and `B` be equivalent to two representations on one space which are the scalar
multiples `a(g) ρ(g)` and `b(g) ρ(g)` of a common representation `ρ`. If `α a = β b`, then
the twist of `A` by `α` is equivalent to the twist of `B` by `β`. -/
def twistEquivOfEquivScalar {Γ : Type uΓ} [Group Γ] [TopologicalSpace Γ]
    {A : SmoothRep.{0, uΓ, v₁} ℂ Γ} {B : SmoothRep.{0, uΓ, v₂} ℂ Γ}
    {W : Type v₃} [AddCommGroup W] [Module ℂ W] {ρa ρb : Representation ℂ Γ W}
    (ρ : Representation ℂ Γ W)
    (EA : A.representation.Equiv ρa) (EB : B.representation.Equiv ρb) (a b : Γ → ℂ)
    (ha : ∀ g w, ρa g w = a g • ρ g w) (hb : ∀ g w, ρb g w = b g • ρ g w)
    (α β : Γ →* ℂˣ) (hα : IsOpen (α.ker : Set Γ)) (hβ : IsOpen (β.ker : Set Γ))
    (h : ∀ g, (α g : ℂ) * a g = β g * b g) :
    (A.twist α hα).representation.Equiv (B.twist β hβ).representation where
  toLinearEquiv := EA.toLinearEquiv.trans EB.toLinearEquiv.symm
  isIntertwining' g := by
    ext v
    have hA : ∀ w, EA.toLinearEquiv (A.representation g w) =
        a g • ρ g (EA.toLinearEquiv w) := fun w =>
      (Representation.IntertwiningMap.isIntertwining _ _ EA.toIntertwiningMap g w).trans
        (ha g _)
    have hB : ∀ w, EB.toLinearEquiv (B.representation g w) =
        b g • ρ g (EB.toLinearEquiv w) := fun w =>
      (Representation.IntertwiningMap.isIntertwining _ _ EB.toIntertwiningMap g w).trans
        (hb g _)
    change EB.toLinearEquiv.symm (EA.toLinearEquiv ((α g : ℂ) • A.representation g v)) =
      (β g : ℂ) • B.representation g (EB.toLinearEquiv.symm (EA.toLinearEquiv v))
    apply EB.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, map_smul, map_smul, hB, LinearEquiv.apply_symm_apply, hA,
      smul_smul, smul_smul, h]

end Twist

section Wall

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {M L M₁ Q₁ V₁ : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffine M.X.left] [IsAffine L.X.left] [IsAffine M₁.X.left] [IsAffineHom M₁.X.hom]

local instance persistenceWallMTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology k M.X

local instance persistenceWallLTopology : TopologicalSpace (rationalPoints L) :=
  rationalPointTopology k L.X

omit [T2Space k] in
/-- Two points with distinct values of one unramified character of `M(k)` give a nonzero
polynomial off whose zero set the two weighted evaluations differ (the published
`exists_polynomial_ne_of_two_points`, for a connected reductive `M` not presented as a
Levi subgroup). -/
theorem exists_polynomial_mul_ne_of_ne (hM : IsConnectedReductive M)
    (g₁ g₂ : rationalPoints M) (c₁ c₂ : ℂˣ)
    (ψ₀ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul))
    (h₀ : (ψ₀.val g₁ : ℂ) ≠ ψ₀.val g₂) :
    ∃ g : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, g ≠ 0 ∧
      ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hM g,
        (c₁ : ℂ) * ψ.val g₁ ≠ (c₂ : ℂ) * ψ.val g₂ := by
  have := hM.smooth
  let ν := fun c : rationalCharacters M => (Plancherel.rationalNormCharacters M c).toMul
  let b : Plancherel.unramifiedRegularFunctions ν :=
    algebraMap ℂ _ (c₁ : ℂ) * Plancherel.unramifiedEvaluationRegular ν g₁ -
      algebraMap ℂ _ (c₂ : ℂ) * Plancherel.unramifiedEvaluationRegular ν g₂
  have hb : ∀ ψ : Plancherel.unramifiedCharacters ν,
      b.val ψ = (c₁ : ℂ) * ψ.val g₁ - (c₂ : ℂ) * ψ.val g₂ := fun ψ => rfl
  have hiff :=
    Renard.AlgebraicFamily.UnramifiedPolynomialWitness.rationalRegularPolynomial_eval_ne_zero_iff
      M hM b
  refine ⟨Renard.AlgebraicFamily.UnramifiedPolynomialWitness.rationalRegularPolynomial M hM b,
    ?_, ?_⟩
  · intro h0
    have e1 := hiff 1
    have e0 := hiff ψ₀
    rw [h0, map_zero, ne_self_iff_false, false_iff, not_not, hb] at e1 e0
    have h1 : ((1 : Plancherel.unramifiedCharacters ν).val g₁ : ℂ) = 1 := rfl
    have h2 : ((1 : Plancherel.unramifiedCharacters ν).val g₂ : ℂ) = 1 := rfl
    rw [h1, h2, mul_one, mul_one, sub_eq_zero] at e1
    rw [e1, ← mul_sub, mul_eq_zero, sub_eq_zero] at e0
    rcases e0 with h | h
    · exact Units.ne_zero c₂ h
    · exact h₀ h
  · intro ψ hψ
    have h := (hiff ψ).mp ((Plancherel.mem_rationalUnramifiedPrincipalOpen _ _ _ ψ).mp hψ)
    rw [hb] at h
    exact sub_ne_zero.mp h

local instance persistenceWallM₁Topology : TopologicalSpace (rationalPoints M₁) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints M₁)] [NonarchimedeanGroup (rationalPoints M₁)]

set_option maxHeartbeats 1000000 in
/-- **Generic irreducibility at one wall, for one element of the normalizer.** Let `Q₁` be a
parabolic of `M₁` with Levi `L`, let `f : L → M`, let `φ` be an automorphism of `L`, and let
`σ` be an irreducible representation of `L(k)`. Assume Renard VI.8.5 and that
`(ψ, χ) ↦ ψ|_L · χ|_L` maps `X(M) × X(M₁)` onto `X(L)`. Then there is a nonzero polynomial
`g` on `X(M)` such that for every `ψ` off its zero set, every irreducible supercuspidal `C`
equivalent to the pullback along `φ` of `σ ⊗ ψ|_L`, sharing an `A_L`-exponent with
`σ ⊗ ψ|_L`, has irreducible induction `i^{M₁}_{Q₁}(C)`. -/
theorem exists_polynomial_isIrreducible_wall
    (hVI : Renard.AlgebraicFamily.GenericInducedIrreducibilityStatement.{u, max u v})
    (hM : IsConnectedReductive M) (hM₁ : IsConnectedReductive M₁)
    (q₁ : Q₁ ⟶ M₁) (l₁ : L ⟶ Q₁) (v₁ : V₁ ⟶ Q₁) (hq₁ : IsParabolicSubgroup q₁)
    (hl₁ : IsRationalLeviSubgroup l₁) (hv₁ : LeviSubgroup.IsGeometricUnipotentRadical v₁)
    (hmulQ₁ : IsIso (subgroupMultiplication l₁ v₁)) (f : L ⟶ M)
    (hsurj : ∀ φ : Plancherel.unramifiedCharacters
        (fun c => (Plancherel.rationalNormCharacters L c).toMul),
      ∃ (ψ : Plancherel.unramifiedCharacters
          (fun c => (Plancherel.rationalNormCharacters M c).toMul))
        (χ : Plancherel.unramifiedCharacters
          (fun c => (Plancherel.rationalNormCharacters M₁ c).toMul)),
        φ = Plancherel.rationalUnramifiedCharacterRestrict f ψ *
          Plancherel.rationalUnramifiedCharacterRestrict (l₁ ≫ q₁) χ)
    (φ : L ≅ L) {B : CommGroupScheme (Spec (CommRingCat.of k))} {bL : B.toGrp ⟶ L}
    (hbL : IsSplitComponent bL)
    (σ : letI := leviPointTopology l₁ hl₁; SmoothRep.{0, u, w} ℂ (rationalPoints L))
    (hσ : letI := leviPointTopology l₁ hl₁; σ.IsIrreducible) :
    haveI := hl₁.isConnectedReductive.isAffineHom
    letI := leviPointTopology l₁ hl₁
    haveI := leviPoints_locallyCompactSpace q₁ l₁ hq₁ hl₁
    haveI := leviPoints_nonarchimedeanGroup q₁ l₁ hq₁ hl₁
    ∃ g : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ, g ≠ 0 ∧
      ∀ ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hM g,
        ∀ (θL : rationalPoints L →* ℂˣ) (hθL : IsOpen (θL.ker : Set (rationalPoints L))),
          (∀ z, (θL z : ℂ) = ψ.val (rationalPoints.map f z)) →
          ∀ C : SmoothRep.{0, u, max u v} ℂ (rationalPoints L), C.IsIrreducible →
            IsSupercuspidal C →
            Nonempty (C.representation.Equiv
              (SmoothRep.pullback (ambientIsoPointsEquiv φ) (σ.twist θL hθL)).representation) →
            ∀ χ : rationalPoints B.toGrp →* ℂˣ,
              IsGeneralizedEigencharacter
                ((σ.twist θL hθL).representation.comp (rationalPoints.map bL)) χ →
              IsGeneralizedEigencharacter (C.representation.comp (rationalPoints.map bL)) χ →
              ((leviInductionFunctor q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁).obj C).IsIrreducible := by
  classical
  have hL : IsConnectedReductive L := hl₁.isConnectedReductive
  have := hL.isAffineHom
  let := leviPointTopology l₁ hl₁
  have := leviPoints_locallyCompactSpace q₁ l₁ hq₁ hl₁
  have := leviPoints_nonarchimedeanGroup q₁ l₁ hq₁ hl₁
  have := hM.smooth
  have := hL.smooth
  let e := ambientIsoPointsEquiv φ
  have hcen : ∀ (a : rationalPoints B.toGrp) (z : rationalPoints L),
      rationalPoints.map bL a * z = z * rationalPoints.map bL a := fun a z =>
    (Subgroup.mem_center_iff.mp (hbL.isCentralSplitTorus.isCentral.map_mem_center a) z).symm
  by_cases hD : ∀ (ψ : Plancherel.unramifiedCharacters
      (fun c => (Plancherel.rationalNormCharacters M c).toMul)) (a : rationalPoints B.toGrp),
      ψ.val (rationalPoints.map f (rationalPoints.map φ.hom (rationalPoints.map bL a))) =
        ψ.val (rationalPoints.map f (rationalPoints.map bL a))
  · -- the twist commutes with the conjugation: VI.8.5 applies along the whole family
    have hA := unramified_apply_map_eq_of_splitComponent hM hL f φ.hom hbL hD
    by_cases hstar : ∃ (ψs : Plancherel.unramifiedCharacters
        (fun c => (Plancherel.rationalNormCharacters M c).toMul))
        (θS : rationalPoints L →* ℂˣ) (hθS : IsOpen (θS.ker : Set (rationalPoints L)))
        (_ : ∀ z, (θS z : ℂ) = ψs.val (rationalPoints.map f z))
        (Cs : SmoothRep.{0, u, max u v} ℂ (rationalPoints L)),
        Cs.IsIrreducible ∧ IsSupercuspidal Cs ∧
          Nonempty (Cs.representation.Equiv
            (SmoothRep.pullback e (σ.twist θS hθS)).representation)
    · obtain ⟨ψs, θS, hθS, hθSψ, Cs, hCs, hscs, ⟨Es⟩⟩ := hstar
      obtain ⟨F, hF, hFirr⟩ := hVI k M₁ hM₁ Q₁ L V₁ q₁ l₁ v₁ hq₁ hl₁ hv₁ hmulQ₁ Cs hCs hscs
      obtain ⟨g, hg, hgψ⟩ := exists_polynomial_restrict_mul_mem hM hL f (l₁ ≫ q₁) hsurj
        (Plancherel.rationalUnramifiedCharacterRestrict f ψs)⁻¹ F hF
      refine ⟨g, hg, ?_⟩
      intro ψ hψ θL hθL hθLψ C hC _ ⟨E⟩ χ _ _
      obtain ⟨χ₁, hχ₁⟩ := hgψ ψ hψ
      have hirr := hFirr _ hχ₁
      let E' := twistEquivOfEquivScalar (SmoothRep.pullback e σ).representation Es E
        (fun z => (θS (e z) : ℂ)) (fun z => (θL (e z) : ℂ)) (fun _ _ => rfl) (fun _ _ => rfl)
        ((Plancherel.rationalUnramifiedCharacterRestrict f ψs)⁻¹ *
          Plancherel.rationalUnramifiedCharacterRestrict f ψ *
          Plancherel.rationalUnramifiedCharacterRestrict (l₁ ≫ q₁) χ₁).val.toMonoidHom
        (leviRestrictedCharacter q₁ l₁
          (χ₁ : rationalPoints M₁ →ₜ* ℂˣ).toMonoidHom)
        (Plancherel.unramifiedCharacter_isOpen_ker _ _)
        (isOpen_ker_leviRestrictedCharacter q₁ l₁ hq₁ hl₁ (χ₁ : rationalPoints M₁ →ₜ* ℂˣ))
        (by
          intro z
          have h1 : (θS (e z) : ℂ) = ψs.val (rationalPoints.map f z) := by
            rw [hθSψ, ambientIsoPointsEquiv_apply, hA ψs z]
          have h2 : (θL (e z) : ℂ) = ψ.val (rationalPoints.map f z) := by
            rw [hθLψ, ambientIsoPointsEquiv_apply, hA ψ z]
          rw [h1, h2, leviRestrictedCharacter_apply]
          change ((((Plancherel.rationalUnramifiedCharacterRestrict f ψs)⁻¹ *
              Plancherel.rationalUnramifiedCharacterRestrict f ψ *
              Plancherel.rationalUnramifiedCharacterRestrict (l₁ ≫ q₁) χ₁).val z : ℂˣ) : ℂ) *
              (ψs.val (rationalPoints.map f z) : ℂ) =
            (χ₁.val (rationalPoints.map (l₁ ≫ q₁) z) : ℂ) * (ψ.val (rationalPoints.map f z) : ℂ)
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, ContinuousMonoidHom.mul_apply,
            Units.val_mul, Plancherel.rationalUnramifiedCharacterRestrict_apply]
          have hinv : (((Plancherel.rationalUnramifiedCharacterRestrict f ψs).val⁻¹ z : ℂˣ) : ℂ) *
              (ψs.val (rationalPoints.map f z) : ℂ) = 1 :=
            Units.inv_mul (ψs.val (rationalPoints.map f z))
          linear_combination (ψ.val (rationalPoints.map f z) : ℂ) *
            (χ₁.val (rationalPoints.map (l₁ ≫ q₁) z) : ℂ) * hinv)
      have hirr' := (isIrreducible_iff_of_equiv
        (leviInductionEquivOfEquiv q₁ l₁ v₁ hq₁ hl₁ hv₁ hmulQ₁ _ _ E')).mp hirr
      exact (leviInduction_isIrreducible_unramifiedTwist_iff q₁ l₁ v₁ hq₁ hv₁ hl₁ hmulQ₁
        χ₁ C).mp hirr'
    · refine ⟨1, one_ne_zero, ?_⟩
      intro ψ _ θL hθL hθLψ C hC hsc hE
      exact absurd ⟨ψ, θL, hθL, hθLψ, C, hC, hsc, hE⟩ hstar
  · -- the conjugation moves some unramified character on the split component
    push Not at hD
    obtain ⟨ψ₀, a₀, h₀⟩ := hD
    have : Nontrivial σ := nontrivial_of_isIrreducible hσ
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : σ)
    let x := rationalPoints.map φ.hom (rationalPoints.map bL a₀)
    let y := rationalPoints.map bL a₀
    have key : ∀ (ψ : Plancherel.unramifiedCharacters
        (fun c => (Plancherel.rationalNormCharacters M c).toMul))
        (θL : rationalPoints L →* ℂˣ) (hθL : IsOpen (θL.ker : Set (rationalPoints L))),
        (∀ z, (θL z : ℂ) = ψ.val (rationalPoints.map f z)) →
        ∀ C : SmoothRep.{0, u, max u v} ℂ (rationalPoints L), C.IsIrreducible →
        C.representation.Equiv
          (SmoothRep.pullback e (σ.twist θL hθL)).representation →
        ∀ χ : rationalPoints B.toGrp →* ℂˣ,
          IsGeneralizedEigencharacter
            ((σ.twist θL hθL).representation.comp (rationalPoints.map bL)) χ →
          IsGeneralizedEigencharacter (C.representation.comp (rationalPoints.map bL)) χ →
          (∀ w, (ψ.val (rationalPoints.map f x) : ℂ) • σ.representation x w =
            (χ a₀ : ℂ) • w) ∧
          (∀ w, (ψ.val (rationalPoints.map f y) : ℂ) • σ.representation y w =
            (χ a₀ : ℂ) • w) := by
      intro ψ θL hθL hθLψ C hC E χ hσχ hCχ
      constructor
      · intro w
        let u : C := E.toLinearEquiv.symm w
        have hEu : E.toLinearEquiv u = w := LinearEquiv.apply_symm_apply _ _
        have h1 := ExactClassCentralSpectrumProof.apply_eq_smul_of_isGeneralizedEigencharacter
          hC (rationalPoints.map bL) hcen χ hCχ a₀ u
        have h2 : E.toLinearEquiv (C.representation (rationalPoints.map bL a₀) u) =
            (SmoothRep.pullback e (σ.twist θL hθL)).representation (rationalPoints.map bL a₀)
              (E.toLinearEquiv u) :=
          Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap _ _
        rw [h1, map_smul, hEu] at h2
        have h3 : (SmoothRep.pullback e (σ.twist θL hθL)).representation (rationalPoints.map bL a₀) w =
            (θL x : ℂ) • σ.representation x w := rfl
        rw [h3, hθLψ] at h2
        exact h2.symm
      · intro w
        have hσψ : (σ.twist θL hθL).IsIrreducible :=
          (SmoothRep.isIrreducible_twist_iff _ _ σ).mpr hσ
        have h1 := ExactClassCentralSpectrumProof.apply_eq_smul_of_isGeneralizedEigencharacter
          hσψ (rationalPoints.map bL) hcen χ hσχ a₀ w
        have h3 : (σ.twist θL hθL).representation (rationalPoints.map bL a₀) w =
            (θL y : ℂ) • σ.representation y w := rfl
        rw [h3, hθLψ] at h1
        exact h1
    by_cases hsc : ∃ s t : ℂˣ, (∀ w, σ.representation x w = (s : ℂ) • w) ∧
        (∀ w, σ.representation y w = (t : ℂ) • w)
    · obtain ⟨s, t, hs, ht⟩ := hsc
      obtain ⟨g, hg, hgψ⟩ := exists_polynomial_mul_ne_of_ne hM (rationalPoints.map f x)
        (rationalPoints.map f y) s t ψ₀ (fun h => h₀ (Units.ext h))
      refine ⟨g, hg, ?_⟩
      intro ψ hψ θL hθL hθLψ C hC _ ⟨E⟩ χ hσχ hCχ
      exfalso
      obtain ⟨k1, k2⟩ := key ψ θL hθL hθLψ C hC E χ hσχ hCχ
      apply hgψ ψ hψ
      have e1 := k1 w₀
      have e2 := k2 w₀
      rw [hs, smul_smul] at e1
      rw [ht, smul_smul] at e2
      have e3 := smul_left_injective ℂ hw₀ (e1.trans e2.symm)
      rw [mul_comm (s : ℂ), mul_comm (t : ℂ)]
      exact e3
    · refine ⟨1, one_ne_zero, ?_⟩
      intro ψ _ θL hθL hθLψ C hC _ ⟨E⟩ χ hσχ hCχ
      exfalso
      obtain ⟨k1, k2⟩ := key ψ θL hθL hθLψ C hC E χ hσχ hCχ
      apply hsc
      refine ⟨χ a₀ * (ψ.val (rationalPoints.map f x))⁻¹,
        χ a₀ * (ψ.val (rationalPoints.map f y))⁻¹, fun w => ?_, fun w => ?_⟩
      · apply smul_right_injective σ (Units.ne_zero (ψ.val (rationalPoints.map f x)))
        change (ψ.val (rationalPoints.map f x) : ℂ) • σ.representation x w =
          (ψ.val (rationalPoints.map f x) : ℂ) •
            (((χ a₀ * (ψ.val (rationalPoints.map f x))⁻¹ : ℂˣ) : ℂ) • w)
        rw [k1 w, smul_smul, Units.val_mul, Units.val_inv_eq_inv_val]
        congr 1
        field_simp
      · apply smul_right_injective σ (Units.ne_zero (ψ.val (rationalPoints.map f y)))
        change (ψ.val (rationalPoints.map f y) : ℂ) • σ.representation y w =
          (ψ.val (rationalPoints.map f y) : ℂ) •
            (((χ a₀ * (ψ.val (rationalPoints.map f y))⁻¹ : ℂˣ) : ℂ) • w)
        rw [k2 w, smul_smul, Units.val_mul, Units.val_inv_eq_inv_val]
        congr 1
        field_simp

end Wall

end Langlands.InducedTwistPersistence

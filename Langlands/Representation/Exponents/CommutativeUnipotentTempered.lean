import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.Exponents.JacquetExponentRestriction
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof

/-! # Unipotent representations of commutative reductive groups are tempered

If the group of rational points `G(k)` of a connected reductive group `G` is commutative and
every operator `π(g)` of an admissible smooth representation satisfies `(π(g) - 1)² = 0`, then
`π` is tempered in the published normalized-exponent sense: every normalized Jacquet exponent
is the trivial character, whose normalized real part `0` lies in every nonnegative root cone.
This is the temperedness half of the `𝔾_m` example built for Renard VII.2.6, Remark.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- An operator `T` with `(T - 1)² = 0` has no nonzero generalized eigenvector for an
eigenvalue `c ≠ 1`. -/
theorem eq_one_of_sq_sub_one_eq_zero_of_pow_sub_smul_apply_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (hT : (T - 1) ^ 2 = 0) {c : ℂ} {d : ℕ} {w : V} (hw : w ≠ 0)
    (hd : ((T - c • 1) ^ d) w = 0) : c = 1 := by
  by_contra hc
  have h₁ : w ∈ T.genEigenspace c d := Module.End.mem_genEigenspace_nat.mpr hd
  have h₂ : w ∈ T.genEigenspace 1 ((2 : ℕ) : ℕ∞) := Module.End.mem_genEigenspace_nat.mpr (by
    rw [one_smul ℂ (1 : Module.End ℂ V), hT, LinearMap.ker_zero]
    exact Submodule.mem_top)
  have h := (Module.End.disjoint_genEigenspace T hc (d : ℕ∞) ((2 : ℕ) : ℕ∞)).le_bot
    (Submodule.mem_inf.mpr ⟨h₁, h₂⟩)
  exact hw ((Submodule.mem_bot ℂ).mp h)

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance commutativeUnipotentPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

section Jacquet

variable {P M U : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- When `G(k)` is commutative, the split component acts on the normalized Jacquet module
through the original operators, so `(π(g) - 1)² = 0` passes to the Jacquet module. -/
theorem jacquet_sq_sub_one_eq_zero_of_mul_comm
    (hcomm : ∀ g h : rationalPoints G, g * h = h * g)
    (hunip : ∀ g, (π.representation g - 1) ^ 2 = 0) (t : rationalPoints A.toGrp) :
    (((jacquetFunctor p l r hp hr hl hmul).obj π).representation
        (splitComponentPointsMap (l ≫ p) a t) - 1) ^ 2 = 0 := by
  set m := splitComponentPointsMap (l ≫ p) a t
  have hm : (m : rationalPoints G) ∈ Subgroup.center (rationalPoints G) :=
    Subgroup.mem_center_iff.mpr fun g => hcomm g _
  set ρ := ((jacquetFunctor p l r hp hr hl hmul).obj π).representation m
  let q : π.obj →ₗ[ℂ] ((jacquetFunctor p l r hp hr hl hmul).obj π).obj :=
    Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1
  have hq : ∀ x, ρ (q x) = q (π.representation (m : rationalPoints G) x) := fun x =>
    normalizedJacquetFunctor_obj_apply_of_mem_center _ _ _ _ π m hm x
  have hstep : ∀ x, (ρ - 1) (q x) = q ((π.representation (m : rationalPoints G) - 1) x) := by
    intro x
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      map_sub, hq]
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ : ∃ x, q x = y :=
    Jacquet.Localization.mk_surjective π.representation (pointImage (r ≫ p)) 1 y
  rw [sq, Module.End.mul_apply, hstep, hstep, ← Module.End.mul_apply, ← sq, hunip,
    LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
include hp hl hr hmul in
/-- When `G(k)` is commutative and `(π(g) - 1)² = 0` for all `g`, the only normalized
Jacquet exponent is the trivial character. -/
theorem eq_one_of_isNormalizedJacquetExponent_of_mul_comm
    (ha : IsSplitComponent a)
    (hcomm : ∀ g h : rationalPoints G, g * h = h * g)
    (hunip : ∀ g, (π.representation g - 1) ^ 2 = 0) (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) : χ = 1 := by
  obtain ⟨d, w, hw, hd⟩ := (isGeneralizedEigencharacter_iff _ _).mp
    ((isNormalizedJacquetExponent_iff p l r hp hl hr hmul ha π χ).mp hχ)
  ext t
  rw [MonoidHom.one_apply, Units.val_one]
  exact eq_one_of_sq_sub_one_eq_zero_of_pow_sub_smul_apply_eq_zero _
    (jacquet_sq_sub_one_eq_zero_of_mul_comm p l r a hp hl hr hmul π hcomm hunip t) hw (hd t)

end Jacquet

/-- **Commutative unipotent temperedness.** If `G(k)` is commutative and `π` is an admissible
smooth representation with `(π(g) - 1)² = 0` for every `g`, then `π` is tempered: every
specified parabolic admits a root presentation (published existence theorem), and every
normalized Jacquet exponent is trivial, with normalized real part `0` in the nonnegative
cone. -/
theorem isNormalizedExponentTempered_of_mul_comm_of_sq_sub_one_eq_zero
    (hG : IsConnectedReductive G) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hadm : IsAdmissible π.representation)
    (hcomm : ∀ g h : rationalPoints G, g * h = h * g)
    (hunip : ∀ g, (π.representation g - 1) ^ 2 = 0) :
    IsNormalizedExponentTempered hG π := by
  have := hG.smooth
  refine ⟨hadm, fun P M A p l a hp hl ha => ⟨?_, ?_⟩⟩
  · exact parabolicRootPresentationExistence k G hG P M A p l a hp hl ha
  · intro pres U r hr hmul χ hχ
    obtain rfl := eq_one_of_isNormalizedJacquetExponent_of_mul_comm p l r a hp hl hr hmul π ha
      hcomm hunip χ hχ
    rw [Plancherel.SplitTorus.normalizedRealPart_one]
    exact pres.zero_mem_nonnegCone

end Langlands.Aubert.General.RepresentedParabolic

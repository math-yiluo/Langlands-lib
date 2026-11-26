import Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation
import Langlands.Global.AdelicParabolicConstantTermAutomorphy
import Langlands.Global.AdelicConstantTermSplitFinitenessStatement
import Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement

/-! # Finiteness under the positive split component from Harish-Chandra's finiteness theorem

`constantTermSplitComponentFiniteness_of_parabolicHarishChandraFiniteness` proves
`ConstantTermSplitComponentFinitenessStatement` (Bernstein–Lapid §6.2 and §8.5,
Mœglin–Waldspurger I.3.2) from `ParabolicHarishChandraFinitenessStatement`, Harish-Chandra's
finiteness theorem on `U'(𝔸)M'(F) \ G(𝔸)`. The constant term `C_{U'}φ` is automorphic on
`U'(𝔸)M'(F) \ G(𝔸)`, and its left translates by points of `𝔄_{P'}` lie in one space of
automorphic forms of fixed level, fixed annihilating ideal and fixed `K_∞`-profile. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

section Levi

variable {k : Type u} [Field k] {L P U : GroupScheme (Spec (CommRingCat.of k))}

/-- For a rational Levi subgroup `l : L → P`, multiplication `L × U → P` is an isomorphism
for every geometric unipotent radical `r : U → P`, not only for the one supplied by
`IsRationalLeviSubgroup`: the two radicals have the same image. -/
theorem IsRationalLeviSubgroup.isIso_subgroupMultiplication_of_radical {l : L ⟶ P}
    (hl : IsRationalLeviSubgroup l) {r : U ⟶ P} (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    IsIso (subgroupMultiplication l r) := by
  obtain ⟨U₀, r₀, hr₀, hiso⟩ := hl.exists_unipotentRadical
  have hrange : SubgroupFunctor.range r₀ = SubgroupFunctor.range r := hr₀.1.range_eq hr.1
  let e := hr₀.1.isClosedSubgroup.sourceIsoOfRangeEq hr.1.isClosedSubgroup hrange
  have he : e.hom ≫ r = r₀ :=
    hr₀.1.isClosedSubgroup.sourceIsoOfRangeEq_hom_comp hr.1.isClosedSubgroup hrange
  have hfac : subgroupMultiplication l r₀ =
      (L.X ◁ e.hom.hom.hom) ≫ subgroupMultiplication l r := by
    rw [← he]
    simp only [subgroupMultiplication, Grp.comp_hom_hom, MonObj.comp_mul, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc]
  have : IsIso e.hom.hom.hom := (inferInstance : IsIso ((Grp.forget _).mapIso e).hom)
  rw [hfac] at hiso
  exact (isIso_comp_left_iff _ _).mp hiso

end Levi

end Langlands.GroupScheme

namespace Langlands.Global

open AdelicGroupPoints InfiniteAdelicGroupPoints Langlands.GroupScheme
  Langlands.Automorphic.GroupSchemeFunctions Langlands.Geometry.Manifold

section Translates

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "A" => AdelicGroupPoints F G

/-- An element of the center annihilating every infinite slice of `ψ` annihilates every
infinite slice of its left translate `g ↦ ψ(x g)`. -/
theorem centerAction_leftTranslate_eq_zero {ψ : A → ℂ}
    (hψ : ∀ b, functionInfiniteSlice F G ψ b ∈ InfinitePlotSmoothFunctions F G)
    (z : AdelicEnvelopingCenter F G hsmooth)
    (hz : ∀ b (h : functionInfiniteSlice F G ψ b ∈ InfinitePlotSmoothFunctions F G),
      plotSmoothCenterAction F G hsmooth hcalc z ⟨_, h⟩ = 0) (x : A)
    (b : FiniteAdelicGroupPoints F G)
    (h : functionInfiniteSlice F G (fun g => ψ (x * g)) b ∈ InfinitePlotSmoothFunctions F G) :
    plotSmoothCenterAction F G hsmooth hcalc z ⟨_, h⟩ = 0 := by
  have heq : (⟨functionInfiniteSlice F G (fun g => ψ (x * g)) b, h⟩ :
      InfinitePlotSmoothFunctions F G) =
      plotSmoothLeftTranslation F G (infinite F G x) ⟨_, hψ (finite F G x * b)⟩ := by
    apply Subtype.ext
    funext a
    change ψ (x * pair F G a b) = ψ (pair F G (infinite F G x * a) (finite F G x * b))
    conv_lhs => rw [← pair_projections F G x, pair_mul]
  rw [heq]
  change plotSmoothEnvelopingAction F G hsmooth hcalc z.val
    (plotSmoothLeftTranslation F G (infinite F G x) ⟨_, hψ (finite F G x * b)⟩) = 0
  rw [Langlands.Automorphic.GroupSchemeFunctions.plotSmoothEnvelopingAction_leftTranslation hcalc]
  have hzer : plotSmoothEnvelopingAction F G hsmooth hcalc z.val ⟨_, hψ (finite F G x * b)⟩ = 0 :=
    hz (finite F G x * b) _
  rw [hzer, map_zero]

/-- If the right translates of `ψ` by a subgroup `Kinf` of `G(F_∞)` span a finite-dimensional
space, then the functions `k ↦ ψ(g k)` on `Kinf`, for all `g`, lie in one finite-dimensional
space. -/
theorem exists_finiteDimensional_profile {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    {ψ : A → ℂ} (hψ : IsInfiniteSubgroupFiniteFunction F G Kinf ψ) :
    ∃ E : Submodule ℂ (Kinf → ℂ), FiniteDimensional ℂ E ∧
      ∀ g : A, (fun k : Kinf => ψ (g * ofInfinite F G k)) ∈ E := by
  let W := Submodule.span ℂ (Set.range fun k : Kinf => fun g : A => ψ (g * ofInfinite F G k))
  have : FiniteDimensional ℂ W := hψ
  let b := Module.finBasis ℂ W
  let v (k : Kinf) : W := ⟨fun g : A => ψ (g * ofInfinite F G k), Submodule.subset_span ⟨k, rfl⟩⟩
  let c (i : Fin (Module.finrank ℂ W)) (k : Kinf) : ℂ := b.repr (v k) i
  refine ⟨Submodule.span ℂ (Set.range c), FiniteDimensional.span_of_finite ℂ (Set.finite_range _),
    fun g => ?_⟩
  have hv (k : Kinf) : ψ (g * ofInfinite F G k) = ∑ i, c i k * (b i : A → ℂ) g := by
    have h := congrArg (fun w : W => (w : A → ℂ) g) (b.sum_repr (v k))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    exact h.symm
  have hfun : (fun k : Kinf => ψ (g * ofInfinite F G k)) =
      ∑ i, (b i : A → ℂ) g • c i := by
    funext k
    rw [hv k, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Finiteness of constant terms under the positive split component**, from Harish-Chandra's
finiteness theorem on `U'(𝔸)M'(F) \ G(𝔸)`. The constant term `ψ = C_{U'}φ` is automorphic on
`U'(𝔸)M'(F) \ G(𝔸)` (`IsAutomorphicFunctionOn.subgroupConstantTerm_of_rationalImage_le`). For
`x ∈ 𝔄_{P'}` the left translate `g ↦ ψ(x g)` is again automorphic there, because `x` lies in
`P'(𝔸)` and commutes with `M'(𝔸)`; it is fixed by the level of `ψ`, annihilated by the ideal
of `ψ`, and its functions `k ↦ ψ(x g k)` lie in the space of `K_∞`-profiles of `ψ`. All
translates therefore lie in one space of Harish-Chandra's theorem. -/
theorem constantTermSplitComponentFiniteness_of_parabolicHarishChandraFiniteness
    (hHC : ParabolicHarishChandraFinitenessStatement.{u}) :
    ConstantTermSplitComponentFinitenessStatement.{u} := by
  intro F _ _ G P M U P' M' U' T _ _ _ _ _ _ p _ iU l p' _ iU' l' _ i τ hG hp hU hl hp' hU' hl'
    hT hτ hle K hK hK' N d rho hsmooth hcalc φ hrho hφ
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  let ψ := subgroupConstantTerm F (iU' ≫ p') φ
  have hψ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p' iU' l')
      Kinf rho ψ :=
    IsAutomorphicFunctionOn.subgroupConstantTerm_of_range_le p' iU' l' hcalc p iU l hU hl hU' hle hφ
  obtain ⟨hψinv, hψsm, hψK, hψZ, _⟩ := id hψ
  obtain ⟨L, hLo, hLfix⟩ := hψsm.2.2
  obtain ⟨J, hJ, hJann⟩ := hψZ
  obtain ⟨E, hE, hEmem⟩ := exists_finiteDimensional_profile hψK
  have hiso := hl'.isIso_subgroupMultiplication_of_radical hU'
  have hfin := hHC F G P' M' U' p' iU' l' hG hp' hU' hl' hiso K hK hK' rho hsmooth hcalc hrho
    J hJ L hLo E hE
  have hsub : ∀ X : Set (AdelicGroupPoints F G → ℂ), FiniteDimensional ℂ (Submodule.span ℂ X) →
      (Set.range fun x : positiveCentralTorusPoints T i (l' ≫ p') =>
        fun g : AdelicGroupPoints F G => ψ ((x : AdelicGroupPoints F G) * g)) ⊆ X →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x :
        positiveCentralTorusPoints T i (l' ≫ p') =>
          fun g : AdelicGroupPoints F G => ψ ((x : AdelicGroupPoints F G) * g))) :=
    fun X hX hSX => by
      have := hX
      exact Submodule.finiteDimensional_of_le (Submodule.span_mono hSX)
  refine hsub _ hfin ?_
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨⟨t, -, htx⟩, hxc⟩ := Subgroup.mem_inf.mp hx
  -- `x` is the image of a point of `P'(𝔸)`
  let y : AdelicGroupPoints F P' := t ≫ (τ ≫ l').hom.hom
  have hy : map F P' G p' y = x := by
    rw [← htx, ← hτ]
    rfl
  refine ⟨⟨?_, (IsAutomorphicFunctionOn.leftTranslate hcalc hψ x).2⟩, ?_, ?_, ?_⟩
  · apply IsLeftInvariantUnder.sup
    · rintro _ ⟨n, rfl⟩ g
      have hn : map F U' G (iU' ≫ p') n ∈
          AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU' ≫ p')) := ⟨n, rfl⟩
      obtain ⟨n', hn'⟩ := conj_mem_adelicPoints_range p' iU' hU'.1.isNormal y hn
      rw [hy] at hn'
      change ψ (x * (map F U' G (iU' ≫ p') n * g)) = ψ (x * g)
      have hmul : x * (map F U' G (iU' ≫ p') n * g) =
          (x * map F U' G (iU' ≫ p') n * x⁻¹) * (x * g) := by group
      rw [hmul]
      exact hψinv _ (Subgroup.mem_sup_left ⟨n', hn'⟩) _
    · rintro _ ⟨m, rfl⟩ g
      have hcomm := (Subgroup.mem_centralizer_iff.mp hxc)
        (map F M' G (l' ≫ p') (rational F M' m)) ⟨_, rfl⟩
      change ψ (x * (map F M' G (l' ≫ p') (rational F M' m) * g)) = ψ (x * g)
      rw [← mul_assoc, ← hcomm, mul_assoc]
      exact hψinv _ (Subgroup.mem_sup_right ⟨m, rfl⟩) _
  · intro b hb g
    change ψ (x * (g * ofFinite F G b)) = ψ (x * g)
    rw [← mul_assoc]
    exact hLfix b hb _
  · exact fun z hz b h => centerAction_leftTranslate_eq_zero hcalc hψsm.2.1 z (hJann z hz) x b h
  · intro g
    have h := hEmem (x * g)
    simp only [mul_assoc] at h
    exact h

end Translates

end Langlands.Global

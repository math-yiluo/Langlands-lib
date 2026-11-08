import Langlands.Representation.Families.RenardGenericIrreducibilityStatements
import Langlands.Representation.Exponents.LeviNormalizerQuotientStatements
import Langlands.Representation.Exponents.LeviJacquetInductionSupercuspidalFiltrationStatement
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Exponents.MaximalLeviReducibilityInductionInputs
import Langlands.Representation.Aubert.General.JacquetMultiplicityIrreducibility
import Langlands.Representation.Plancherel.RationalUnitaryNonvanishing
import Langlands.Representation.Filtration.IntertwiningRankFiltrationBound
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof

/-! # Renard VI.8.5 from its inputs

Renard 2026, VI.8.5 (PDF pp.199–200): for an irreducible supercuspidal `ρ` of `M(F)`, the
induced representation `i_P^G(ρ ⊗ ψ)` is irreducible for `ψ` in a nonempty Zariski open
subset of `X(M)`. This module derives `GenericInducedIrreducibilityStatement` from VI.8.4
(`InducedIrreducibilityOpenStatement`) and the seven further published statements named in
`genericInducedIrreducibility_of_statements`; none of them is proved here.

By VI.8.4 it suffices to find one unramified `ψ₀` with `i_P^G(ρ ⊗ ψ₀)` irreducible, since
the polynomial it gives does not vanish at `ψ₀`. We take `ψ₀ = ψ₊ ψ_u`, where `ψ₊` has
positive values and makes the central character unitary, and `ψ_u` is a unitary
unramified character avoiding finitely many hypersurfaces `b_j = 0`, one for each
nontrivial class `g_j M(F)` of `N_G(M)(F)/M(F)`. Then `σ = ρ ⊗ ψ₀` is unitarizable, so
`i_P^G σ` is admissible, unitarizable and semisimple. Frobenius reciprocity identifies
its endomorphisms with `Hom_M(r_P^G i_P^G σ, σ)`. The filtration of VI.5.3(iii) and left
exactness bound this rank by the sum over its graded pieces `σ ∘ Int(z_i)`. Schur's
lemma bounds the piece of the trivial double coset by one, and the choice of `ψ_u`
separates the central characters of all the other pieces from that of `σ`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

section Abstract

variable {H : Type*} [Group H] [TopologicalSpace H]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Schur's lemma as a rank bound: from an irreducible representation to an irreducible
admissible one there is at most a line of intertwiners. -/
theorem rank_intertwiningMap_le_one_of_isIrreducible {ρ : Representation ℂ H V}
    {σ : Representation ℂ H W} (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (ha : IsAdmissible σ) : Module.rank ℂ (ρ.IntertwiningMap σ) ≤ 1 := by
  classical
  by_cases he : Nonempty (ρ.Equiv σ)
  · obtain ⟨e⟩ := he
    obtain ⟨L⟩ := admissibleSchur_homEquiv ρ (isAdmissible_of_equiv e.symm ha) hρ σ e
    have h := L.lift_rank_eq
    rw [Module.rank_self, Cardinal.lift_one, Cardinal.lift_eq_one] at h
    exact h.le
  · have : IsEmpty (ρ.Equiv σ) := ⟨fun e => he ⟨e⟩⟩
    rw [rank_subsingleton']
    exact zero_le

omit [TopologicalSpace H] in
/-- Irreducibility transports along an equivariant linear equivalence. -/
theorem isIrreducible_of_representationEquiv {ρ : Representation ℂ H V}
    {σ : Representation ℂ H W} (e : ρ.Equiv σ) (hi : ρ.IsIrreducible) : σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at hi ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap)
    e.bijective).mp hi

/-- The complex embedding of positive real units is injective. -/
theorem positiveUnitsToComplex_injective : Function.Injective positiveUnitsToComplex := by
  intro x y h
  apply Units.ext
  apply NNReal.coe_injective
  have h' := congrArg (fun z : ℂˣ => ((z : ℂ)).re) h
  simpa using h'

variable {I : Type*}

/-- A positive character trivial on the common norm kernel is an unramified character, once
the common norm kernel is open. -/
theorem exists_unramifiedCharacter_eq_positive [IsTopologicalGroup H] (ν : I → (H →* ℝ≥0ˣ))
    (hG1 : IsOpen (Plancherel.commonNormKernel ν : Set H)) (i : I) :
    ∃ θ : Plancherel.unramifiedCharacters ν,
      ∀ h : H, (θ : H →ₜ* ℂˣ) h = positiveUnitsToComplex (ν i h) := by
  let ψ₀ : H →* ℂˣ := positiveUnitsToComplex.comp (ν i)
  have hker : Plancherel.commonNormKernel ν ≤ ψ₀.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    change positiveUnitsToComplex (ν i g) = 1
    rw [(Plancherel.mem_commonNormKernel ν g).mp hg i, map_one]
  exact ⟨⟨⟨ψ₀, Langlands.Weil.continuous_of_open_kernel ψ₀ (Subgroup.isOpen_mono hker hG1)⟩,
    hker⟩, fun _ => rfl⟩

/-- The regular function `χ ↦ c₁ χ(x₁) - c₂ χ(x₂)` is nonzero as soon as some unramified
`θ` separates `x₁` and `x₂`: its values at `1` and at `θ` cannot both vanish. -/
theorem evaluationDifference_ne_zero (ν : I → (H →* ℝ≥0ˣ)) (x₁ x₂ : H) (c₁ c₂ : ℂˣ)
    (θ : Plancherel.unramifiedCharacters ν)
    (hθ : (((θ : H →ₜ* ℂˣ) x₁ : ℂˣ) : ℂ) ≠ (θ : H →ₜ* ℂˣ) x₂) :
    (c₁ : ℂ) • Plancherel.unramifiedEvaluationRegular ν x₁ -
      (c₂ : ℂ) • Plancherel.unramifiedEvaluationRegular ν x₂ ≠ 0 := by
  intro h
  have h1 := congrArg (fun b : Plancherel.unramifiedRegularFunctions ν => b.val 1) h
  have h2 := congrArg (fun b : Plancherel.unramifiedRegularFunctions ν => b.val θ) h
  simp only [Subalgebra.coe_sub, Subalgebra.coe_smul, Pi.sub_apply, Pi.smul_apply,
    Plancherel.unramifiedEvaluationRegular_apply, smul_eq_mul, ZeroMemClass.coe_zero,
    Pi.zero_apply] at h1 h2
  have h1' : (c₁ : ℂ) = c₂ := by
    simpa [sub_eq_zero] using h1
  rw [h1', ← mul_sub, mul_eq_zero, sub_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact c₂.ne_zero h2
  · exact hθ h2

end Abstract

section Points

variable {k : Type u} [Field k] {G P M : GroupScheme (Spec (CommRingCat.of k))}

/-- A point map of an automorphism of `M` sends the centre of `M(k)` into itself. -/
theorem map_hom_mem_center (φ : M ≅ M) {a : rationalPoints M}
    (ha : a ∈ Subgroup.center (rationalPoints M)) :
    rationalPoints.map φ.hom a ∈ Subgroup.center (rationalPoints M) := by
  rw [Subgroup.mem_center_iff]
  intro y
  rw [← rationalPoints_map_hom_map_inv φ y, ← map_mul, ← map_mul,
    Subgroup.mem_center_iff.mp ha]

/-- Through the Levi embedding, the automorphism of `M` attached to a normalizing `w` is
conjugation by `w`. -/
theorem map_levi_map_of_normalizes (p : P ⟶ G) (l : M ⟶ P) (w : rationalPoints G)
    (φ : M ≅ M) (hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom) (x : rationalPoints M) :
    rationalPoints.map (l ≫ p) (rationalPoints.map φ.hom x) =
      w * rationalPoints.map (l ≫ p) x * w⁻¹ := by
  rw [← pointMap_comp_apply, hφ, ← Category.assoc, pointMap_comp_apply,
    rationalPoints_map_innerIso]
  rfl

/-- Two normalizing elements in the same class modulo `M(k)` induce the same map on the
centre of `M(k)`. -/
theorem map_hom_center_eq_of_mul (p : P ⟶ G) (l : M ⟶ P)
    (hinj : Function.Injective (rationalPoints.map (l ≫ p))) (w g : rationalPoints G)
    (φ ψ : M ≅ M) (hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom)
    (hψ : ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom) (m : rationalPoints M)
    (hw : w = g * rationalPoints.map (l ≫ p) m) {a : rationalPoints M}
    (ha : a ∈ Subgroup.center (rationalPoints M)) :
    rationalPoints.map φ.hom a = rationalPoints.map ψ.hom a := by
  apply hinj
  rw [map_levi_map_of_normalizes p l w φ hφ, map_levi_map_of_normalizes p l g ψ hψ, hw]
  have hc : rationalPoints.map (l ≫ p) m * rationalPoints.map (l ≫ p) a =
      rationalPoints.map (l ≫ p) a * rationalPoints.map (l ≫ p) m := by
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp ha m]
  calc g * rationalPoints.map (l ≫ p) m * rationalPoints.map (l ≫ p) a *
        (g * rationalPoints.map (l ≫ p) m)⁻¹ =
      g * (rationalPoints.map (l ≫ p) m * rationalPoints.map (l ≫ p) a) *
        (rationalPoints.map (l ≫ p) m)⁻¹ * g⁻¹ := by group
    _ = g * (rationalPoints.map (l ≫ p) a * rationalPoints.map (l ≫ p) m) *
        (rationalPoints.map (l ≫ p) m)⁻¹ * g⁻¹ := by rw [hc]
    _ = g * rationalPoints.map (l ≫ p) a * g⁻¹ := by group

end Points

section Core

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

local instance genericIrreducibilityPointTopology {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] : TopologicalSpace (rationalPoints H) :=
  RationalPointFamily.pointTopology

variable {G P M U : GroupScheme (Spec (CommRingCat.of k))}

variable [IsAffineHom M.X.hom] [NonarchimedeanGroup (rationalPoints M)]

/-- The core of Renard VI.8.5: one unramified twist of an irreducible supercuspidal `ρ` has
irreducible normalized induction. -/
theorem exists_unramifiedTwist_leviInduction_isIrreducible [T2Space k]
    (hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, v})
    (hSU : SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u, v})
    (hIA : LeviInductionAdmissibleStatement.{u, v})
    (hIU : LeviInductionUnitarizableStatement.{u, v})
    (hFilt : LeviJacquetInductionSupercuspidalFiltrationStatement.{u, v})
    (hW1 : LeviNormalizerFiniteQuotientStatement.{u})
    (hW2 : LeviNormalizerNormFixingStatement.{u})
    (hG : IsConnectedReductive G) [IsAffineHom G.X.hom]
    [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
    [LocallyCompactSpace (rationalPoints M)]
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (hirr : ρ.IsIrreducible)
    (hsc : ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
      (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
      (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
      (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
      (hmul' : IsIso (subgroupMultiplication l' r')),
      ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) :
    ∃ ψ₀ : Plancherel.unramifiedCharacters
        (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul),
      ((leviInductionFunctor p l r hp hr hl hmul).obj
        (ρ.twist ψ₀.val.toMonoidHom
          (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₀))).IsIrreducible := by
  classical
  have hM : IsConnectedReductive M := hl.isConnectedReductive
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : Smooth M.X.hom := hM.smooth
  have : IsTopologicalGroup (rationalPoints M) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_isTopologicalGroup k M
  -- The central character `ω` of `ρ` and the positive correction `ψ₊`.
  obtain ⟨ω, hact⟩ := CuspidalSupport.rationalPointCentralCharacter k M hM ρ hirr
  obtain ⟨x₀, hx₀⟩ :=
    Whittaker.MirabolicRigidity.exists_ne_zero_of_isIrreducible ρ.representation hirr
  have : Nontrivial ρ := ⟨⟨x₀, 0, hx₀⟩⟩
  have hω : IsOpen (ω.ker : Set (Subgroup.center (rationalPoints M))) :=
    SmoothRep.HasCentralCharacter.isOpen_ker ρ hact
  obtain ⟨ψp, -, hnormp⟩ := exists_positive_unramifiedCharacter_norm_mul_eq_one hM ω hω
  -- Representatives of `N_G(M)(F)/M(F)` and the moving central points.
  obtain ⟨n, g, hgφ, hcover⟩ := hW1 k G hG P M p l hp hl
  choose φg hφg using hgφ
  have hdata : ∀ j : Fin n, ∃ a : rationalPoints M, a ∈ Subgroup.center (rationalPoints M) ∧
      (g j ∉ pointImage (l ≫ p) → ∃ χ : rationalCharacters M,
        (Plancherel.rationalNormCharacters M χ).toMul (rationalPoints.map (φg j).hom a) ≠
          (Plancherel.rationalNormCharacters M χ).toMul a) := by
    intro j
    by_cases hj : g j ∈ pointImage (l ≫ p)
    · exact ⟨1, Subgroup.one_mem _, fun h => absurd hj h⟩
    · have h := mt (hW2 k G hG P M p l hp hl (g j) (φg j) (hφg j)) hj
      push Not at h
      obtain ⟨a, ha, χ, hχ⟩ := h
      exact ⟨a, ha, fun _ => ⟨χ, hχ⟩⟩
  choose a ha hmove using hdata
  let ν := fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul
  let az : Fin n → Subgroup.center (rationalPoints M) := fun j => ⟨a j, ha j⟩
  let bz : Fin n → Subgroup.center (rationalPoints M) := fun j =>
    ⟨rationalPoints.map (φg j).hom (a j), map_hom_mem_center (φg j) (ha j)⟩
  let ω₀ : Subgroup.center (rationalPoints M) → ℂˣ := fun z =>
    (ψp : rationalPoints M →ₜ* ℂˣ) z * ω z
  let b : Fin n → Plancherel.unramifiedRegularFunctions ν := fun j =>
    ((ω₀ (bz j) : ℂˣ) : ℂ) • Plancherel.unramifiedEvaluationRegular ν (bz j : rationalPoints M) -
      ((ω₀ (az j) : ℂˣ) : ℂ) • Plancherel.unramifiedEvaluationRegular ν (az j : rationalPoints M)
  let S : Finset (Fin n) := Finset.univ.filter fun j => g j ∉ pointImage (l ≫ p)
  have hb : ∀ j ∈ S, b j ≠ 0 := by
    intro j hjS
    have hj : g j ∉ pointImage (l ≫ p) := (Finset.mem_filter.mp hjS).2
    obtain ⟨χ, hχ⟩ := hmove j hj
    obtain ⟨θ, hθ⟩ := exists_unramifiedCharacter_eq_positive ν
      (Plancherel.isOpen_rationalCommonNormKernel M) χ
    refine evaluationDifference_ne_zero ν _ _ _ _ θ ?_
    rw [hθ, hθ]
    intro h
    exact hχ (positiveUnitsToComplex_injective (Units.ext h))
  obtain ⟨χu, hχu⟩ := Plancherel.rationalUnramifiedRegular_exists_unitary_finset_ne_zero M hM
    S b hb
  -- The twist `σ = ρ ⊗ ψ₀`.
  let ψu : Plancherel.unramifiedCharacters ν := ⟨χu.val, χu.property.1⟩
  have hψu : ∀ m : rationalPoints M, ‖(((ψu : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ)‖ = 1 :=
    χu.property.2
  refine ⟨ψp * ψu, ?_⟩
  set ψ₀ : Plancherel.unramifiedCharacters ν := ψp * ψu with hψ₀def
  have hψ₀ : ∀ m : rationalPoints M, (((ψ₀ : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) =
      (((ψp : rationalPoints M →ₜ* ℂˣ) m : ℂˣ) : ℂ) * ((ψu : rationalPoints M →ₜ* ℂˣ) m) := by
    intro m
    rfl
  have hχ₀ := Plancherel.unramifiedCharacter_isOpen_ker _ ψ₀
  set σ := ρ.twist ψ₀.val.toMonoidHom hχ₀ with hσdef
  have hσirr : σ.IsIrreducible := (SmoothRep.isIrreducible_twist_iff _ hχ₀ ρ).mpr hirr
  have hσsc := properJacquet_subsingleton_unramifiedTwist ψ₀ ρ hsc
  have hσadm : σ.IsAdmissible := hAdm k M hM σ hσirr
  have hσact : ∀ (z : Subgroup.center (rationalPoints M)) (x : σ),
      σ.representation (z : rationalPoints M) x =
        ((((ψ₀ : rationalPoints M →ₜ* ℂˣ) z : ℂˣ) : ℂ) * (ω z : ℂ)) • x := by
    intro z x
    change (((ψ₀ : rationalPoints M →ₜ* ℂˣ) z : ℂˣ) : ℂ) • ρ.representation z x = _
    rw [hact z x, smul_smul]
  have hσnorm : ∀ z : Subgroup.center (rationalPoints M),
      ‖(((ψ₀ : rationalPoints M →ₜ* ℂˣ).toMonoidHom z : ℂˣ) : ℂ) * (ω z : ℂ)‖ = 1 := by
    intro z
    change ‖(((ψ₀ : rationalPoints M →ₜ* ℂˣ) z : ℂˣ) : ℂ) * (ω z : ℂ)‖ = 1
    rw [hψ₀, mul_right_comm, norm_mul, hnormp z, hψu, one_mul]
  have hσunit : IsUnitarizable σ.representation :=
    hSU k M hM σ hσirr hσsc ⟨twistUnitaryCentralCharacter ρ.representation
      (ψ₀ : rationalPoints M →ₜ* ℂˣ).toMonoidHom hχ₀ ω hω hact hσnorm⟩
  obtain ⟨y₀, hy₀⟩ :=
    Whittaker.MirabolicRigidity.exists_ne_zero_of_isIrreducible σ.representation hσirr
  have : Nontrivial σ := ⟨⟨y₀, 0, hy₀⟩⟩
  -- The induced representation is admissible, unitarizable, nonzero and semisimple.
  set π := (leviInductionFunctor p l r hp hr hl hmul).obj σ with hπdef
  have hπadm : π.IsAdmissible := hIA k G hG P M U p l r hp hl hr hmul σ hσadm
  have hπunit : IsUnitarizable π.representation :=
    hIU k G hG P M U p l r hp hl hr hmul σ hσunit
  have : Nontrivial π := leviInductionNontrivial k G hG P M U p l r hp hl hr hmul σ inferInstance
  have hsem := admissibleUnitarySemisimplicity (rationalPoints G)
    (compactOpenCofinal_of_nonarchimedean (rationalPoints G)) π π.representation hπadm hπunit
  apply isIrreducible_of_semisimple_rank_endomorphism_le_one π hsem
  -- Frobenius reciprocity and the filtration of the Jacquet module.
  obtain ⟨e, -⟩ := leviFrobeniusReciprocity.{u, v, max u v} k G hG P M U p l r hp hl hr hmul π σ
  rw [e.rank_eq]
  obtain ⟨⟨m, c, z, φ, eφ, hz, hφ, he, s, hs⟩, -⟩ :=
    hFilt k G hG P M U P M U p l r hp hl hr hmul p l r hp hl hr hmul
      ⟨1, Iso.refl M, by rw [G.innerIso_one_hom]; simp⟩ σ hσsc
  have hinj : Function.Injective (rationalPoints.map (l ≫ p)) := by
    intro x y hxy
    apply (leviPointsEquiv p l hp hl).injective
    exact Subtype.ext hxy
  let d : Fin m → ℕ := fun i => if z i ∈ pointImage p then 1 else 0
  have hd : ∀ i, Module.rank ℂ ((s.gradedRepresentation i).ρ.IntertwiningMap
      σ.representation) ≤ d i := by
    intro i
    obtain ⟨ε⟩ := hs i
    by_cases hzi : z i ∈ pointImage p
    · simp only [d, hzi, ↓reduceIte, Nat.cast_one]
      exact rank_intertwiningMap_le_one_of_isIrreducible
        (isIrreducible_of_representationEquiv ε.symm
          ((isIrreducible_comp_continuousMulEquiv_iff σ.representation (eφ i)).mpr hσirr))
        hσirr hσadm
    · simp only [d, hzi, ↓reduceIte, Nat.cast_zero]
      obtain ⟨j, m₀, hzj⟩ := hcover (z i) (φ i) (hφ i)
      have hj : g j ∉ pointImage (l ≫ p) := by
        rintro ⟨y, hy⟩
        apply hzi
        rw [hzj, ← hy, ← map_mul]
        exact pointImage_comp_le p l ⟨y * m₀, rfl⟩
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      have hcent : ∀ x : rationalPoints M, x ∈ Subgroup.center (rationalPoints M) →
          eφ i x = rationalPoints.map (φg j).hom x := fun x hx =>
        (he i x).trans (map_hom_center_eq_of_mul p l hinj (z i) (g j) (φ i) (φg j) (hφ i)
          (hφg j) m₀ hzj hx)
      have hzero : ∀ f : (SmoothRep.pullback (eφ i) σ).representation.IntertwiningMap
          σ.representation, f = 0 := by
        intro f
        ext x
        by_contra hx
        have hx' : f x ≠ 0 := hx
        -- Equality of central characters at the moving point `a j`.
        have key := Representation.IntertwiningMap.isIntertwining _ _ f (a j) x
        have hk1 : (SmoothRep.pullback (eφ i) σ).representation (a j) x =
            ((((ψ₀ : rationalPoints M →ₜ* ℂˣ) (bz j) : ℂˣ) : ℂ) * (ω (bz j) : ℂ)) • x := by
          change σ.representation (eφ i (a j)) x = _
          rw [hcent (a j) (ha j)]
          exact hσact (bz j) x
        have hk2 := hσact (az j) (f x)
        change σ.representation (a j) (f x) = _ at hk2
        rw [hk1, hk2, map_smul] at key
        have hscal := smul_left_injective ℂ hx' key
        apply hχu j hjS
        change ((ω₀ (bz j) : ℂˣ) : ℂ) * (((ψu : rationalPoints M →ₜ* ℂˣ) (bz j) : ℂˣ) : ℂ) -
          ((ω₀ (az j) : ℂˣ) : ℂ) * (((ψu : rationalPoints M →ₜ* ℂˣ) (az j) : ℂˣ) : ℂ) = 0
        rw [sub_eq_zero]
        simp only [ω₀, Units.val_mul]
        rw [hψ₀, hψ₀] at hscal
        calc (((ψp : rationalPoints M →ₜ* ℂˣ) (bz j) : ℂˣ) : ℂ) * (ω (bz j) : ℂ) *
              (((ψu : rationalPoints M →ₜ* ℂˣ) (bz j) : ℂˣ) : ℂ) =
            (((ψp : rationalPoints M →ₜ* ℂˣ) (bz j) : ℂˣ) : ℂ) *
              (((ψu : rationalPoints M →ₜ* ℂˣ) (bz j) : ℂˣ) : ℂ) * (ω (bz j) : ℂ) := by ring
          _ = (((ψp : rationalPoints M →ₜ* ℂˣ) (az j) : ℂˣ) : ℂ) *
              (((ψu : rationalPoints M →ₜ* ℂˣ) (az j) : ℂˣ) : ℂ) * (ω (az j) : ℂ) := hscal
          _ = _ := by ring
      have : Subsingleton ((s.gradedRepresentation i).ρ.IntertwiningMap σ.representation) := by
        constructor
        intro f₁ f₂
        apply HomSpace.comap_injective σ.representation ε.symm.toIntertwiningMap
          ε.symm.surjective
        rw [hzero (HomSpace.comap σ.representation ε.symm.toIntertwiningMap f₁),
          hzero (HomSpace.comap σ.representation ε.symm.toIntertwiningMap f₂)]
      rw [rank_subsingleton']
  refine (ObjectRepFiltration.rank_intertwiningMap_le_sum s σ.representation d hd).trans ?_
  have hsum : ∑ i, d i ≤ 1 := by
    have hcard : ∑ i, d i = (Finset.univ.filter fun i => z i ∈ pointImage p).card := by
      simp only [d]
      rw [Finset.sum_boole, Nat.cast_id]
    rw [hcard, Finset.card_le_one]
    intro i hi i' hi'
    have hzi : z i ∈ pointImage p := (Finset.mem_filter.mp hi).2
    have hzi' : z i' ∈ pointImage p := (Finset.mem_filter.mp hi').2
    have hmk : ∀ x : rationalPoints G, x ∈ pointImage p →
        DoubleCoset.mk (pointImage p) (pointImage p) x =
          DoubleCoset.mk (pointImage p) (pointImage p) 1 := by
      intro x hx
      rw [DoubleCoset.eq]
      exact ⟨x⁻¹, Subgroup.inv_mem _ hx, 1, Subgroup.one_mem _, by group⟩
    apply c.injective
    apply Subtype.ext
    rw [← hz i, ← hz i', hmk _ hzi, hmk _ hzi']
  exact_mod_cast hsum

end Core

/-- **Renard VI.8.5 from its inputs.** VI.8.4, Jacquet's admissibility theorem, unitarity of
supercuspidals with unitary central character, admissibility and unitarity of normalized
induction, the geometric lemma VI.5.3(iii) and the finiteness and faithfulness of `N_G(M)/M`
imply the generic irreducibility theorem. -/
theorem genericInducedIrreducibility_of_statements
    (hOpen : InducedIrreducibilityOpenStatement.{u, v})
    (hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, v})
    (hSU : SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u, v})
    (hIA : LeviInductionAdmissibleStatement.{u, v})
    (hIU : LeviInductionUnitarizableStatement.{u, v})
    (hFilt : LeviJacquetInductionSupercuspidalFiltrationStatement.{u, v})
    (hW1 : LeviNormalizerFiniteQuotientStatement.{u})
    (hW2 : LeviNormalizerNormFixingStatement.{u}) :
    GenericInducedIrreducibilityStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hirr hsc
  obtain ⟨ψ₀, hψ₀⟩ := exists_unramifiedTwist_leviInduction_isIrreducible hAdm hSU hIA hIU hFilt
    hW1 hW2 hG p l r hp hl hr hmul ρ hirr hsc
  obtain ⟨f, hf₀, hf⟩ := hOpen k G hG P M U p l r hp hl hr hmul ρ hirr ψ₀ hψ₀
  refine ⟨f, ?_, hf⟩
  rintro rfl
  exact ((Plancherel.mem_rationalUnramifiedPrincipalOpen M hl.isConnectedReductive 0 ψ₀).mp
    hf₀) (by simp)

/-- The eight propositions from which the proof of Renard VI.8.5 is assembled. -/
structure GenericInducedIrreducibilityInputs : Prop where
  inducedIrreducibilityOpen : InducedIrreducibilityOpenStatement.{u, v}
  irreducibleAdmissible : RationalPointsIrreducibleAdmissibleStatement.{u, v}
  supercuspidalUnitarizable : SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u, v}
  inductionAdmissible : LeviInductionAdmissibleStatement.{u, v}
  inductionUnitarizable : LeviInductionUnitarizableStatement.{u, v}
  jacquetFiltration : LeviJacquetInductionSupercuspidalFiltrationStatement.{u, v}
  normalizerFiniteQuotient : LeviNormalizerFiniteQuotientStatement.{u}
  normalizerNormFixing : LeviNormalizerNormFixingStatement.{u}

/-- **Renard VI.8.5** from the packaged inputs. -/
theorem genericInducedIrreducibility_of_inputs (h : GenericInducedIrreducibilityInputs.{u, v}) :
    GenericInducedIrreducibilityStatement.{u, v} :=
  genericInducedIrreducibility_of_statements h.inducedIrreducibilityOpen h.irreducibleAdmissible
    h.supercuspidalUnitarizable h.inductionAdmissible h.inductionUnitarizable h.jacquetFiltration
    h.normalizerFiniteQuotient h.normalizerNormFixing

end Langlands.Renard.AlgebraicFamily

import Langlands.Global.AdelicLocalFinitenessLeftOperators
import Langlands.Global.AdelicLocalFinitenessBoxOperators
import Langlands.Global.AdelicLocalFinitenessSolutionComponents
import Langlands.Global.AdelicLocalFinitenessShiftPoints
import Langlands.Global.AdelicTestFunctionLevelAverage
import Langlands.Global.AdelicLocalFinitenessBoundaryReduction
import Langlands.Global.AdelicLocalFinitenessSmoothing
import Langlands.Global.AdelicLocalFinitenessChamberWeights
import Langlands.Global.AdelicLocalFinitenessResidualOperators
import Langlands.Global.AdelicLocalFinitenessChamberEmbedding

/-! # Construction of the compact boundary model

The right-hand operator family `ν_s` of the boundary model (compact Harish-Chandra restrictions to
the boxes of a smoothed vector, zero on the residual coordinates), and the construction of a
`LocalFinitenessData.BoundaryModel` (module `AdelicLocalFinitenessBoundaryReduction`) for a
standard parabolic family from an Iwasawa subgroup with chamber coordinates, rational Siegel
representatives, and `PositiveTorusSplitComponentStatement`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal Manifold

namespace Langlands.Global.LocalFinitenessData

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {Δ : Type u} {r n : ℕ} {W : TopologicalSpace.Opens (Fin n → ℂ)}
  (X : LocalFinitenessData F G Δ r n W)

/-- For admissible data every coefficient of the residual polynomials of `dirCoeff` is
holomorphic on `W`. -/
theorem mdifferentiableOn_dirCoeff (hX : X.IsAdmissible) (J : Δ → Prop) (ε : Fin r → Bool)
    (k : {β : Δ // ¬ J β} ⊕ Fin r) (q : Fin (X.dirDegree J k)) :
    MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) (fun s => X.dirCoeff J s ε k q) Set.univ := by
  rcases k with β | j
  · exact hX.2.2.2.2.2.1 β.1 q (ContinuousLinearMap.id ℂ ℂ)
  · cases hε : ε j
    · have h1 : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ)
          (fun s => (X.centralD j s).coeff (X.centralDegree j - q)) Set.univ :=
        hX.2.2.2.2.2.2.2 j (X.centralDegree j - q) (ContinuousLinearMap.id ℂ ℂ)
      have h2 : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ)
          (fun s => (X.centralD j s).coeff 0) Set.univ :=
        hX.2.2.2.2.2.2.2 j 0 (ContinuousLinearMap.id ℂ ℂ)
      refine (h1.div h2 fun s _ => (hX.2.2.2.2.2.2.1 j s).2.2).congr fun s _ => ?_
      simp [dirCoeff, hε]
    · have h1 : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ)
          (fun s => (X.centralD j s).coeff q) Set.univ :=
        hX.2.2.2.2.2.2.2 j q (ContinuousLinearMap.id ℂ ℂ)
      refine h1.congr fun s _ => ?_
      simp [dirCoeff, hε]

end Langlands.Global.LocalFinitenessData

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicSubgroupPoints AdelicGroupPoints AdelicSiegelFactors
  Langlands.Analysis.Meromorphic
open Langlands.Global.HarishChandraDecomposition Langlands.Global.StandardConstantTerm

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

private instance : IsClosedImmersion (Standard.parabolicHom 𝓕.i 𝓕.ν ∅).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom 𝓕.i 𝓕.ν ∅

private instance : IsAffine (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅).X.left :=
  isAffine_of_isAffineHom (Standard.parabolicHom 𝓕.i 𝓕.ν ∅).hom.hom.left

variable {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) K)
  [Fintype (simpleRelativeRoots 𝓕.i 𝓕.ν)] [DecidableEq (simpleRelativeRoots 𝓕.i 𝓕.ν)] {r : ℕ}
  (e : RealCharacterDual F (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅) ≃L[ℝ]
    ((simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) × (Fin r → ℝ)))

open scoped Classical in
/-- The core of the right-hand family on a coordinate: the operator `Tbox P ε` into the box of a
component and orthant, zero on a residual coordinate. -/
def boundaryRhsCore (ra τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (rb : Fin r → ℝ)
    (m : ∀ (P : Finset (characterLattice 𝓕.T)) (_ε : Fin r → Bool), 𝓕.BoundaryDirection P r → ℕ)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Tbox : ∀ (P : {P // P ∈ 𝓕.simpleRootFinset.powerset}) (ε : Fin r → Bool),
      V →L[ℂ] Lp ℂ 2 ((𝓕.siegelHaar hK e ra τ rb).restrict (orthantBox (chamberCoords hK e) τ
        (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε (m P.1 ε))))
    (ω : 𝓕.BoundaryIndex r) :
    V →L[ℂ] Lp ℂ 2 ((𝓕.siegelHaar hK e ra τ rb).restrict (𝓕.boundaryRegion hK e τ m ω)) :=
  match ω with
  | ⟨P, ε, none⟩ => Tbox P ε
  | ⟨_, _, some _⟩ => 0

open scoped Classical in
/-- **The right-hand family.** For each parameter `s`, the assembly over all coordinates of
`boundaryRhsCore ω ∘ D s`, for a family `D s : B → V`. -/
def boundaryRhs (ra τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (rb : Fin r → ℝ)
    (m : ∀ (P : Finset (characterLattice 𝓕.T)) (_ε : Fin r → Bool), 𝓕.BoundaryDirection P r → ℕ)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Tbox : ∀ (P : {P // P ∈ 𝓕.simpleRootFinset.powerset}) (ε : Fin r → Bool),
      V →L[ℂ] Lp ℂ 2 ((𝓕.siegelHaar hK e ra τ rb).restrict (orthantBox (chamberCoords hK e) τ
        (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε (m P.1 ε))))
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] {Par : Type*} (D : Par → B →L[ℂ] V)
    (s : Par) :
    B →L[ℂ] PiLp 2 (fun ω : 𝓕.BoundaryIndex r =>
      Lp ℂ 2 ((𝓕.siegelHaar hK e ra τ rb).restrict (𝓕.boundaryRegion hK e τ m ω))) :=
  piAssemble fun ω => 𝓕.boundaryRhsCore hK e ra τ rb m Tbox ω ∘L D s

open scoped Classical in
theorem isCompactOperator_boundaryRhs (ra τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ)
    (rb : Fin r → ℝ)
    (m : ∀ (P : Finset (characterLattice 𝓕.T)) (_ε : Fin r → Bool), 𝓕.BoundaryDirection P r → ℕ)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Tbox : ∀ (P : {P // P ∈ 𝓕.simpleRootFinset.powerset}) (ε : Fin r → Bool),
      V →L[ℂ] Lp ℂ 2 ((𝓕.siegelHaar hK e ra τ rb).restrict (orthantBox (chamberCoords hK e) τ
        (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε (m P.1 ε))))
    (hT : ∀ P ε, IsCompactOperator (Tbox P ε))
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] {Par : Type*} (D : Par → B →L[ℂ] V)
    (s : Par) : IsCompactOperator (𝓕.boundaryRhs hK e ra τ rb m Tbox D s) := by
  refine isCompactOperator_piAssemble _ fun ω => ?_
  have hcore : IsCompactOperator (𝓕.boundaryRhsCore hK e ra τ rb m Tbox ω) := by
    rcases ω with ⟨P, ε, _ | k⟩
    · exact hT P ε
    · exact isCompactOperator_zero
  exact hcore.comp_clm (D s)

section Holomorphy

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E' H)
  {Par : Type*} [TopologicalSpace Par] [ChartedSpace H Par]

open scoped Classical in
theorem isHolomorphicOperatorFamilyOn_boundaryRhs (ra τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ)
    (rb : Fin r → ℝ)
    (m : ∀ (P : Finset (characterLattice 𝓕.T)) (_ε : Fin r → Bool), 𝓕.BoundaryDirection P r → ℕ)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Tbox : ∀ (P : {P // P ∈ 𝓕.simpleRootFinset.powerset}) (ε : Fin r → Bool),
      V →L[ℂ] Lp ℂ 2 ((𝓕.siegelHaar hK e ra τ rb).restrict (orthantBox (chamberCoords hK e) τ
        (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε (m P.1 ε))))
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] (D : Par → B →L[ℂ] V) (S : Set Par)
    (hD : IsHolomorphicOperatorFamilyOn I D S) :
    IsHolomorphicOperatorFamilyOn I (fun s => 𝓕.boundaryRhs hK e ra τ rb m Tbox D s) S :=
  IsHolomorphicOperatorFamilyOn.piAssemble fun ω =>
    hD.clm_comp (𝓕.boundaryRhsCore hK e ra τ rb m Tbox ω)

end Holomorphy

set_option maxHeartbeats 1600000 in
open RepresentationGrowth Langlands.Automorphic.GroupSchemeFunctions in
open scoped Classical in
/-- **Construction of the compact boundary model.** Assume `PositiveTorusSplitComponentStatement`.
Let `(u, t, z)` be local-finiteness group data for `𝓕` and `j : T₀ → T` a Siegel algebraic setup.
Let `K` be an Iwasawa subgroup of `P₀` with chamber coordinates `e` whose root coordinates of
`d_T h` are `h_α / step_α` (`step_α > 0`), whose vanishing central coordinates force
`H_G = 0`, and which send the logarithms of `t_α` and `z_j` to unit vectors. Let the rational
characters of `P₀` be free of finite rank, and let every `x ∈ G(𝔸)` have a rational translate
`q x` with finite part in a compact `Ω`, root coordinates at least `θ` and
`ht(q x) ≤ M ht(x)^{t'}`. Then for admissible data `X` of `Ξ_main`, every open compact level `L`
and every `s₀`, there are an index `i₀` with `c_{i₀}(s₀) ≠ 0`, Hilbert spaces `B`, `C` and a
boundary model of `X` for `i₀` at `s₀`. -/
theorem exists_boundaryModel (hsplit : PositiveTorusSplitComponentStatement.{u})
    {Ua : simpleRelativeRoots 𝓕.i 𝓕.ν → GroupScheme (Spec (CommRingCat.of F))}
    [∀ α, IsAffine (Ua α).X.left] {u : ∀ α, Ua α ⟶ G} [∀ α, IsClosedImmersion (u α).hom.hom.left]
    {t : simpleRelativeRoots 𝓕.i 𝓕.ν → AdelicGroupPoints F 𝓕.T.toGrp}
    {z : Fin r → AdelicGroupPoints F 𝓕.T.toGrp}
    (hdata : IsLocalFinitenessGroupData 𝓕.i 𝓕.ν u t z)
    {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ 𝓕.T)
    {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (rho : MatrixRepresentation G (Fin N)) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (dT : RealCharacterDual F 𝓕.T.toGrp ≃L[ℝ]
      RealCharacterDual F (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅))
    (step : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ)
    (hsetup : IsSiegelAlgebraicSetup F G 𝓕.T 𝓕.i 𝓕.ν T₀ j)
    (hd : ∀ h, dT h = realCharacterDualMap F 𝓕.T.toGrp (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅)
      (torusToStandardParabolic F G 𝓕.T 𝓕.i 𝓕.ν) h)
    (hstep : ∀ α, 0 < step α)
    (hRoot : ∀ (h : RealCharacterDual F 𝓕.T.toGrp) (α : simpleRelativeRoots 𝓕.i 𝓕.ν),
      (e (dT h)).1 α = h α.val / step α)
    (hCen : ∀ h : RealCharacterDual F 𝓕.T.toGrp, (e (dT h)).2 = 0 →
      realCharacterDualMap F 𝓕.T.toGrp G 𝓕.i h = 0)
    (het : ∀ α, e (characterLog F _ (map F 𝓕.T.toGrp _
      (torusToStandardParabolic F G 𝓕.T 𝓕.i 𝓕.ν) (t α))) = (Pi.single α 1, 0))
    (hez : ∀ j, e (characterLog F _ (map F 𝓕.T.toGrp _
      (torusToStandardParabolic F G 𝓕.T 𝓕.i 𝓕.ν) (z j))) = (0, Pi.single j 1))
    [Module.Free ℤ (rationalCharacters (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅))]
    [Module.Finite ℤ (rationalCharacters (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅))]
    (θ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (Ω : Set (FiniteAdelicGroupPoints F G))
    (hΩ : IsCompact Ω) (M t' : ℝ) (hM : 0 < M) (ht' : 0 ≤ t')
    (hY : ∀ x : AdelicGroupPoints F G, ∃ q : RationalGroupPoints F G,
      AdelicGroupPoints.finite F G (rational F G q * x) ∈ Ω ∧
      (∀ α, θ α ≤ (e (hK.height (rational F G q * x))).1 α) ∧
      adelicHeight F G rho (rational F G q * x) ≤ M * adelicHeight F G rho x ^ t')
    {n : ℕ} {W : TopologicalSpace.Opens (Fin n → ℂ)}
    (X : LocalFinitenessData F G (simpleRelativeRoots 𝓕.i 𝓕.ν) r n W) (hX : X.IsAdmissible)
    (L : Subgroup (FiniteAdelicGroupPoints F G)) (hLo : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    (hLc : IsCompact (L : Set (FiniteAdelicGroupPoints F G))) (s₀ : W) :
    ∃ (i₀ : X.Idx), X.c i₀ s₀ ≠ 0 ∧
      ∃ (B : Type u) (_ : NormedAddCommGroup B) (_ : InnerProductSpace ℂ B) (_ : CompleteSpace B)
        (C : Type u) (_ : NormedAddCommGroup C) (_ : InnerProductSpace ℂ C) (_ : CompleteSpace C),
        Nonempty (X.BoundaryModel u (fun α => map F 𝓕.T.toGrp G 𝓕.i (t α))
          (fun j => map F 𝓕.T.toGrp G 𝓕.i (z j)) rho hN hrho hsmooth hcalc L i₀ s₀ B C) := by
  -- the points `a_β = i(t_β)`, `z_j = i(z_j)` shift the chamber coordinates by unit vectors
  set a : simpleRelativeRoots 𝓕.i 𝓕.ν → AdelicGroupPoints F G :=
    fun α => map F 𝓕.T.toGrp G 𝓕.i (t α) with ha_def
  set zz : Fin r → AdelicGroupPoints F G := fun j => map F 𝓕.T.toGrp G 𝓕.i (z j) with hzz_def
  have hca : ∀ β g, chamberCoords hK e (a β * g) = chamberCoords hK e g + (Pi.single β 1, 0) := by
    intro β g
    have h := AdelicSiegelFactors.isCoordinateShift_torus hK
      (e.toLinearEquiv.toLinearMap) (t β) g
    unfold chamberCoords
    rw [← het β]
    exact h
  have hcz : ∀ j g, chamberCoords hK e (zz j * g) = chamberCoords hK e g + (0, Pi.single j 1) := by
    intro j g
    have h := AdelicSiegelFactors.isCoordinateShift_torus hK
      (e.toLinearEquiv.toLinearMap) (z j) g
    unfold chamberCoords
    rw [← hez j]
    exact h
  obtain ⟨haN, hzN⟩ := 𝓕.isLeviNormalizingPoint_of_groupData hsplit hdata
  -- the equation and its normalized coefficients
  obtain ⟨i₀, hi₀⟩ := hX.2.2.2.1 s₀
  have hc : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) (X.c i₀) univ :=
    hX.2.2.1 i₀ (ContinuousLinearMap.id ℂ ℂ)
  have hcC : Continuous (X.c i₀) := continuousOn_univ.mp hc.continuousOn
  -- the residual degrees and coefficients
  let Jx : Finset (characterLattice 𝓕.T) → simpleRelativeRoots 𝓕.i 𝓕.ν → Prop :=
    fun P β => β.val ∈ (𝓕.finsetIndex P).1
  let m : ∀ (P : Finset (characterLattice 𝓕.T)) (_ε : Fin r → Bool),
      𝓕.BoundaryDirection P r → ℕ := fun P _ k => X.dirDegree (Jx P) k
  let p : W → ∀ P ε k, Fin (m P ε k) → ℂ := fun s P ε k =>
    if P ∈ 𝓕.simpleRootFinset.powerset then X.dirCoeff (Jx P) s ε k else 0
  let Msum : W → ℝ := fun s => ∑ P ∈ 𝓕.simpleRootFinset.powerset, ∑ ε : Fin r → Bool,
    ∑ k : 𝓕.BoundaryDirection P r, ∑ q : Fin (m P ε k), ‖X.dirCoeff (Jx P) s ε k q‖
  have hMsum : Continuous Msum :=
    continuous_finsetSum _ fun P _ => continuous_finsetSum _ fun ε _ =>
      continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun q _ =>
        (continuousOn_univ.mp (X.mdifferentiableOn_dirCoeff hX (Jx P) ε k q).continuousOn).norm
  have hpbound : ∀ s P ε k, ∑ q, ‖p s P ε k q‖ ≤ Msum s := by
    intro s P ε k
    by_cases hP : P ∈ 𝓕.simpleRootFinset.powerset
    · simp only [p, hP, ↓reduceIte]
      refine le_trans ?_ (Finset.single_le_sum (f := fun P => ∑ ε : Fin r → Bool,
        ∑ k : 𝓕.BoundaryDirection P r, ∑ q : Fin (m P ε k), ‖X.dirCoeff (Jx P) s ε k q‖)
        (fun P _ => by positivity) hP)
      refine le_trans ?_ (Finset.single_le_sum (f := fun ε =>
        ∑ k : 𝓕.BoundaryDirection P r, ∑ q : Fin (m P ε k), ‖X.dirCoeff (Jx P) s ε k q‖)
        (fun ε _ => by positivity) (Finset.mem_univ ε))
      exact Finset.single_le_sum (f := fun k => ∑ q : Fin (m P ε k), ‖X.dirCoeff (Jx P) s ε k q‖)
        (fun k _ => by positivity) (Finset.mem_univ k)
    · simp only [p, hP, ↓reduceIte, Pi.zero_apply, norm_zero, Finset.sum_const_zero]
      positivity
  set Mc : ℝ := Msum s₀ + 1 with hMc
  let S : Set W := {s | X.c i₀ s ≠ 0 ∧ Msum s < Mc}
  have hSo : IsOpen S := (isOpen_ne_fun hcC continuous_const).inter
    (isOpen_lt hMsum continuous_const)
  have hs₀S : s₀ ∈ S := ⟨hi₀, lt_add_one _⟩
  have hpS : ∀ s ∈ S, ∀ P ε k, ∑ q, ‖p s P ε k q‖ ≤ Mc := fun s hs P ε k =>
    (hpbound s P ε k).trans hs.2.le
  have hp : ∀ P ε k q, MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) (fun s => p s P ε k q) S := by
    intro P ε k q
    by_cases hP : P ∈ 𝓕.simpleRootFinset.powerset
    · exact ((X.mdifferentiableOn_dirCoeff hX (Jx P) ε k q).mono (subset_univ S)).congr
        fun s _ => by simp only [p, hP, ↓reduceIte]
    · exact (mdifferentiableOn_const (c := (0 : ℂ))).congr fun s _ => by
        simp only [p, hP, ↓reduceIte, Pi.zero_apply]
  have hb : ∀ k, MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) (X.normalizedCoefficient i₀ k) S := by
    intro k
    have hbk : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) (X.b i₀ k) univ :=
      hX.2.1 i₀ k (ContinuousLinearMap.id ℂ ℂ)
    exact (hbk.mono (subset_univ S)).div (hc.mono (subset_univ S)) (fun _ hs => hs.1)
  -- level-averaged kernels, left invariant under `L`
  obtain ⟨L', -, -, hfin, hL'inv⟩ := exists_common_level (X.h i₀) (hX.1 i₀) hLo hLc
  have := hfin
  let h' : Fin (X.m i₀) → AdelicGroupPoints F G → ℂ := fun k => levelAverage L L' (X.h i₀ k)
  have hh' : ∀ k, IsAdelicTestFunction F G (h' k) := fun k =>
    isAdelicTestFunction_levelAverage hLo (hX.1 i₀ k) (hL'inv k)
  have hh'L : ∀ k, ∀ l ∈ L, ∀ x, h' k (ofFinite F G l * x) = h' k x := fun k l hl x =>
    levelAverage_mul_left (hL'inv k) hl x
  -- the margin of the smoothing operators, and the Siegel threshold
  obtain ⟨δ, hδ, hsm⟩ := WeightedSiegel.exists_smoothingOperators hK rho hN hrho hsmooth hcalc e θ
    Ω hΩ M t' hM ht' hY h' hh'
  let τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ := fun α => θ α - δ - 1
  have hτ : ∀ α, τ α + δ < θ α := fun α => by simp only [τ]; linarith
  -- rate thresholds
  obtain ⟨Rres, hRres, hres⟩ := 𝓕.exists_residualOperators hK e a zz hca hcz haN hzN τ Mc
  let Idx := {P // P ∈ 𝓕.simpleRootFinset.powerset}
  obtain ⟨Remb, hRemb, hemb⟩ := StandardConstantTerm.exists_chamberEmbedding hK
    𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic e a zz hca hcz
    (fun β J hJ hβ => haN β J hJ hβ) (fun j J hJ => hzN j J hJ)
    (J := fun P : Idx => (𝓕.finsetIndex P.1).1) (fun P => (𝓕.finsetIndex P.1).2) τ Mc
  obtain ⟨cBC, hcBC, hBC⟩ := 𝓕.exists_boxBoundaryOperator j hsmooth rho hcalc hN hrho dT e step
    𝓕.connectedReductive hsetup hd hstep hRoot hCen hK
  obtain ⟨cBC₀, -, hBC₀⟩ := 𝓕.exists_boxBoundaryOperator.{u, 0} j hsmooth rho hcalc hN hrho dT e
    step 𝓕.connectedReductive hsetup hd hstep hRoot hCen hK
  set ρ0 : ℝ := max (max Rres cBC₀) (max Remb cBC) with hρ0
  have hρres : Rres ≤ ρ0 := (le_max_left _ _).trans (le_max_left _ _)
  have hρBC₀ : cBC₀ ≤ ρ0 := (le_max_right _ _).trans (le_max_left _ _)
  have hρemb : Remb ≤ ρ0 := (le_max_left _ _).trans (le_max_right _ _)
  have hρBC : cBC ≤ ρ0 := (le_max_right _ _).trans (le_max_right _ _)
  have hρpos : 0 < ρ0 := hcBC.trans_le hρBC
  let ra : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ := fun _ => ρ0
  let rb : Fin r → ℝ := fun _ => ρ0
  -- the polynomial bound of the weight
  obtain ⟨-, hexp, -⟩ := adelicLocalFinitenessChamberWeight hK rho e ra rb (fun _ => hρpos.le)
  obtain ⟨Wc, r', hWc, hr', hweight⟩ := hexp hN hrho
  -- the smoothing operators
  obtain ⟨R₀, hR₀, hsmR⟩ := hsm τ hτ ra rb Wc r' hWc hr' hweight
  obtain ⟨Ksm, hKsm⟩ := hsmR R₀ le_rfl L hh'L
  -- the left-hand operators
  obtain ⟨E, Lsh, hE, hLsh, -, hbd⟩ := hres ra rb (fun _ => hρres) (fun _ => hρres)
  -- the box operators on the smoothed vector
  let B := 𝓕.siegelHilbert hK e ra τ rb
  let Fib : Fin (X.m i₀) → Type u := fun _ => B
  let smoothSum : PiLp 2 Fib →L[ℂ] UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R₀ L :=
    ∑ k, Ksm k ∘L PiLp.proj (p := 2) (𝕜 := ℂ) (β := Fib) k
  have hT := fun (P : Idx) (ε : Fin r → Bool) => hBC ra rb (fun _ => hρBC) (fun _ => hρBC) τ P.1 ε
    (m P.1 ε) R₀ hR₀ L hLo (PiLp 2 Fib) smoothSum
  choose Tbox hTc hTae using hT
  let D : W → B →L[ℂ] PiLp 2 Fib := fun s =>
    piAssemble fun k => X.normalizedCoefficient i₀ k s • ContinuousLinearMap.id ℂ B
  have hD : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, Fin n → ℂ) D S := by
    refine IsHolomorphicOperatorFamilyOn.piAssemble fun k => ?_
    intro v φ
    refine ((hb k).mul (mdifferentiableOn_const (c := φ v))).congr fun s _ => ?_
    simp only [_root_.smul_apply, map_smul, smul_eq_mul]
    rfl
  have hsmoothD : ∀ s (y : B),
      smoothSum (D s y) = (∑ k, X.normalizedCoefficient i₀ k s • Ksm k) y := by
    intro s y
    simp only [smoothSum, D, _root_.sum_apply, ContinuousLinearMap.comp_apply,
      _root_.smul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    change Ksm k (X.normalizedCoefficient i₀ k s • y) = _
    rw [map_smul]
  have hexpand : ∀ (c : Fin (X.m i₀) → ℂ) (y : B) g,
      UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R₀ L
          ((∑ k, c k • Ksm k) y) g =
        ∑ k, c k * UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R₀ L
          (Ksm k y) g := by
    intro c y g
    change UniformGrowthFrechetSpace.evaluation F G rho hsmooth hcalc hN hrho R₀ L g
        ((∑ k, c k • Ksm k) y) =
      ∑ k, c k * UniformGrowthFrechetSpace.evaluation F G rho hsmooth hcalc hN hrho R₀ L g
        (Ksm k y)
    rw [_root_.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [_root_.smul_apply, map_smul, smul_eq_mul]
  have hcompat : ∀ y : B, (∑ k, X.normalizedCoefficient i₀ k s₀ • Ksm k) y = 0 →
      𝓕.boundaryRhs hK e ra τ rb m Tbox D s₀ y = 0 := by
    intro y hy
    refine PiLp.ext fun ω => ?_
    rcases ω with ⟨P, ε, _ | k⟩
    · rw [PiLp.zero_apply]
      change Tbox P ε (D s₀ y) = 0
      have heq : smoothSum (D s₀ y) = smoothSum 0 := by rw [hsmoothD, hy, map_zero]
      have h1 := hTae P ε (D s₀ y)
      rw [heq] at h1
      have h2 : Tbox P ε (D s₀ y) = Tbox P ε 0 := Lp.ext (h1.trans (hTae P ε 0).symm)
      rw [h2, map_zero]
    · rw [PiLp.zero_apply]
      rfl
  -- the quotient map is measure preserving from the Siegel measure to the automorphic measure
  have hmpG : MeasurePreserving (LeftCosetSpace.mk (rationalSubgroup F G))
      (𝓕.siegelHaar hK e ra τ rb)
      (WeightedSiegel.automorphicMeasure F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK
        (localFinitenessLogWeight ra rb ∘ e)
        (WeightedSiegel.domainHeight F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK ⁻¹'
          WeightedSiegel.siegelHeightRegion (⇑e) τ)) :=
    ((WeightedSiegel.measurePreserving_toAutomorphic F _ hK _ _).comp
      (WeightedSiegel.measurePreserving_mk_frameMeasure hK _ (𝓕.continuous_siegelLogWeight e ra rb)
        _ (𝓕.measurableSet_siegelHeightRegion e τ))).comp
      (𝓕.measurePreserving_id_siegelHaar hK e ra τ rb)
  have hlift : ∀ s ∈ S, ∀ R, R₀ ≤ R →
      ∀ f ∈ X.solutions u a zz rho hN hrho hsmooth hcalc R L s,
      ∃ y : B, 𝓕.boundaryLhs hK e ra τ rb E Lsh m p s y = 𝓕.boundaryRhs hK e ra τ rb m Tbox D s y ∧
        ∀ g, UniformGrowthFrechetSpace.evaluation F G rho hsmooth hcalc hN hrho R₀ L g
            ((∑ k, X.normalizedCoefficient i₀ k s • Ksm k) y) =
          ∑ k, X.normalizedCoefficient i₀ k s * rightConvolution F G (X.h i₀ k)
            (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L f) g := by
    intro s hs R hR f hf
    let φf := UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L f
    have hφc : Continuous φf :=
      (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val.val.property
    have hφm : Measurable φf := hφc.measurable
    have hφP : ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, φf (l * x) = φf x := by
      intro l hl x
      obtain ⟨q, hq⟩ := minimalParabolicImage_le F G 𝓕.i 𝓕.ν hl
      rw [← hq]
      exact evaluate_rational_mul F G _ q x
    have hφrat : ∀ (q : rationalSubgroup F G) (x : AdelicGroupPoints F G),
        φf ((q : AdelicGroupPoints F G) * x) = φf x := by
      rintro ⟨_, q, rfl⟩ x
      exact evaluate_rational_mul F G _ q x
    have hφL : ∀ l ∈ L, ∀ x, φf (x * ofFinite F G l) = φf x := by
      intro l hl x
      have h := (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).property.1 l hl
      exact congrArg (fun w : FinitePlotSmoothRationalFunctions F G => evaluate F G w.val x) h
    -- the Harish-Chandra components of `φf`
    have hφeq : ∀ P, 𝓕.hcComponent P φf = alternatingSum (fun S => 𝓕.componentFoldCT S φf) P :=
      fun P => 𝓕.hcComponent_eq_alternatingSum_componentFoldCT P hφm hφP
    let φ : Idx → AdelicGroupPoints F G → ℂ := fun P => 𝓕.hcComponent P.1 φf
    have hφm' : ∀ P : Idx, Measurable (φ P) := by
      intro P
      have h := Finset.measurable_sum P.1.powerset
        (f := fun S => ((-1 : ℂ) ^ (P.1 \ S).card) • 𝓕.componentFoldCT S φf)
        fun S _ => (𝓕.measurable_componentFoldCT S hφm).const_smul _
      convert h using 1
      funext x
      simp [φ, hφeq, alternatingSum, Finset.sum_apply]
    have hφinv : ∀ P : Idx, ∀ h ∈ cosetSubgroup F G 𝓕.i 𝓕.ν (𝓕.finsetIndex P.1).1, ∀ g,
        φ P (h * g) = φ P g := by
      intro P
      simp only [φ, hφeq]
      refine invariant_sup _ _ _ (fun l hl x => ?_) (fun w hw x => ?_)
      · simp only [alternatingSum, Finset.sum_apply, Pi.smul_apply]
        exact Finset.sum_congr rfl fun S hS => by
          rw [(𝓕.componentFoldCT_invariant (Finset.mem_powerset.mp hS) φf).1 l hl x]
      · simp only [alternatingSum, Finset.sum_apply, Pi.smul_apply]
        exact Finset.sum_congr rfl fun S hS => by
          rw [(𝓕.componentFoldCT_invariant (Finset.mem_powerset.mp hS) φf).2 w hw x]
    have hsum : φf =ᵐ[𝓕.siegelHaar hK e ra τ rb] fun g => ∑ P, φ P g := by
      refine Filter.Eventually.of_forall fun g => ?_
      have h := congrFun (𝓕.sum_hcComponent φf) g
      rw [Finset.sum_apply, ← Finset.sum_coe_sort] at h
      exact h.symm
    have hboxM : ∀ (P : Idx) ε, MemLp (φ P) 2 ((𝓕.siegelHaar hK e ra τ rb).restrict
        (orthantBox (chamberCoords hK e) τ
          (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε (m P.1 ε))) := by
      intro P ε
      obtain ⟨T1, -, hT1⟩ := hBC₀ ra rb (fun _ => hρBC₀) (fun _ => hρBC₀) τ P.1 ε (m P.1 ε) R
        (hR₀.trans hR) L hLo ℂ ((ContinuousLinearMap.id ℂ ℂ).smulRight f)
      have h1 := hT1 1
      have hone : (ContinuousLinearMap.id ℂ ℂ).smulRight f 1 = f := by simp
      rw [hone] at h1
      exact (Lp.memLp (T1 1)).ae_eq h1
    have hbd' : ∀ (P : Idx) ε k, ∑ q, ‖p s P.1 ε k q‖ ≤ Mc := fun P => hpS s hs P.1
    have hemb' := hemb ra rb (fun _ => hρemb) (fun _ => hρemb) (fun P => m P.1)
      (fun P => p s P.1) hbd'
    obtain ⟨Cm, -, hCm⟩ := hemb'
    have hCm1 := hCm φf φ hφm hφm' hφinv
    have hCm2 := hCm1 hsum
    have hCm3 := hCm2 hboxM
    have hCm4 := hCm3 (fun P ε k => by
      have hz := 𝓕.residualFun_hcComponent_eq_zero hsplit hdata X hX rho hN hrho hsmooth hcalc R
        L s hf P.1 ε k
      have hpP : p s P.1 ε k = X.dirCoeff (Jx P.1) s ε k := by simp only [p, P.2, ↓reduceIte]
      have hzero : residualFun F G (orthantShift a zz
          (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε k)
          (p s P.1 ε k) (𝓕.hcComponent P.1 φf) = 0 := by
        rw [hpP]
        exact hz
      exact MemLp.zero.ae_eq (Filter.EventuallyEq.of_eq hzero.symm))
    obtain ⟨hφmem, -⟩ := hCm4
    -- descent to the quotient
    let fbar : RationalQuotient F G → ℂ := LeftCosetSpace.lift (rationalSubgroup F G) φf hφrat
    have hfbarm : Measurable fbar := measurable_from_quotient.mpr hφm
    have hfbar : fbar ∘ LeftCosetSpace.mk (rationalSubgroup F G) = φf :=
      funext fun g => LeftCosetSpace.lift_mk (rationalSubgroup F G) φf hφrat g
    clear_value fbar
    have hmem : MemLp fbar 2 (WeightedSiegel.automorphicMeasure F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK
        (localFinitenessLogWeight ra rb ∘ e)
        (WeightedSiegel.domainHeight F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK ⁻¹'
          WeightedSiegel.siegelHeightRegion (⇑e) τ)) := by
      rw [← hmpG.map_eq]
      refine (memLp_map_measure_iff hfbarm.aestronglyMeasurable hmpG.measurable.aemeasurable).mpr ?_
      rw [hfbar]
      exact hφmem
    let y : B := hmem.toLp fbar
    have hyae : ⇑y =ᵐ[WeightedSiegel.automorphicMeasure F
        (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK (localFinitenessLogWeight ra rb ∘ e)
        (WeightedSiegel.domainHeight F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK ⁻¹'
          WeightedSiegel.siegelHeightRegion (⇑e) τ)] fbar := hmem.coeFn_toLp
    clear_value y
    have hcomp : (⇑y ∘ LeftCosetSpace.mk (rationalSubgroup F G)) =ᵐ[𝓕.siegelHaar hK e ra τ rb]
        fbar ∘ LeftCosetSpace.mk (rationalSubgroup F G) :=
      hmpG.quasiMeasurePreserving.ae_eq_comp hyae
    rw [hfbar] at hcomp
    have hembx : ⇑(𝓕.siegelEmbedding hK e ra τ rb y) =ᵐ[𝓕.siegelHaar hK e ra τ rb] φf :=
      (𝓕.siegelEmbedding_ae hK e ra τ rb y).trans hcomp
    -- the smoothed vector is `φf`
    have hsol := hf.1 i₀
    have hloc : LocallyIntegrable φf (Measure.haar : Measure (AdelicGroupPoints F G)) :=
      hφc.locallyIntegrable
    have havg : ∀ g, ∑ k, X.b i₀ k s * rightConvolution F G (h' k) φf g = X.c i₀ s * φf g :=
      fun g => sum_rightConvolution_levelAverage (L := L) (L' := L') Finset.univ (X.h i₀)
        (fun k => X.b i₀ k s) (X.c i₀ s) (fun k => (hX.1 i₀ k).1.1) (fun k => (hX.1 i₀ k).2.1)
        hloc hφL hsol g
    have hnorm : ∀ g (A : Fin (X.m i₀) → ℂ), ∑ k, X.b i₀ k s * A k = X.c i₀ s * φf g →
        ∑ k, X.normalizedCoefficient i₀ k s * A k = φf g := by
      intro g A hA
      have hdiv : ∑ k, X.normalizedCoefficient i₀ k s * A k =
          (∑ k, X.b i₀ k s * A k) / X.c i₀ s := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [LocalFinitenessData.normalizedCoefficient]
        ring
      rw [hdiv, hA, mul_div_cancel_left₀ _ hs.1]
    have hvx : ∀ g, UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R₀ L
        ((∑ k, X.normalizedCoefficient i₀ k s • Ksm k) y) g = φf g := by
      intro g
      rw [hexpand]
      refine hnorm g _ ?_
      rw [← havg g]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hKsm k y fbar hfbarm hyae.symm g, hfbar]
    have htoFun : UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R₀ L
        (smoothSum (D s y)) = φf := funext fun g => by rw [hsmoothD]; exact hvx g
    refine ⟨y, PiLp.ext fun ω => ?_, fun g => ?_⟩
    · rcases ω with ⟨P, ε, _ | k⟩
      · change LpToLpRestrictCLM (AdelicGroupPoints F G) ℂ ℂ (𝓕.siegelHaar hK e ra τ rb) 2 _
          (E P.1 (𝓕.siegelEmbedding hK e ra τ rb y)) = Tbox P ε (D s y)
        apply Lp.ext
        have h1 := LpToLpRestrictCLM_coeFn ℂ (orthantBox (chamberCoords hK e) τ
          (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε (m P.1 ε))
          (E P.1 (𝓕.siegelEmbedding hK e ra τ rb y))
        have h2 := (hE P.1 (𝓕.siegelEmbedding hK e ra τ rb y) hφm hembx.symm).trans
          (Filter.EventuallyEq.of_eq (hφeq P.1).symm)
        have h3 := (hTae P ε (D s y)).trans
          (Filter.EventuallyEq.of_eq (congrArg (𝓕.hcComponent P.1) htoFun))
        exact h1.trans (Filter.EventuallyEq.trans (ae_restrict_of_ae h2) h3.symm)
      · change LpToLpRestrictCLM (AdelicGroupPoints F G) ℂ ℂ (𝓕.siegelHaar hK e ra τ rb) 2 _
          (residualOperator (Lsh P.1 ε k) (p s P.1 ε k) (𝓕.siegelEmbedding hK e ra τ rb y)) =
            (0 : PiLp 2 Fib →L[ℂ] _) (D s y)
        rw [_root_.zero_apply]
        apply Lp.ext
        have hz := 𝓕.residualFun_hcComponent_eq_zero hsplit hdata X hX rho hN hrho hsmooth hcalc R
          L s hf P.1 ε k
        have hpP : p s P.1 ε k = X.dirCoeff (Jx P.1) s ε k := by simp only [p, P.2, ↓reduceIte]
        have hzero : residualFun F G (orthantShift a zz
            (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε k)
            (p s P.1 ε k) (alternatingSum (fun S => 𝓕.componentFoldCT S φf) P.1) = 0 := by
          rw [← hφeq, hpP]
          exact hz
        have hr := residualOperator_ae (Lsh P.1 ε k) (orthantShift a zz
          (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε k)
          (alternatingSum (fun S => 𝓕.componentFoldCT S φf) P.1)
          (𝓕.siegelEmbedding hK e ra τ rb y) (fun q => hLsh P.1 ε k q _ hφm hembx.symm)
          (p s P.1 ε k)
        rw [hzero] at hr
        have h1 := LpToLpRestrictCLM_coeFn ℂ (orthantPos (chamberCoords hK e) τ
          (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε)
          (residualOperator (Lsh P.1 ε k) (p s P.1 ε k) (𝓕.siegelEmbedding hK e ra τ rb y))
        exact h1.trans (Filter.EventuallyEq.trans (ae_restrict_of_ae hr) (Lp.coeFn_zero ℂ 2 _).symm)
    · exact (hvx g).trans (hnorm g _ (hsol g)).symm
  have hEmb : Topology.IsEmbedding (𝓕.boundaryLhs hK e ra τ rb E Lsh m p s₀) := by
    obtain ⟨Cb, hCb, hbound⟩ := hbd m (p s₀) (hpS s₀ hs₀S)
    exact 𝓕.isEmbedding_boundaryLhs hK e ra τ rb E Lsh m p s₀ hCb hbound
  exact ⟨i₀, hi₀, B, inferInstance, inferInstance, inferInstance, _, inferInstance, inferInstance,
    inferInstance, ⟨{
      S := S
      isOpen_S := hSo
      mem_S := hs₀S
      R₀ := R₀
      lhs := fun s => 𝓕.boundaryLhs hK e ra τ rb E Lsh m p s
      rhs := fun s => 𝓕.boundaryRhs hK e ra τ rb m Tbox D s
      holomorphic_lhs := 𝓕.isHolomorphicOperatorFamilyOn_boundaryLhs hK e 𝓘(ℂ, Fin n → ℂ) ra τ rb
        E Lsh m p S hp
      holomorphic_rhs := 𝓕.isHolomorphicOperatorFamilyOn_boundaryRhs hK e 𝓘(ℂ, Fin n → ℂ) ra τ rb
        m Tbox D S hD
      embedding_lhs := hEmb
      compact_rhs := 𝓕.isCompactOperator_boundaryRhs hK e ra τ rb m Tbox hTc D s₀
      K := Ksm
      compatible := hcompat
      lift_solution := hlift }⟩⟩

end Langlands.Global.StandardParabolicFamily

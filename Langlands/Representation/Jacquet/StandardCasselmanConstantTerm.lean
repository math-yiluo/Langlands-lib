import Langlands.Representation.Jacquet.StandardCasselmanPairing
import Langlands.Representation.Jacquet.StandardFixedVectorStructure
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RightFiniteUniqueness
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen
import Langlands.Group.HaarModulus

/-! # Waldspurger's Proposition I.6.2 for actual standard parabolic subgroups

For the actual standard parabolic `P_J = M_J U_J` of a connected reductive group, with Renard's
structural data of V.5.2 (a basis of compact open subgroups normal in `K₀`, a compatible split
component `A` of `M_J`, a standard cocharacter for `J`), every `f ∈ A(G)` has a unique constant
term `f_P ∈ A(M_J)`: for every `m ∈ M_J` there is `ε > 0` with
`δ(m a)^{-1/2} f(m a) = f_P(m a)` for every `a ∈ A(F)` with `|α(a)|_F < ε` on `Δ(P_J)`, where `δ`
is the Haar modulus of conjugation on `U_J(F)`. This is the source's cone, on the whole split
component. The constant term is also unchanged by right translation by `U_J(F)` and left
translation by `Ū_J(F)`.
-/

noncomputable section

universe u uV uW uG

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Jacquet

/-- The constant term `coefficientConstantTerm` at `m` is `δ(m)^{-1/2} ℓ(ρ(m) v)` as soon as the
asymptotic identity `ℓ(ρ(m) v) = b [ℓ] [ρ(m) v]` holds at `m`. -/
theorem StablePairingData.inv_sqrt_mul_eq_coefficientConstantTerm {G : Type uG} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (D : StablePairingData G) (ρ : Representation ℂ G V)
    (b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ] Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ)
    (δ : D.M →* ℝ≥0ˣ) (ℓ : SmoothDual ρ) (v : V) (m : D.M)
    (h : smoothDualPairing ρ ℓ (ρ m v) =
      b (Jacquet.mk (smoothContragredient ρ) D.N ℓ) (Jacquet.mk ρ D.Nbar (ρ m v))) :
    (((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ))⁻¹ * smoothDualPairing ρ ℓ (ρ m v) =
      D.coefficientConstantTerm ρ b δ ℓ v m := by
  rw [h]
  simp only [StablePairingData.coefficientConstantTerm, normalizedActionOfModulus_mk, map_smul,
    smul_eq_mul]

end Langlands.Jacquet

namespace Langlands.BruhatTits.SpecialCompact

section ConstantTerm

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup

local instance standardConstantTermT2Field : T2Space F := BruhatTits.localField_t2Space F
local instance standardConstantTermLocallyCompact : LocallyCompactSpace (rationalPoints G) :=
  rationalPoint_locallyCompactSpace F G
local instance standardConstantTermNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The actual points of a compatible split component `A` of `M_J`, as elements of `M_J(F)`. -/
def standardComponentHom (hA : IsCompatibleStandardSplitComponent i ν J A q) :
    rationalPoints A.toGrp →* standardLeviPoints i ν J :=
  (rationalPoints.map (q ≫ i)).codRestrict _ (hA.map_mem_standardLeviPoints i ν)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem coe_standardComponentHom (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (x : rationalPoints A.toGrp) :
    ((standardComponentHom hA x : standardLeviPoints i ν J) : rationalPoints G) =
      rationalPoints.map (q ≫ i) x :=
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The image of `A(F)` is central in `M_J(F)`. -/
theorem standardComponentHom_commute (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (x : rationalPoints A.toGrp) (m : standardLeviPoints i ν J) :
    standardComponentHom hA x * m = m * standardComponentHom hA x :=
  Subtype.ext (hA.map_commute x m.2).symm

variable (i ν J) in
/-- **The radical modulus `δ_{U_J}`** on `M_J(F)`: the Haar modulus of conjugation by `M_J(F)` on
the closed radical `U_J(F)`. -/
def standardRadicalModulus : standardLeviPoints i ν J →* ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter (standardUnipotentPoints i ν J)
    (isClosed_standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)

theorem isOpen_ker_standardRadicalModulus :
    IsOpen ((standardRadicalModulus i ν J).ker : Set (standardLeviPoints i ν J)) :=
  HaarModulus.isOpen_ker_closedRestrictCharacter _ _ _ _

variable (i ν J) in
/-- `δ_{U_J}(m)^{1/2}` as a complex number. -/
def standardHalfModulus (m : standardLeviPoints i ν J) : ℂ :=
  ((NNReal.sqrt (standardRadicalModulus i ν J m : ℝ≥0) : ℝ) : ℂ)

theorem standardHalfModulus_mul (m m' : standardLeviPoints i ν J) :
    standardHalfModulus i ν J (m * m') =
      standardHalfModulus i ν J m * standardHalfModulus i ν J m' := by
  simp only [standardHalfModulus, map_mul, Units.val_mul, NNReal.sqrt_mul, NNReal.coe_mul,
    Complex.ofReal_mul]

theorem standardHalfModulus_ne_zero (m : standardLeviPoints i ν J) :
    standardHalfModulus i ν J m ≠ 0 := by
  simp [standardHalfModulus, (standardRadicalModulus i ν J m).ne_zero]

variable (i ν J q) in
/-- **The source's cone** in `A(F)`: the points `x` with `|α(x)|_F < ε` for every
`α ∈ Δ(P_J)` (the restrictions to `A` of the simple roots outside `J`). -/
def standardCone (ε : ℝ) : Set (rationalPoints A.toGrp) :=
  {x | ∀ α ∈ standardParabolicComponentCharacters i ν J q,
    CocharacterUniformizer.characterNorm F A α x < ε}

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem characterNorm_mul' (α : characterLattice A) (a b : rationalPoints A.toGrp) :
    CocharacterUniformizer.characterNorm F A α (a * b) =
      CocharacterUniformizer.characterNorm F A α a *
        CocharacterUniformizer.characterNorm F A α b := by
  simp [CocharacterUniformizer.characterNorm]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem characterNorm_pow' (α : characterLattice A) (a : rationalPoints A.toGrp) (n : ℕ) :
    CocharacterUniformizer.characterNorm F A α (a ^ n) =
      CocharacterUniformizer.characterNorm F A α a ^ n := by
  simp [CocharacterUniformizer.characterNorm]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem characterNorm_nonneg' (α : characterLattice A) (a : rationalPoints A.toGrp) :
    0 ≤ CocharacterUniformizer.characterNorm F A α a :=
  NNReal.coe_nonneg _

/-- **The constant-term property of Waldspurger's Proposition I.6.2** for the actual standard
parabolic `P_J`: `f_P` on `M_J(F)` is a constant term of `f` on `G(F)` if for every `m ∈ M_J(F)`
there is `ε > 0` with `δ(m a)^{-1/2} f(m a) = f_P(m a)` for every `a` in the image of the cone
`standardCone i ν J q ε` of `A(F)`. Here `δ = δ_{U_J}` (`standardRadicalModulus`). -/
def IsStandardConstantTerm (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (f : rationalPoints G → ℂ) (fP : standardLeviPoints i ν J → ℂ) : Prop :=
  ∀ m : standardLeviPoints i ν J, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ standardCone i ν J q ε,
    (standardHalfModulus i ν J (m * standardComponentHom hA x))⁻¹ *
        f ((m * standardComponentHom hA x : standardLeviPoints i ν J) : rationalPoints G) =
      fP (m * standardComponentHom hA x)

variable (hA : IsCompatibleStandardSplitComponent i ν J A q)

theorem isStandardConstantTerm_zero : IsStandardConstantTerm hA 0 0 :=
  fun _ => ⟨1, one_pos, fun _ _ => by simp⟩

theorem IsStandardConstantTerm.add {f₁ f₂ : rationalPoints G → ℂ}
    {g₁ g₂ : standardLeviPoints i ν J → ℂ} (h₁ : IsStandardConstantTerm hA f₁ g₁)
    (h₂ : IsStandardConstantTerm hA f₂ g₂) : IsStandardConstantTerm hA (f₁ + f₂) (g₁ + g₂) := by
  intro m
  obtain ⟨ε₁, hε₁, e₁⟩ := h₁ m
  obtain ⟨ε₂, hε₂, e₂⟩ := h₂ m
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun x hx => ?_⟩
  have hx₁ : x ∈ standardCone i ν J q ε₁ := fun α hα => (hx α hα).trans_le (min_le_left _ _)
  have hx₂ : x ∈ standardCone i ν J q ε₂ := fun α hα => (hx α hα).trans_le (min_le_right _ _)
  simp only [Pi.add_apply, mul_add, e₁ x hx₁, e₂ x hx₂]

theorem IsStandardConstantTerm.smul {f : rationalPoints G → ℂ}
    {g : standardLeviPoints i ν J → ℂ} (h : IsStandardConstantTerm hA f g) (c : ℂ) :
    IsStandardConstantTerm hA (c • f) (c • g) := by
  intro m
  obtain ⟨ε, hε, e⟩ := h m
  refine ⟨ε, hε, fun x hx => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, ← e x hx]
  ring

/-- **Right translation by the Levi.** If `f_P` is a constant term of `f`, then
`y ↦ δ(m₀)^{1/2} f_P(y m₀)` is a constant term of `x ↦ f(x m₀)`. -/
theorem IsStandardConstantTerm.mul_right {f : rationalPoints G → ℂ}
    {g : standardLeviPoints i ν J → ℂ} (h : IsStandardConstantTerm hA f g)
    (m₀ : standardLeviPoints i ν J) :
    IsStandardConstantTerm hA (fun x => f (x * (m₀ : rationalPoints G)))
      (fun y => standardHalfModulus i ν J m₀ * g (y * m₀)) := by
  intro m
  obtain ⟨ε, hε, e⟩ := h (m * m₀)
  refine ⟨ε, hε, fun x hx => ?_⟩
  have key := e x hx
  set c := standardComponentHom hA x
  have hcomm : c * m₀ = m₀ * c := standardComponentHom_commute hA x m₀
  have hc : m * c * m₀ = m * m₀ * c := by
    rw [mul_assoc, hcomm, ← mul_assoc]
  have hpt : ((m * c : standardLeviPoints i ν J) : rationalPoints G) * (m₀ : rationalPoints G) =
      ((m * m₀ * c : standardLeviPoints i ν J) : rationalPoints G) := by
    rw [← hc]
    rfl
  have hδ : standardHalfModulus i ν J (m * m₀ * c) =
      standardHalfModulus i ν J (m * c) * standardHalfModulus i ν J m₀ := by
    rw [← hc, standardHalfModulus_mul]
  rw [hδ] at key
  change (standardHalfModulus i ν J (m * c))⁻¹ *
      f (((m * c : standardLeviPoints i ν J) : rationalPoints G) * (m₀ : rationalPoints G)) =
    standardHalfModulus i ν J m₀ * g (m * c * m₀)
  rw [hpt, hc, ← key, mul_inv]
  have h₁ := standardHalfModulus_ne_zero (i := i) (ν := ν) (J := J) m₀
  have h₂ := standardHalfModulus_ne_zero (i := i) (ν := ν) (J := J) (m * c)
  field_simp

/-- **Left translation by the Levi.** If `f_P` is a constant term of `f`, then
`y ↦ δ(m₀)^{1/2} f_P(m₀ y)` is a constant term of `x ↦ f(m₀ x)`. -/
theorem IsStandardConstantTerm.mul_left {f : rationalPoints G → ℂ}
    {g : standardLeviPoints i ν J → ℂ} (h : IsStandardConstantTerm hA f g)
    (m₀ : standardLeviPoints i ν J) :
    IsStandardConstantTerm hA (fun x => f ((m₀ : rationalPoints G) * x))
      (fun y => standardHalfModulus i ν J m₀ * g (m₀ * y)) := by
  intro m
  obtain ⟨ε, hε, e⟩ := h (m₀ * m)
  refine ⟨ε, hε, fun x hx => ?_⟩
  have key := e x hx
  set c := standardComponentHom hA x
  have hδ : standardHalfModulus i ν J (m₀ * m * c) =
      standardHalfModulus i ν J m₀ * standardHalfModulus i ν J (m * c) := by
    rw [mul_assoc, standardHalfModulus_mul]
  rw [hδ] at key
  change (standardHalfModulus i ν J (m * c))⁻¹ *
      f ((m₀ : rationalPoints G) * ((m * c : standardLeviPoints i ν J) : rationalPoints G)) =
    standardHalfModulus i ν J m₀ * g (m₀ * (m * c))
  have hpt : (m₀ : rationalPoints G) * ((m * c : standardLeviPoints i ν J) : rationalPoints G) =
      ((m₀ * m * c : standardLeviPoints i ν J) : rationalPoints G) := by
    rw [mul_assoc]
    rfl
  rw [hpt, ← mul_assoc, ← key, mul_inv]
  have h₁ := standardHalfModulus_ne_zero (i := i) (ν := ν) (J := J) m₀
  have h₂ := standardHalfModulus_ne_zero (i := i) (ν := ν) (J := J) (m * c)
  field_simp

omit [LocallyOfFiniteType G.X.hom] in
/-- Powers of a point that is strictly contracting on `Δ(P_J)` eventually lie in every cone,
when `Δ(P_J)` is finite. -/
theorem eventually_pow_mem_standardCone
    (hfin : (standardParabolicComponentCharacters i ν J q).Finite)
    {y : rationalPoints A.toGrp}
    (hy : ∀ α ∈ standardParabolicComponentCharacters i ν J q,
      CocharacterUniformizer.characterNorm F A α y < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in Filter.atTop, y ^ r ∈ standardCone i ν J q ε := by
  have h : ∀ α ∈ standardParabolicComponentCharacters i ν J q,
      ∀ᶠ r : ℕ in Filter.atTop, CocharacterUniformizer.characterNorm F A α (y ^ r) < ε := by
    intro α hα
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (characterNorm_nonneg' α y) (hy α hα)
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with r hr
    rw [characterNorm_pow']
    exact hr
  exact (Filter.eventually_all_finite hfin).2 h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The image of `A(F)` in `M_J(F)` is a central subgroup. -/
theorem standardComponentHom_range_central :
    ∀ z ∈ (standardComponentHom hA).range, ∀ m : standardLeviPoints i ν J, z * m = m * z := by
  rintro _ ⟨x, rfl⟩ m
  exact standardComponentHom_commute hA x m

/-- **Uniqueness along a strictly contracting point, for right-finite functions.** If `Δ(P_J)` is
finite and `y ∈ A(F)` has `|α(y)|_F < 1` for every `α ∈ Δ(P_J)`, two functions on `M_J(F)` that are
finite under right translation by the powers of `y` and are constant terms of the same `f` are
equal. -/
theorem IsStandardConstantTerm.eq_of_isRightFinite
    (hfin : (standardParabolicComponentCharacters i ν J q).Finite)
    {y : rationalPoints A.toGrp}
    (hy : ∀ α ∈ standardParabolicComponentCharacters i ν J q,
      CocharacterUniformizer.characterNorm F A α y < 1)
    {f : rationalPoints G → ℂ} {f₁ f₂ : standardLeviPoints i ν J → ℂ}
    (h₁ : HarishChandraSchwartz.IsRightFinite (Subgroup.zpowers (standardComponentHom hA y)) f₁)
    (h₂ : HarishChandraSchwartz.IsRightFinite (Subgroup.zpowers (standardComponentHom hA y)) f₂)
    (hf₁ : IsStandardConstantTerm hA f f₁) (hf₂ : IsStandardConstantTerm hA f f₂) :
    f₁ = f₂ := by
  let gL : standardLeviPoints i ν J := standardComponentHom hA y
  let Z : Subgroup (standardLeviPoints i ν J) := Subgroup.zpowers gL
  let s : Z := ⟨gL, Subgroup.mem_zpowers gL⟩
  have hspow : ∀ r : ℕ, ((s ^ r : Z) : standardLeviPoints i ν J) = gL ^ r := fun r =>
    Subgroup.coe_pow Z s r
  have hS : Subgroup.closure ({s} : Set Z) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
    have e : z = s ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk.symm
    rw [e]
    exact zpow_mem (Subgroup.subset_closure (Set.mem_singleton s)) k
  refine h₁.eq_of_eqOn_cones h₂ hS fun m => ?_
  obtain ⟨ε₁, hε₁, e₁⟩ := hf₁ m
  obtain ⟨ε₂, hε₂, e₂⟩ := hf₂ m
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp
    (eventually_pow_mem_standardCone hfin hy (lt_min hε₁ hε₂))
  refine ⟨{z | ∃ r, r₀ ≤ r ∧ z = s ^ r}, ⟨s ^ r₀, r₀, le_rfl, rfl⟩, ?_, ?_⟩
  · rintro c ⟨r, hr, rfl⟩ x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨r + 1, hr.trans (Nat.le_succ r), (pow_succ s r).symm⟩
  · rintro c ⟨r, hr, rfl⟩
    have hx := hr₀ r hr
    have hc : ((s ^ r : Z) : standardLeviPoints i ν J) = standardComponentHom hA (y ^ r) := by
      rw [hspow r, map_pow]
    rw [hc, ← e₁ (y ^ r) fun α hα => (hx α hα).trans_le (min_le_left _ _),
      ← e₂ (y ^ r) fun α hα => (hx α hα).trans_le (min_le_right _ _)]

/-- `f` has a constant term (`IsStandardConstantTerm`) that is finite under right translation by
the image of `A(F)`; under the hypotheses of `standardConstantTerm_eq` it is unique. -/
def HasStandardConstantTerm (f : rationalPoints G → ℂ) : Prop :=
  ∃ fP : standardLeviPoints i ν J → ℂ,
    HarishChandraSchwartz.IsRightFinite (standardComponentHom hA).range fP ∧
      IsStandardConstantTerm hA f fP

open Classical in
/-- **The constant term `f_P`** of Waldspurger's Proposition I.6.2 for the actual standard
parabolic `P_J`: the chosen right-finite constant term of `f` when one exists, and `0`
otherwise. For connected reductive `G` it is the unique one (`standardConstantTerm_eq`), and for
`f ∈ A(ρ)` with `ρ` admissible it exists and lies in `A(M_J)` (`standardConstantTerm_spec`). -/
def standardConstantTerm (f : rationalPoints G → ℂ) : standardLeviPoints i ν J → ℂ :=
  if h : HasStandardConstantTerm hA f then h.choose else 0

theorem HasStandardConstantTerm.isRightFinite {f : rationalPoints G → ℂ}
    (h : HasStandardConstantTerm hA f) :
    HarishChandraSchwartz.IsRightFinite (standardComponentHom hA).range
      (standardConstantTerm hA f) := by
  rw [standardConstantTerm, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.1

theorem HasStandardConstantTerm.isStandardConstantTerm {f : rationalPoints G → ℂ}
    (h : HasStandardConstantTerm hA f) :
    IsStandardConstantTerm hA f (standardConstantTerm hA f) := by
  rw [standardConstantTerm, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.2

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem isRightFinite_comp_mul_right' {Z : Subgroup (standardLeviPoints i ν J)}
    (hZ : ∀ z ∈ Z, ∀ m : standardLeviPoints i ν J, z * m = m * z)
    {φ : standardLeviPoints i ν J → ℂ} (h : HarishChandraSchwartz.IsRightFinite Z φ)
    (m₀ : standardLeviPoints i ν J) :
    HarishChandraSchwartz.IsRightFinite Z (fun y => φ (y * m₀)) := by
  obtain ⟨W, hW, hφ, hWZ⟩ := h
  let L : (standardLeviPoints i ν J → ℂ) →ₗ[ℂ] (standardLeviPoints i ν J → ℂ) :=
    { toFun := fun ψ y => ψ (y * m₀)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨W.map L, inferInstance, ⟨φ, hφ, rfl⟩, ?_⟩
  rintro x hx _ ⟨ψ, hψ, rfl⟩
  refine ⟨fun y => ψ (y * x), hWZ x hx ψ hψ, ?_⟩
  funext y
  change ψ (y * m₀ * x) = ψ (y * x * m₀)
  rw [mul_assoc, ← hZ x hx m₀, ← mul_assoc]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem isRightFinite_comp_mul_left' {Z : Subgroup (standardLeviPoints i ν J)}
    {φ : standardLeviPoints i ν J → ℂ} (h : HarishChandraSchwartz.IsRightFinite Z φ)
    (m₀ : standardLeviPoints i ν J) :
    HarishChandraSchwartz.IsRightFinite Z (fun y => φ (m₀ * y)) := by
  obtain ⟨W, hW, hφ, hWZ⟩ := h
  let L : (standardLeviPoints i ν J → ℂ) →ₗ[ℂ] (standardLeviPoints i ν J → ℂ) :=
    { toFun := fun ψ y => ψ (m₀ * y)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨W.map L, inferInstance, ⟨φ, hφ, rfl⟩, ?_⟩
  rintro x hx _ ⟨ψ, hψ, rfl⟩
  refine ⟨fun y => ψ (y * x), hWZ x hx ψ hψ, ?_⟩
  funext y
  change ψ (m₀ * y * x) = ψ (m₀ * (y * x))
  rw [mul_assoc]

end ConstantTerm

section Pairing

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup standardConstantTermT2Field standardConstantTermLocallyCompact
  standardConstantTermNonarchimedean

variable (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
  {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
  {J : Set (characterLattice S)} {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν J ζ)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)
  (hmem : ∀ K ∈ B, StandardParabolicBasisMember i ν J q K)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

include hB hA hmem in
open Langlands.Jacquet in
/-- The asymptotic identity of Théorème I.4.1 on Renard's lattice chambers `C_A^ε`, for **every**
stable pairing of the standard data (the argument of `exists_standardCasselmanPairing`). -/
theorem standard_lattice_asymptotics (ρ : Representation ℂ (rationalPoints G) V)
    (hρ : IsAdmissible ρ)
    {b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
        Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ}
    (hb : (standardCasselmanPairingData hG hi hν hζ hB hA hmem).IsStablePairing ρ hρ.1 b)
    (v : V) (ℓ : SmoothDual ρ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ a ∈ standardComponentCAepsilon i ν J q ε,
        smoothDualPairing ρ ℓ (ρ a v) =
          b (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
            (Jacquet.mk ρ (standardUnipotentPoints i ν J) (ρ a v)) := by
  let D := standardCasselmanPairingData hG hi hν hζ hB hA hmem
  have hAd : D.Admits ρ hρ.1 := standardCasselmanPairingData_admits hG hi hν hζ hB hA hmem ρ hρ
  obtain ⟨U₁, hU₁⟩ := hρ.1 v
  obtain ⟨U₂, hU₂⟩ := isSmooth_smoothContragredient ρ ℓ
  obtain ⟨K, hKB, hKU⟩ := hB.2.mem_iff.mp (U₁ ⊓ U₂).mem_nhds_one
  have hKgood : D.Good (basisOpenSubgroup hB hKB) := good_of_mem hG hi hν hζ hB hA hmem hKB
  have hle₁ : basisOpenSubgroup hB hKB ≤ U₁ := fun x hx => (hKU hx).1
  have hle₂ : basisOpenSubgroup hB hKB ≤ U₂ := fun x hx => (hKU hx).2
  have hv := mem_fixedVectors_of_le ρ hle₁ hU₁
  have hℓ := mem_fixedVectors_of_le (smoothContragredient ρ) hle₂ hU₂
  obtain ⟨Fs, hFs, hasym⟩ :=
    hb.exists_finset_asymptotics_of_commute hAd (basisOpenSubgroup hB hKB) hKgood hv hℓ
  obtain ⟨hfac, hcon⟩ := hmem K hKB
  let Γ : Set (standardUnipotentPoints i ν J) := {x | (x : rationalPoints G) ∈ Fs}
  have hΓ : IsCompact Γ :=
    (Fs.finite_toSet.preimage Subtype.val_injective.injOn).isCompact
  obtain ⟨ε, hε, hεΓ⟩ := hcon.2.2.2.1.1 Γ hΓ
  obtain ⟨hgM, hgCA, hgplus, hgstrict⟩ := hA.strictElement_spec i ν hi hζ
  refine ⟨min ε 1, lt_min hε one_pos, fun a ha => ?_⟩
  obtain ⟨x, ⟨hxCA, hxε⟩, rfl⟩ := ha
  have haε : rationalPoints.map (q ≫ i) x ∈ standardComponentCAepsilon i ν J q ε :=
    ⟨x, ⟨hxCA, fun α hα => (hxε α hα).trans_le (min_le_left _ _)⟩, rfl⟩
  have haplus : rationalPoints.map (q ≫ i) x ∈ standardComponentCAplus i ν J q :=
    ⟨x, ⟨hxCA, fun α hα => ((hxε α hα).trans_le (min_le_right _ _)).le⟩, rfl⟩
  have haCA : rationalPoints.map (q ≫ i) x ∈ standardComponentCA i q := ⟨x, hxCA, rfl⟩
  set a := rationalPoints.map (q ≫ i) x with ha_def
  set g := hA.strictElement i ν hi hζ with hg_def
  have hfactor : ∀ k ∈ basisOpenSubgroup hB hKB,
      ∃ l ∈ (basisOpenSubgroup hB hKB).toSubgroup ⊓ standardOppositeUnipotentPoints i ν J,
      ∃ m ∈ (basisOpenSubgroup hB hKB).toSubgroup ⊓ standardLeviPoints i ν J,
      ∃ u ∈ (basisOpenSubgroup hB hKB).toSubgroup ⊓ standardUnipotentPoints i ν J,
        k = l * m * u := by
    intro k hk
    obtain ⟨⟨l, m, n⟩, heq⟩ := hfac.2 ⟨k, hk⟩
    exact ⟨l, l.property, m, m.property, n, n.property, (congrArg Subtype.val heq).symm⟩
  have hup : ∀ c ∈ standardComponentCAplus i ν J q,
      ∀ u ∈ (basisOpenSubgroup hB hKB).toSubgroup ⊓ standardUnipotentPoints i ν J,
        c * u * c⁻¹ ∈ basisOpenSubgroup hB hKB := fun c hc u hu =>
    ((hcon.2.1 c hc).1 ⟨u, hu, rfl⟩).1
  have hlow : ∀ c ∈ standardComponentCAplus i ν J q,
      ∀ l ∈ (basisOpenSubgroup hB hKB).toSubgroup ⊓ standardOppositeUnipotentPoints i ν J,
        c⁻¹ * l * c ∈ basisOpenSubgroup hB hKB := fun c hc l hl => by
    have h := (hcon.2.1 c hc).2 ⟨l, hl, rfl⟩
    simp only [inv_inv, SetLike.mem_coe] at h
    exact h.1
  have hmid : ∀ c ∈ (standardComponentCA i q : Set (rationalPoints G)),
      ∀ m ∈ (basisOpenSubgroup hB hKB).toSubgroup ⊓ standardLeviPoints i ν J,
        c⁻¹ * m * c ∈ basisOpenSubgroup hB hKB := fun c hc m hm => by
    have hm' : m ∈ ambientConjugate c ((K ⊓ standardLeviPoints i ν J :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
      rw [hcon.1 c hc]
      exact hm
    obtain ⟨y, hy, heq⟩ := hm'
    have h : c⁻¹ * m * c = y := by
      rw [← heq]
      group
    rw [h]
    exact hy.1
  have hac : a * g = g * a := by
    obtain ⟨y, -, hy⟩ := hgCA
    rw [← hy, ha_def, ← map_mul, ← map_mul, mul_comm]
  have h1 : ∀ u ∈ basisOpenSubgroup hB hKB, u ∈ D.N → a⁻¹ * u * a ∈ basisOpenSubgroup hB hKB :=
    fun u hu huN => hlow a haplus u ⟨hu, huN⟩
  have h2 : Commute (compressedAction ρ hρ.1 (basisOpenSubgroup hB hKB)
      (D.isCompact (basisOpenSubgroup hB hKB) hKgood) a)
      (compressedAction ρ hρ.1 (basisOpenSubgroup hB hKB)
        (D.isCompact (basisOpenSubgroup hB hKB) hKgood) D.g⁻¹) := by
    have hDg : D.g⁻¹ = g := inv_inv g
    rw [hDg]
    exact compressedAction_commute_of_factor ρ hρ.1 (basisOpenSubgroup hB hKB) _
      (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
      (standardOppositeUnipotentPoints i ν J) hfactor hac
      (hup a haplus) (hlow a haplus) (hmid a haCA)
      (hup g hgplus) (hlow g hgplus) (hmid g hgCA)
  have h3 : ∀ n ∈ Fs, a * n * a⁻¹ ∈ basisOpenSubgroup hB hKB := by
    intro n hn
    have hnU : n ∈ standardUnipotentPoints i ν J := hFs hn
    have hmem' := hεΓ a haε ⟨⟨n, hnU⟩, hn, rfl⟩
    obtain ⟨y, hy, heq⟩ := hmem'
    have heq' : a⁻¹ * y * a⁻¹⁻¹ = n := heq
    have h : a * n * a⁻¹ = y := by
      rw [← heq']
      group
    rw [h]
    exact hy.1
  exact hasym a h1 h2 h3

include hB hA hmem in
open Langlands.Jacquet in
/-- The asymptotic identity of Théorème I.4.1 on the whole cone of the split component, for every
stable pairing of the standard data (the argument of
`exists_standardCasselmanPairing_splitComponent`). -/
theorem standard_cone_asymptotics (ρ : Representation ℂ (rationalPoints G) V)
    (hρ : IsAdmissible ρ)
    {b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
        Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ}
    (hb : (standardCasselmanPairingData hG hi hν hζ hB hA hmem).IsStablePairing ρ hρ.1 b)
    (v : V) (ℓ : SmoothDual ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ standardCone i ν J q ε,
      smoothDualPairing ρ ℓ (ρ (rationalPoints.map (q ≫ i) x) v) =
        b (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
          (Jacquet.mk ρ (standardUnipotentPoints i ν J)
            (ρ (rationalPoints.map (q ≫ i) x) v)) := by
  have hasym := fun w => standard_lattice_asymptotics hG hi hν hζ hB hA hmem ρ hρ hb w ℓ
  have hsplit : IsSplitTorus A.toGrp := hA.1.1
  have : IsAffineHom A.toGrp.X.hom := hsplit.isAffineHom
  have : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  let : TopologicalSpace (rationalPoints A.toGrp) := rationalPointTopology F A.X
  let Ker := Plancherel.rationalCommonNormKernel A.toGrp
  have hKc : IsCompact (Ker : Set (rationalPoints A.toGrp)) :=
    Plancherel.SplitTorus.isCompact_commonNormKernel hsplit
  have : CompactSpace Ker := isCompact_iff_compactSpace.mp hKc
  have hloc : IsLocallyConstant (fun c : rationalPoints G => ρ c v) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro c
    obtain ⟨U, hU⟩ := hρ.1 v
    have ht : Filter.Tendsto (fun y : rationalPoints G => c⁻¹ * y) (nhds c) (nhds 1) :=
      (continuous_const.mul continuous_id :
        Continuous fun y : rationalPoints G => c⁻¹ * y).tendsto' c 1 (inv_mul_cancel c)
    filter_upwards [ht U.mem_nhds_one] with y hy
    have hyc : y = c * (c⁻¹ * y) := by group
    rw [hyc, map_mul, Module.End.mul_apply]
    congr 1
    exact (Representation.mem_invariants _ v).mp hU ⟨c⁻¹ * y, hy⟩
  have hcont : Continuous
      (fun k : Ker => rationalPoints.map (q ≫ i) (k : rationalPoints A.toGrp)) :=
    (continuous_rationalPointMap F (q ≫ i).hom.hom).comp continuous_subtype_val
  have hfin : (Set.range (fun k : Ker =>
      ρ (rationalPoints.map (q ≫ i) (k : rationalPoints A.toGrp)) v)).Finite :=
    (hloc.comp_continuous hcont).range_finite
  choose εf hεf hεasym using hasym
  have hWne : (Set.range (fun k : Ker =>
      ρ (rationalPoints.map (q ≫ i) (k : rationalPoints A.toGrp)) v)).Nonempty :=
    ⟨_, ⟨1, rfl⟩⟩
  obtain ⟨w₀, -, hmin⟩ := Set.exists_min_image _ εf hfin hWne
  refine ⟨εf w₀, hεf w₀, fun x hx => ?_⟩
  obtain ⟨c, hc, -⟩ := (CocharacterUniformizer.isUniformizerLatticeSection F A hsplit).2.2 x
  let xc := CocharacterUniformizer.latticeSection F A c
  let k : rationalPoints A.toGrp := x * xc⁻¹
  have hk : k ∈ Ker := hc
  have hx_eq : x = xc * k := by
    change x = xc * (x * xc⁻¹)
    rw [mul_comm x, mul_inv_cancel_left]
  have hnorm : ∀ α, CocharacterUniformizer.characterNorm F A α x =
      CocharacterUniformizer.characterNorm F A α xc := by
    intro α
    have h1 : (Plancherel.rationalNormCharacters A.toGrp
        ((rationalCharacters.equivCharacterLattice A).symm α)).toMul k = 1 :=
      (Plancherel.mem_rationalCommonNormKernel A.toGrp k).1 hk
        ((rationalCharacters.equivCharacterLattice A).symm α)
    simp only [CocharacterUniformizer.characterNorm]
    rw [hx_eq, map_mul, h1, mul_one]
  let w := ρ (rationalPoints.map (q ≫ i) k) v
  have hle := hmin w ⟨⟨k, hk⟩, rfl⟩
  have hxc : rationalPoints.map (q ≫ i) xc ∈ standardComponentCAepsilon i ν J q (εf w) :=
    ⟨xc, ⟨⟨c, rfl⟩, fun α hα => ((hnorm α) ▸ hx α hα).trans_le hle⟩, rfl⟩
  have key := hεasym w _ hxc
  have hρx : ρ (rationalPoints.map (q ≫ i) x) v = ρ (rationalPoints.map (q ≫ i) xc) w := by
    rw [hx_eq, map_mul, map_mul, Module.End.mul_apply]
  rw [hρx]
  exact key

omit [LocallyOfFiniteType G.X.hom] in
include hi hζ hB hA hmem in
/-- The Iwahori contraction basis of the radical side: compact open subgroups with Iwahori
factorization relative to `(U_J, M_J, Ū_J)` and arbitrarily small Levi parts. -/
theorem hasIwahoriContractionBasis_standard :
    Jacquet.HasIwahoriContractionBasis (standardUnipotentPoints i ν J)
      (standardLeviPoints i ν J) (standardOppositeUnipotentPoints i ν J) := by
  intro L
  obtain ⟨W, hW, hWL⟩ := isOpen_induced_iff.mp L.isOpen
  have h1 : (1 : rationalPoints G) ∈ W := by
    have : (1 : standardLeviPoints i ν J) ∈ (Subtype.val : standardLeviPoints i ν J →
        rationalPoints G) ⁻¹' W := by
      rw [hWL]
      exact L.one_mem
    exact this
  obtain ⟨K, hK, hKW⟩ := hB.2.mem_iff.mp (hW.mem_nhds h1)
  refine ⟨basisOpenSubgroup hB hK, (hB.1 K hK).2.2.2, ?_, _,
    (basis_isIwahoriContraction hi hζ hB hA hmem hK).2⟩
  intro m hm
  change m ∈ (L : Set (standardLeviPoints i ν J))
  rw [← hWL]
  exact hKW hm

include hi hζ hA in
/-- `Δ(P_J)` is finite and contains no character of norm `≥ 1` at some point of `A(F)`. -/
theorem exists_strictly_contracting_point :
    (standardParabolicComponentCharacters i ν J q).Finite ∧
      ∃ y : rationalPoints A.toGrp, ∀ α ∈ standardParabolicComponentCharacters i ν J q,
        CocharacterUniformizer.characterNorm F A α y < 1 := by
  refine ⟨((hi.1.1.finite_simpleRelativeRoots i ν).subset Set.sdiff_subset).image _, ?_⟩
  obtain ⟨y, ⟨-, hy⟩, -⟩ := (hA.strictElement_spec i ν hi hζ).2.2.2
  exact ⟨y, hy⟩

include hi hζ in
/-- **Uniqueness of right-finite constant terms.** Two functions on `M_J(F)` that are finite
under right translation by the image of `A(F)` and are constant terms of the same `f` are
equal. -/
theorem IsStandardConstantTerm.eq_of_isRightFinite_range {f : rationalPoints G → ℂ}
    {f₁ f₂ : standardLeviPoints i ν J → ℂ}
    (h₁ : HarishChandraSchwartz.IsRightFinite (standardComponentHom hA).range f₁)
    (h₂ : HarishChandraSchwartz.IsRightFinite (standardComponentHom hA).range f₂)
    (hf₁ : IsStandardConstantTerm hA f f₁) (hf₂ : IsStandardConstantTerm hA f f₂) :
    f₁ = f₂ := by
  obtain ⟨hfin, y, hy⟩ := exists_strictly_contracting_point hi hζ hA
  have hle : Subgroup.zpowers (standardComponentHom hA y) ≤ (standardComponentHom hA).range :=
    Subgroup.zpowers_le.mpr ⟨y, rfl⟩
  have mono : ∀ {φ : standardLeviPoints i ν J → ℂ},
      HarishChandraSchwartz.IsRightFinite (standardComponentHom hA).range φ →
        HarishChandraSchwartz.IsRightFinite (Subgroup.zpowers (standardComponentHom hA y)) φ :=
    fun ⟨W, hW, hφ, hWZ⟩ => ⟨W, hW, hφ, fun x hx => hWZ x (hle hx)⟩
  exact hf₁.eq_of_isRightFinite hA hfin hy (mono h₁) (mono h₂) hf₂

include hi hζ in
/-- Every right-finite constant term of `f` is `standardConstantTerm hA f`. -/
theorem standardConstantTerm_eq {f : rationalPoints G → ℂ} {fP : standardLeviPoints i ν J → ℂ}
    (hR : HarishChandraSchwartz.IsRightFinite (standardComponentHom hA).range fP)
    (h : IsStandardConstantTerm hA f fP) : standardConstantTerm hA f = fP :=
  (HasStandardConstantTerm.isStandardConstantTerm hA ⟨fP, hR, h⟩).eq_of_isRightFinite_range
    hi hζ hA (HasStandardConstantTerm.isRightFinite hA ⟨fP, hR, h⟩) hR h

include hi hζ in
/-- **Uniqueness in Proposition I.6.2.** Two elements of `A(M_J)` (each a coefficient of an
admissible smooth representation of `M_J(F)`) that are constant terms of the same `f` are
equal. -/
theorem eq_of_isStandardConstantTerm {f : rationalPoints G → ℂ}
    {f₁ f₂ : standardLeviPoints i ν J → ℂ}
    (h₁ : ∃ B : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J), IsAdmissible B.representation ∧
      f₁ ∈ HarishChandraSchwartz.coefficientFunctionSpace B)
    (h₂ : ∃ B : SmoothRep.{0, u, uW} ℂ (standardLeviPoints i ν J), IsAdmissible B.representation ∧
      f₂ ∈ HarishChandraSchwartz.coefficientFunctionSpace B)
    (hf₁ : IsStandardConstantTerm hA f f₁) (hf₂ : IsStandardConstantTerm hA f f₂) :
    f₁ = f₂ := by
  obtain ⟨B₁, hB₁, hf₁B⟩ := h₁
  obtain ⟨B₂, hB₂, hf₂B⟩ := h₂
  exact hf₁.eq_of_isRightFinite_range hi hζ hA
    (HarishChandraSchwartz.isRightFinite_of_mem_coefficientFunctionSpace hB₁ _
      (standardComponentHom_range_central hA) hf₁B)
    (HarishChandraSchwartz.isRightFinite_of_mem_coefficientFunctionSpace hB₂ _
      (standardComponentHom_range_central hA) hf₂B) hf₂

open Langlands.Jacquet in
/-- **Existence in Proposition I.6.2 for one coefficient.** For a stable pairing `b` of the
standard data, the Library's constant term `m ↦ b(ǰ(ℓ), π_P(m) j(v))` (normalized by `δ_{U_J}`)
of the coefficient `x ↦ ℓ(ρ(x) v)` has the constant-term property on the source's cones. -/
theorem isStandardConstantTerm_coefficientConstantTerm
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ)
    {b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
        Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ}
    (hb : (standardCasselmanPairingData hG hi hν hζ hB hA hmem).IsStablePairing ρ hρ.1 b)
    (ℓ : SmoothDual ρ) (v : V) :
    IsStandardConstantTerm hA (fun x => smoothDualPairing ρ ℓ (ρ x v))
      ((standardCasselmanPairingData hG hi hν hζ hB hA hmem).coefficientConstantTerm ρ b
        (standardRadicalModulus i ν J) ℓ v) := by
  intro m
  obtain ⟨ε, hε, h⟩ := standard_cone_asymptotics hG hi hν hζ hB hA hmem ρ hρ hb (ρ m v) ℓ
  refine ⟨ε, hε, fun x hx => ?_⟩
  have hpt : ρ ((m * standardComponentHom hA x : standardLeviPoints i ν J) : rationalPoints G) v =
      ρ (rationalPoints.map (q ≫ i) x) (ρ m v) := by
    rw [← standardComponentHom_commute hA x m]
    change ρ (rationalPoints.map (q ≫ i) x * (m : rationalPoints G)) v = _
    rw [map_mul, Module.End.mul_apply]
  have key := h x hx
  rw [← hpt] at key
  exact StablePairingData.inv_sqrt_mul_eq_coefficientConstantTerm
    (standardCasselmanPairingData hG hi hν hζ hB hA hmem) ρ b (standardRadicalModulus i ν J) ℓ v
    (m * standardComponentHom hA x) key

include hG hi hν hζ hB hmem in
open Langlands.Jacquet in
/-- **Existence in Proposition I.6.2, with the radical invariances.** For an admissible `ρ` there
is one admissible smooth representation `B` of `M_J(F)` (the normalized Jacquet module of `ρ`
along `U_J(F)`) such that every `f ∈ A(ρ)` has a constant term `f_P ∈ A(B)` on the source's cones,
which is also a constant term of `x ↦ f(x n)` for `n ∈ U_J(F)` and of `x ↦ f(n x)` for
`n ∈ Ū_J(F)`. -/
theorem exists_standardConstantTerm (ρ : Representation ℂ (rationalPoints G) V)
    (hρ : IsAdmissible ρ) :
    ∃ B : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J), IsAdmissible B.representation ∧
      ∀ f ∈ HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1),
        ∃ fP ∈ HarishChandraSchwartz.coefficientFunctionSpace B,
          IsStandardConstantTerm hA f fP ∧
          (∀ n ∈ standardUnipotentPoints i ν J,
            IsStandardConstantTerm hA (fun x => f (x * n)) fP) ∧
          (∀ n ∈ standardOppositeUnipotentPoints i ν J,
            IsStandardConstantTerm hA (fun x => f (n * x)) fP) := by
  let D := standardCasselmanPairingData hG hi hν hζ hB hA hmem
  have hAd : D.Admits ρ hρ.1 := standardCasselmanPairingData_admits hG hi hν hζ hB hA hmem ρ hρ
  obtain ⟨b, hb⟩ := D.exists_isStablePairing hAd
  have hδ := isOpen_ker_standardRadicalModulus (i := i) (ν := ν) (J := J)
  have hbasis : HasIwahoriContractionBasis D.Nbar D.M D.N :=
    hasIwahoriContractionBasis_standard hi hζ hB hA hmem
  let B : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J) :=
    SmoothRep.of (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar (standardRadicalModulus i ν J))
      (isSmooth_normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar _ hδ hρ.1)
  refine ⟨B, isAdmissible_normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar _ hδ hρ.1
    (isAdmissible_action_of_iwahoriContraction ρ hρ D.Nbar D.M D.N D.hMNbar hbasis), ?_⟩
  let W : Submodule ℂ (rationalPoints G → ℂ) :=
    { carrier := {f | ∃ fP ∈ HarishChandraSchwartz.coefficientFunctionSpace B,
        IsStandardConstantTerm hA f fP ∧
        (∀ n ∈ standardUnipotentPoints i ν J,
          IsStandardConstantTerm hA (fun x => f (x * n)) fP) ∧
        (∀ n ∈ standardOppositeUnipotentPoints i ν J,
          IsStandardConstantTerm hA (fun x => f (n * x)) fP)}
      add_mem' := by
        rintro f₁ f₂ ⟨g₁, hg₁, h₁, hU₁, hO₁⟩ ⟨g₂, hg₂, h₂, hU₂, hO₂⟩
        exact ⟨g₁ + g₂, Submodule.add_mem _ hg₁ hg₂, h₁.add hA h₂,
          fun n hn => (hU₁ n hn).add hA (hU₂ n hn),
          fun n hn => (hO₁ n hn).add hA (hO₂ n hn)⟩
      zero_mem' := ⟨0, Submodule.zero_mem _, isStandardConstantTerm_zero hA,
        fun _ _ => isStandardConstantTerm_zero hA, fun _ _ => isStandardConstantTerm_zero hA⟩
      smul_mem' := by
        rintro c f ⟨g, hg, h, hU, hO⟩
        exact ⟨c • g, Submodule.smul_mem _ c hg, h.smul hA c,
          fun n hn => (hU n hn).smul hA c, fun n hn => (hO n hn).smul hA c⟩ }
  have hle : HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1) ≤ W := by
    refine iSup_le fun ℓ => ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨D.coefficientConstantTerm ρ b (standardRadicalModulus i ν J) ℓ x,
      hb.coefficientConstantTerm_mem_coefficientFunctionSpace hAd _ hδ ℓ x,
      isStandardConstantTerm_coefficientConstantTerm hG hi hν hζ hB hA hmem ρ hρ hb ℓ x, ?_, ?_⟩
    · intro n hn
      have e : D.coefficientConstantTerm ρ b (standardRadicalModulus i ν J) ℓ (ρ n x) =
          D.coefficientConstantTerm ρ b (standardRadicalModulus i ν J) ℓ x := by
        funext m
        simp only [StablePairingData.coefficientConstantTerm]
        congr 2
        exact mk_apply_subgroup ρ D.Nbar ⟨n, hn⟩ x
      have h := isStandardConstantTerm_coefficientConstantTerm hG hi hν hζ hB hA hmem ρ hρ hb ℓ
        (ρ n x)
      rw [e] at h
      have hfun : (fun y => smoothDualPairing ρ ℓ (ρ y (ρ n x))) =
          fun y => matrixCoefficient (SmoothRep.of ρ hρ.1).representation ℓ.val x (y * n) := by
        funext y
        change smoothDualPairing ρ ℓ (ρ y (ρ n x)) = smoothDualPairing ρ ℓ (ρ (y * n) x)
        rw [map_mul, Module.End.mul_apply]
      exact hfun ▸ h
    · intro n hn
      have hn' : n⁻¹ ∈ D.N := inv_mem hn
      have e : D.coefficientConstantTerm ρ b (standardRadicalModulus i ν J)
          (smoothContragredient ρ n⁻¹ ℓ) x =
          D.coefficientConstantTerm ρ b (standardRadicalModulus i ν J) ℓ x := by
        funext m
        simp only [StablePairingData.coefficientConstantTerm]
        congr 2
        exact mk_apply_subgroup (smoothContragredient ρ) D.N ⟨n⁻¹, hn'⟩ ℓ
      have h := isStandardConstantTerm_coefficientConstantTerm hG hi hν hζ hB hA hmem ρ hρ hb
        (smoothContragredient ρ n⁻¹ ℓ) x
      rw [e] at h
      have hfun : (fun y => smoothDualPairing ρ (smoothContragredient ρ n⁻¹ ℓ) (ρ y x)) =
          fun y => matrixCoefficient (SmoothRep.of ρ hρ.1).representation ℓ.val x (n * y) := by
        funext y
        change smoothDualPairing ρ (smoothContragredient ρ n⁻¹ ℓ) (ρ y x) =
          smoothDualPairing ρ ℓ (ρ (n * y) x)
        rw [smoothDualPairing_action, inv_inv, map_mul, Module.End.mul_apply]
      exact hfun ▸ h
  exact fun f hf => hle hf

include hi hζ in
/-- Linearity of the constant term on functions having one: `(f₁ + f₂)_P = (f₁)_P + (f₂)_P`. -/
theorem standardConstantTerm_add {f₁ f₂ : rationalPoints G → ℂ}
    (h₁ : HasStandardConstantTerm hA f₁) (h₂ : HasStandardConstantTerm hA f₂) :
    standardConstantTerm hA (f₁ + f₂) = standardConstantTerm hA f₁ + standardConstantTerm hA f₂ :=
  standardConstantTerm_eq hi hζ hA ((h₁.isRightFinite hA).add (h₂.isRightFinite hA))
    ((h₁.isStandardConstantTerm hA).add hA (h₂.isStandardConstantTerm hA))

include hi hζ in
/-- Linearity of the constant term on functions having one: `(c f)_P = c f_P`. -/
theorem standardConstantTerm_smul {f : rationalPoints G → ℂ}
    (h : HasStandardConstantTerm hA f) (c : ℂ) :
    standardConstantTerm hA (c • f) = c • standardConstantTerm hA f :=
  standardConstantTerm_eq hi hζ hA ((h.isRightFinite hA).smul c)
    ((h.isStandardConstantTerm hA).smul hA c)

include hG hi hν hζ hB hmem in
/-- **Waldspurger, Proposition I.6.2, for actual standard parabolic subgroups.** For an
admissible smooth representation `ρ` of `G(F)` and `f ∈ A(ρ)`, there is a unique function `f_P` on
`M_J(F)` lying in `A(M_J)` (a coefficient of an admissible smooth representation of `M_J(F)` on a
space in the universe of `ρ`'s space) such that for every `m ∈ M_J(F)` there is `ε > 0` with
`δ(m a)^{-1/2} f(m a) = f_P(m a)` for every `a ∈ A(F)` with `|α(a)|_F < ε` for all
`α ∈ Δ(P_J)`. -/
theorem existsUnique_standardConstantTerm (ρ : Representation ℂ (rationalPoints G) V)
    (hρ : IsAdmissible ρ) {f : rationalPoints G → ℂ}
    (hf : f ∈ HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1)) :
    ∃! fP : standardLeviPoints i ν J → ℂ,
      (∃ B : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J), IsAdmissible B.representation ∧
        fP ∈ HarishChandraSchwartz.coefficientFunctionSpace B) ∧
      IsStandardConstantTerm hA f fP := by
  obtain ⟨B, hB', hex⟩ := exists_standardConstantTerm hG hi hν hζ hB hA hmem ρ hρ
  obtain ⟨fP, hfPB, hfP, -, -⟩ := hex f hf
  exact ⟨fP, ⟨⟨B, hB', hfPB⟩, hfP⟩, fun f' ⟨h', hf'⟩ =>
    eq_of_isStandardConstantTerm hi hζ hA h' ⟨B, hB', hfPB⟩ hf' hfP⟩

include hG hi hν hζ hB hmem in
/-- **The constant term of `f ∈ A(ρ)`.** For admissible `ρ` and `f ∈ A(ρ)`, `f` has a right-finite
constant term; `standardConstantTerm hA f` is this constant term and lies in `A(M_J)`. -/
theorem standardConstantTerm_spec (ρ : Representation ℂ (rationalPoints G) V)
    (hρ : IsAdmissible ρ) {f : rationalPoints G → ℂ}
    (hf : f ∈ HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1)) :
    HasStandardConstantTerm hA f ∧ IsStandardConstantTerm hA f (standardConstantTerm hA f) ∧
      ∃ B : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J), IsAdmissible B.representation ∧
        standardConstantTerm hA f ∈ HarishChandraSchwartz.coefficientFunctionSpace B := by
  obtain ⟨B, hB', hex⟩ := exists_standardConstantTerm hG hi hν hζ hB hA hmem ρ hρ
  obtain ⟨fP, hfPB, hfP, -, -⟩ := hex f hf
  have hR := HarishChandraSchwartz.isRightFinite_of_mem_coefficientFunctionSpace hB' _
    (standardComponentHom_range_central hA) hfPB
  have e := standardConstantTerm_eq hi hζ hA hR hfP
  exact ⟨⟨fP, hR, hfP⟩, e ▸ hfP, B, hB', e ▸ hfPB⟩

include hG hi hν hζ hB hmem in
/-- **Invariance under the radical: `(ρ(n) f)_P = f_P`** for `n ∈ U_J(F)` and `f ∈ A(ρ)`. -/
theorem standardConstantTerm_mul_radical (ρ : Representation ℂ (rationalPoints G) V)
    (hρ : IsAdmissible ρ) {f : rationalPoints G → ℂ}
    (hf : f ∈ HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1))
    {n : rationalPoints G} (hn : n ∈ standardUnipotentPoints i ν J) :
    standardConstantTerm hA (fun x => f (x * n)) = standardConstantTerm hA f := by
  obtain ⟨B, hB', hex⟩ := exists_standardConstantTerm hG hi hν hζ hB hA hmem ρ hρ
  obtain ⟨fP, hfPB, hfP, hU, -⟩ := hex f hf
  have hR := HarishChandraSchwartz.isRightFinite_of_mem_coefficientFunctionSpace hB' _
    (standardComponentHom_range_central hA) hfPB
  rw [standardConstantTerm_eq hi hζ hA hR (hU n hn), standardConstantTerm_eq hi hζ hA hR hfP]

include hG hi hν hζ hB hmem in
/-- **Invariance under the opposite radical** for `n ∈ Ū_J(F)` and `f ∈ A(ρ)`: the constant term
of `x ↦ f(n x)` is `f_P`. -/
theorem standardConstantTerm_oppositeRadical_mul (ρ : Representation ℂ (rationalPoints G) V)
    (hρ : IsAdmissible ρ) {f : rationalPoints G → ℂ}
    (hf : f ∈ HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1))
    {n : rationalPoints G} (hn : n ∈ standardOppositeUnipotentPoints i ν J) :
    standardConstantTerm hA (fun x => f (n * x)) = standardConstantTerm hA f := by
  obtain ⟨B, hB', hex⟩ := exists_standardConstantTerm hG hi hν hζ hB hA hmem ρ hρ
  obtain ⟨fP, hfPB, hfP, -, hO⟩ := hex f hf
  have hR := HarishChandraSchwartz.isRightFinite_of_mem_coefficientFunctionSpace hB' _
    (standardComponentHom_range_central hA) hfPB
  rw [standardConstantTerm_eq hi hζ hA hR (hO n hn), standardConstantTerm_eq hi hζ hA hR hfP]

include hi hζ in
/-- **`(ρ(m₀) f)_P = δ(m₀)^{1/2} ρ(m₀) f_P`** for `m₀ ∈ M_J(F)`. -/
theorem standardConstantTerm_mul_right {f : rationalPoints G → ℂ}
    (h : HasStandardConstantTerm hA f) (m₀ : standardLeviPoints i ν J) :
    standardConstantTerm hA (fun x => f (x * (m₀ : rationalPoints G))) =
      fun y => standardHalfModulus i ν J m₀ * standardConstantTerm hA f (y * m₀) :=
  standardConstantTerm_eq hi hζ hA
    ((isRightFinite_comp_mul_right' (standardComponentHom_range_central hA)
      (h.isRightFinite hA) m₀).smul (standardHalfModulus i ν J m₀))
    ((h.isStandardConstantTerm hA).mul_right hA m₀)

include hi hζ in
/-- The constant term of `x ↦ f(m₀ x)` is `y ↦ δ(m₀)^{1/2} f_P(m₀ y)` for `m₀ ∈ M_J(F)`. -/
theorem standardConstantTerm_mul_left {f : rationalPoints G → ℂ}
    (h : HasStandardConstantTerm hA f) (m₀ : standardLeviPoints i ν J) :
    standardConstantTerm hA (fun x => f ((m₀ : rationalPoints G) * x)) =
      fun y => standardHalfModulus i ν J m₀ * standardConstantTerm hA f (m₀ * y) :=
  standardConstantTerm_eq hi hζ hA
    ((isRightFinite_comp_mul_left' (h.isRightFinite hA) m₀).smul (standardHalfModulus i ν J m₀))
    ((h.isStandardConstantTerm hA).mul_left hA m₀)

end Pairing

end Langlands.BruhatTits.SpecialCompact

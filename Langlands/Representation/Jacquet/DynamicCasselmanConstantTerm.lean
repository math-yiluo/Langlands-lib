import Langlands.Representation.Aubert.General.RationalOppositeIwahoriBasisProof
import Langlands.Representation.Aubert.General.UnipotentIntersectionHaarDeterminant
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction
import Langlands.Representation.Jacquet.OppositeIwahoriBasisAbstract
import Langlands.Representation.Jacquet.IwahoriStablePairingData
import Langlands.Representation.Jacquet.IwahoriStablePairingAdmits
import Langlands.Representation.Jacquet.StablePairingAsymptotics
import Langlands.Representation.Jacquet.StablePairingUniformAsymptotics
import Langlands.Representation.Jacquet.StablePairingVanishing
import Langlands.Representation.Aubert.General.UnitaryOppositeJacquet
import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Langlands.GroupScheme.Dynamic.RationalOpenCell
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RightFiniteUniqueness
import Langlands.Group.HaarModulus
import Langlands.Representation.Smooth.Contragredient.LawsProof

/-! # Casselman's pairing and the constant term for actual dynamic parabolic subgroups

For a smooth affine group scheme `G` over a nonarchimedean local field `F`, a cocharacter
`χ : 𝔾_m → G` and a unit `t ∈ F^×` whose powers tend to `0`, this module builds the Library's
stable-pairing data for the actual dynamic parabolic `P(χ)(F) = Z(χ)(F) U(χ)(F)` with opposite
radical `U(χ⁻¹)(F)` and contracting element `χ(t)`, without structural hypotheses. It proves
Waldspurger's Théorème I.4.1 (Casselman) along the powers `χ(t)^r` and Waldspurger's
Proposition I.6.2 (existence and uniqueness of the constant term `f_P ∈ A(M)`) with the cones
of the source replaced by the tails `{χ(t)^r ; r ≥ r₀}`.
-/

noncomputable section

universe u uV uW

open CategoryTheory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.DynamicUnipotentContainment

namespace Langlands.Jacquet

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]

local instance dynamicCasselmanIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance dynamicCasselmanTopology : TopologicalSpace (RationalPoint F G.X) :=
  rationalPointTopology F G.X
local instance dynamicCasselmanT2Field : T2Space F := BruhatTits.localField_t2Space F
local instance dynamicCasselmanTopologicalGroup : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance dynamicCasselmanLocallyCompact : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance dynamicCasselmanNonarchimedean : NonarchimedeanGroup (RationalPoint F G.X) :=
  Aubert.General.RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- The actual dynamic Levi subgroup `M = Z(χ)(F)` of `G(F)`. -/
abbrev dynamicLeviPoints : Subgroup (RationalPoint F G.X) :=
  (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
/-- `Z(χ)(F)` normalizes the radical `U(χ)(F)`. -/
theorem dynamicLeviPoints_le_normalizer_radical :
    dynamicLeviPoints χ ≤ Subgroup.normalizer (unipotentPoints χ : Set (RationalPoint F G.X)) :=
  Dynamic.centralizer_le_normalizer_unipotent _ _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
/-- `Z(χ)(F)` normalizes the opposite radical `U(χ⁻¹)(F)`. -/
theorem dynamicLeviPoints_le_normalizer_oppositeRadical :
    dynamicLeviPoints χ ≤ Subgroup.normalizer
      (unipotentPoints (Dynamic.inverseCocharacter χ) : Set (RationalPoint F G.X)) := by
  rw [dynamicLeviPoints, ← Dynamic.centralizer_inverseCocharacter χ]
  exact Dynamic.centralizer_le_normalizer_unipotent _ _

variable (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))

include ht in
/-- The value `χ(t)` at a unit whose powers tend to `0` gives an opposite Iwahori contraction
basis of `G(F)` for `U(χ)(F)`, `Z(χ)(F)` and `U(χ⁻¹)(F)`. -/
theorem hasOppositeIwahoriContractionBasis_cocharPoint :
    HasOppositeIwahoriContractionBasis (unipotentPoints χ) (dynamicLeviPoints χ)
      (unipotentPoints (Dynamic.inverseCocharacter χ)) (cocharPoint χ t) := by
  refine hasOppositeIwahoriContractionBasis_of_contraction
    (isClosed_unipotentPoints (Dynamic.inverseCocharacter χ)) (isClosed_unipotentPoints χ)
    (cocharPoint_mem_centralizer χ t) (fun m hm => (commute_cocharPoint χ hm t).eq)
    (dynamicLeviPoints_le_normalizer_oppositeRadical χ)
    (dynamicLeviPoints_le_normalizer_radical χ)
    (Aubert.General.RationalPointFamily.dynamic_opposite_factorization_unique χ) ?_
    (eventually_cocharPoint_pow_conj_mem_ambient χ t ht) ?_
  · have h := Dynamic.opposite_cell_mem_nhds_one F G χ
    rw [← rationalPointTopology_eq_rationalSchemeTopology F G.X] at h
    exact h
  · intro C hC hCO W hW
    have h := eventually_cocharPoint_pow_conj_mem_ambient (Dynamic.inverseCocharacter χ)
      t ht C hC hCO W hW
    simpa only [cocharPoint_inverseCocharacter, inv_pow, inv_inv] using h

/-- **The Casselman pairing data of an actual dynamic parabolic subgroup.** The Library's
stable-pairing data of `G(F)` with upper subgroup `N = U(χ⁻¹)(F)`, opposite subgroup
`Nbar = U(χ)(F)` (whose coinvariants are the Jacquet module of `P(χ)`), Levi `M = Z(χ)(F)` and
contracting element `χ(t)⁻¹`, so that the powers of `χ(t)` contract `U(χ)(F)`. -/
def dynamicCasselmanPairingData : StablePairingData (RationalPoint F G.X) :=
  stablePairingDataOfIwahoriContractions (unipotentPoints (Dynamic.inverseCocharacter χ))
    (dynamicLeviPoints χ) (unipotentPoints χ)
    (dynamicLeviPoints_le_normalizer_oppositeRadical χ)
    (dynamicLeviPoints_le_normalizer_radical χ) (cocharPoint χ t)⁻¹
    (fun _ hm => ((commute_cocharPoint χ hm t).inv_right).eq)
    (HasOppositeIwahoriContractionBasis.symm (hasOppositeIwahoriContractionBasis_cocharPoint χ t ht))

@[simp] theorem dynamicCasselmanPairingData_M :
    (dynamicCasselmanPairingData χ t ht).M = dynamicLeviPoints χ := rfl

@[simp] theorem dynamicCasselmanPairingData_N :
    (dynamicCasselmanPairingData χ t ht).N = unipotentPoints (Dynamic.inverseCocharacter χ) := rfl

@[simp] theorem dynamicCasselmanPairingData_Nbar :
    (dynamicCasselmanPairingData χ t ht).Nbar = unipotentPoints χ := rfl

theorem dynamicCasselmanPairingData_g_inv :
    (dynamicCasselmanPairingData χ t ht).g⁻¹ = cocharPoint χ t := inv_inv _

/-- The point `χ(t)` of the dynamic Levi `Z(χ)(F)`. -/
def dynamicCocharPoint : dynamicLeviPoints χ :=
  ⟨cocharPoint χ t, cocharPoint_mem_centralizer χ t⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
@[simp] theorem coe_dynamicCocharPoint_pow (r : ℕ) :
    ((dynamicCocharPoint χ t ^ r : dynamicLeviPoints χ) : RationalPoint F G.X) =
      cocharPoint χ t ^ r := by
  rw [Subgroup.coe_pow]
  rfl

section Contracting

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- The powers of a contracting element lying in `M` are contracting. -/
theorem StablePairingData.isContractingElement_pow (D : StablePairingData Γ) {a : Γ}
    (ha : D.IsContractingElement a) (haM : a ∈ D.M) (r : ℕ) :
    D.IsContractingElement (a ^ r) := by
  obtain ⟨hM, hg, hlow, hup⟩ := ha
  refine ⟨fun m hm => ((Commute.pow_right (hM m hm) r)).eq, (Commute.pow_left hg r).eq, ?_, ?_⟩
  · intro K hK l hl hlN
    induction r with
    | zero => simpa using hl
    | succ r ih =>
      have hNbar : a ^ r * l * (a ^ r)⁻¹ ∈ D.Nbar :=
        (Subgroup.mem_normalizer_iff.mp (D.hMNbar (pow_mem haM r)) l).mp hlN
      have h := hlow K hK _ ih hNbar
      have e : a ^ (r + 1) * l * (a ^ (r + 1))⁻¹ = a * (a ^ r * l * (a ^ r)⁻¹) * a⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact h
  · intro K hK u hu huN
    induction r with
    | zero => simpa using hu
    | succ r ih =>
      have hN : (a ^ r)⁻¹ * u * (a ^ r) ∈ D.N := by
        have h := (Subgroup.mem_normalizer_iff.mp (D.hMN (inv_mem (pow_mem haM r))) u).mp huN
        simpa only [inv_inv] using h
      have h := hup K hK _ ih hN
      have e : (a ^ (r + 1))⁻¹ * u * a ^ (r + 1) = a⁻¹ * ((a ^ r)⁻¹ * u * a ^ r) * a := by
        rw [pow_succ]
        group
      rw [e]
      exact h

end Contracting

section Pairing

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Admissible representations satisfy the stable-pairing hypothesis `Admits` for the actual
dynamic pairing data. -/
theorem dynamicCasselmanPairingData_admits (ρ : Representation ℂ (RationalPoint F G.X) V)
    (hρ : IsAdmissible ρ) : (dynamicCasselmanPairingData χ t ht).Admits ρ hρ.1 :=
  StablePairingData.admits_of_iwahoriContractions _ ρ hρ
    (fun _ hK => hK.2.1) (fun _ hK => hK.2.2)

include ht in
/-- **Waldspurger, Théorème I.4.1, for actual dynamic parabolic subgroups, along the powers of
`χ(t)`.** For an admissible smooth representation `ρ` of `G(F)` there is a bilinear form `b` on
`V̌_{U(χ⁻¹)} × V_{U(χ)}`, nondegenerate on both sides and invariant under `Z(χ)(F)`, such that
for every `v ∈ V` and smooth functional `ℓ` the identity `ℓ(ρ(χ(t)^r) v) = b(ǰ(ℓ), j(ρ(χ(t)^r) v))`
holds for all sufficiently large `r`. No structural hypothesis is used. -/
theorem exists_dynamicCasselmanPairing (ρ : Representation ℂ (RationalPoint F G.X) V)
    (hρ : IsAdmissible ρ) :
    ∃ b : Coinvariants (smoothContragredient ρ) (unipotentPoints (Dynamic.inverseCocharacter χ))
        →ₗ[ℂ] Coinvariants ρ (unipotentPoints χ) →ₗ[ℂ] ℂ,
      Function.Injective b ∧ Function.Injective b.flip ∧
      (∀ (m : dynamicLeviPoints χ)
          (x : Coinvariants (smoothContragredient ρ)
            (unipotentPoints (Dynamic.inverseCocharacter χ)))
          (y : Coinvariants ρ (unipotentPoints χ)),
        b (action (smoothContragredient ρ) (unipotentPoints (Dynamic.inverseCocharacter χ))
            (dynamicLeviPoints χ) (dynamicLeviPoints_le_normalizer_oppositeRadical χ) m x)
          (action ρ (unipotentPoints χ) (dynamicLeviPoints χ)
            (dynamicLeviPoints_le_normalizer_radical χ) m y) = b x y) ∧
      ∀ (v : V) (ℓ : SmoothDual ρ), ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
        smoothDualPairing ρ ℓ (ρ (cocharPoint χ t ^ r) v) =
          b (Jacquet.mk (smoothContragredient ρ) (unipotentPoints (Dynamic.inverseCocharacter χ)) ℓ)
            (Jacquet.mk ρ (unipotentPoints χ) (ρ (cocharPoint χ t ^ r) v)) := by
  let D := dynamicCasselmanPairingData χ t ht
  have hA : D.Admits ρ hρ.1 := dynamicCasselmanPairingData_admits χ t ht ρ hρ
  obtain ⟨b, hb⟩ := D.exists_isStablePairing hA
  refine ⟨b, hb.injective hA, hb.flip_injective hA, hb.map_action hA, fun v ℓ => ?_⟩
  obtain ⟨r₀, h⟩ := hb.exists_pow_asymptotics hA v ℓ
  refine ⟨r₀, fun r hr => ?_⟩
  have hg : D.g⁻¹ = cocharPoint χ t := dynamicCasselmanPairingData_g_inv χ t ht
  have h' := h r hr
  rw [hg] at h'
  exact h'

end Pairing

section ConstantTerm

/-- **The radical modulus `δ_U` on the Levi of an actual dynamic parabolic**: the Haar modulus of
conjugation by `m ∈ Z(χ)(F)` on the closed radical `U(χ)(F)`, so that `μ(m E m⁻¹) = δ_U(m) μ(E)`
for a Haar measure `μ` of `U(χ)(F)`. -/
def dynamicParabolicModulus : dynamicLeviPoints χ →* ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter (unipotentPoints χ) (isClosed_unipotentPoints χ)
    (dynamicLeviPoints χ) (dynamicLeviPoints_le_normalizer_radical χ)

omit [Smooth G.X.hom] in
/-- `δ_U` has open kernel (it is trivial on every compact open subgroup of `Z(χ)(F)`). -/
theorem isOpen_ker_dynamicParabolicModulus :
    IsOpen ((dynamicParabolicModulus χ).ker : Set (dynamicLeviPoints χ)) :=
  HaarModulus.isOpen_ker_closedRestrictCharacter _ _ _ _

/-- The positive square root `δ_U(m)^{1/2}`, as a complex number. -/
def dynamicHalfModulus (m : dynamicLeviPoints χ) : ℂ :=
  ((NNReal.sqrt (dynamicParabolicModulus χ m : ℝ≥0) : ℝ) : ℂ)

omit [Smooth G.X.hom] in
theorem dynamicHalfModulus_mul (m m' : dynamicLeviPoints χ) :
    dynamicHalfModulus χ (m * m') = dynamicHalfModulus χ m * dynamicHalfModulus χ m' := by
  simp only [dynamicHalfModulus, map_mul, Units.val_mul, NNReal.sqrt_mul, NNReal.coe_mul,
    Complex.ofReal_mul]

omit [Smooth G.X.hom] in
theorem dynamicHalfModulus_ne_zero (m : dynamicLeviPoints χ) : dynamicHalfModulus χ m ≠ 0 := by
  simp [dynamicHalfModulus, (dynamicParabolicModulus χ m).ne_zero]

/-- **The constant-term property along the powers of `χ(t)`.** The function `f_P` on
`M = Z(χ)(F)` is a constant term of `f` on `G(F)` if for every `m ∈ M` the identity
`δ_U(m χ(t)^r)^{-1/2} f(m χ(t)^r) = f_P(m χ(t)^r)` holds for all sufficiently large `r`.
This is the identity of Waldspurger's Proposition I.6.2 with the cone
`{a ∈ A_M ; |α(a)|_F < ε, α ∈ Σ(P)}` replaced by the tail `{χ(t)^r ; r ≥ r₀}` and his modulus
`δ_P` replaced by the radical modulus `δ_U` (they agree on `M` for connected reductive `G`, which
is not proved here). -/
def IsDynamicConstantTerm (f : RationalPoint F G.X → ℂ) (fP : dynamicLeviPoints χ → ℂ) :
    Prop :=
  ∀ m : dynamicLeviPoints χ, ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
    (dynamicHalfModulus χ (m * dynamicCocharPoint χ t ^ r))⁻¹ *
        f ((m * dynamicCocharPoint χ t ^ r : dynamicLeviPoints χ) : RationalPoint F G.X) =
      fP (m * dynamicCocharPoint χ t ^ r)

omit [Smooth G.X.hom] in
theorem isDynamicConstantTerm_zero : IsDynamicConstantTerm χ t 0 0 :=
  fun _ => ⟨0, fun _ _ => by simp⟩

omit [Smooth G.X.hom] in
theorem IsDynamicConstantTerm.add {f₁ f₂ : RationalPoint F G.X → ℂ}
    {g₁ g₂ : dynamicLeviPoints χ → ℂ} (h₁ : IsDynamicConstantTerm χ t f₁ g₁)
    (h₂ : IsDynamicConstantTerm χ t f₂ g₂) : IsDynamicConstantTerm χ t (f₁ + f₂) (g₁ + g₂) := by
  intro m
  obtain ⟨r₁, hr₁⟩ := h₁ m
  obtain ⟨r₂, hr₂⟩ := h₂ m
  refine ⟨max r₁ r₂, fun r hr => ?_⟩
  rw [Pi.add_apply, Pi.add_apply, mul_add, hr₁ r (le_of_max_le_left hr),
    hr₂ r (le_of_max_le_right hr)]

omit [Smooth G.X.hom] in
theorem IsDynamicConstantTerm.smul {f : RationalPoint F G.X → ℂ}
    {g : dynamicLeviPoints χ → ℂ} (h : IsDynamicConstantTerm χ t f g) (c : ℂ) :
    IsDynamicConstantTerm χ t (c • f) (c • g) := by
  intro m
  obtain ⟨r₀, hr₀⟩ := h m
  refine ⟨r₀, fun r hr => ?_⟩
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, hr₀ r hr]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
/-- `χ(t)` is central in `Z(χ)(F)`. -/
theorem dynamicCocharPoint_commute (m : dynamicLeviPoints χ) :
    Commute (dynamicCocharPoint χ t) m :=
  Subtype.ext (commute_cocharPoint χ m.2 t).symm.eq

omit [Smooth G.X.hom] in
/-- **Right translation by the Levi.** If `f_P` is a constant term of `f`, then
`y ↦ δ_U(m₀)^{1/2} f_P(y m₀)` is a constant term of `x ↦ f(x m₀)`. -/
theorem IsDynamicConstantTerm.mul_right {f : RationalPoint F G.X → ℂ}
    {g : dynamicLeviPoints χ → ℂ} (h : IsDynamicConstantTerm χ t f g)
    (m₀ : dynamicLeviPoints χ) :
    IsDynamicConstantTerm χ t (fun x => f (x * (m₀ : RationalPoint F G.X)))
      (fun y => dynamicHalfModulus χ m₀ * g (y * m₀)) := by
  intro m
  obtain ⟨r₀, hr₀⟩ := h (m * m₀)
  refine ⟨r₀, fun r hr => ?_⟩
  have hc : m * dynamicCocharPoint χ t ^ r * m₀ = m * m₀ * dynamicCocharPoint χ t ^ r := by
    rw [mul_assoc, ((dynamicCocharPoint_commute χ t m₀).pow_left r).eq, ← mul_assoc]
  have hpt : ((m * dynamicCocharPoint χ t ^ r : dynamicLeviPoints χ) : RationalPoint F G.X) *
      (m₀ : RationalPoint F G.X) =
      ((m * m₀ * dynamicCocharPoint χ t ^ r : dynamicLeviPoints χ) : RationalPoint F G.X) := by
    rw [← hc]
    rfl
  have hδ : dynamicHalfModulus χ (m * m₀ * dynamicCocharPoint χ t ^ r) =
      dynamicHalfModulus χ (m * dynamicCocharPoint χ t ^ r) * dynamicHalfModulus χ m₀ := by
    rw [← hc, dynamicHalfModulus_mul]
  have key := hr₀ r hr
  rw [hδ] at key
  change (dynamicHalfModulus χ (m * dynamicCocharPoint χ t ^ r))⁻¹ *
      f (((m * dynamicCocharPoint χ t ^ r : dynamicLeviPoints χ) : RationalPoint F G.X) *
        (m₀ : RationalPoint F G.X)) =
    dynamicHalfModulus χ m₀ * g (m * dynamicCocharPoint χ t ^ r * m₀)
  rw [hpt, hc, ← key, mul_inv]
  have h₁ := dynamicHalfModulus_ne_zero χ m₀
  have h₂ := dynamicHalfModulus_ne_zero χ (m * dynamicCocharPoint χ t ^ r)
  field_simp

omit [Smooth G.X.hom] in
/-- **Left translation by the Levi.** If `f_P` is a constant term of `f`, then
`y ↦ δ_U(m₀)^{1/2} f_P(m₀ y)` is a constant term of `x ↦ f(m₀ x)`. -/
theorem IsDynamicConstantTerm.mul_left {f : RationalPoint F G.X → ℂ}
    {g : dynamicLeviPoints χ → ℂ} (h : IsDynamicConstantTerm χ t f g)
    (m₀ : dynamicLeviPoints χ) :
    IsDynamicConstantTerm χ t (fun x => f ((m₀ : RationalPoint F G.X) * x))
      (fun y => dynamicHalfModulus χ m₀ * g (m₀ * y)) := by
  intro m
  obtain ⟨r₀, hr₀⟩ := h (m₀ * m)
  refine ⟨r₀, fun r hr => ?_⟩
  have hδ : dynamicHalfModulus χ (m₀ * m * dynamicCocharPoint χ t ^ r) =
      dynamicHalfModulus χ m₀ * dynamicHalfModulus χ (m * dynamicCocharPoint χ t ^ r) := by
    rw [mul_assoc, dynamicHalfModulus_mul]
  have key := hr₀ r hr
  rw [hδ] at key
  change (dynamicHalfModulus χ (m * dynamicCocharPoint χ t ^ r))⁻¹ *
      f ((m₀ : RationalPoint F G.X) *
        ((m * dynamicCocharPoint χ t ^ r : dynamicLeviPoints χ) : RationalPoint F G.X)) =
    dynamicHalfModulus χ m₀ * g (m₀ * (m * dynamicCocharPoint χ t ^ r))
  have hpt : (m₀ : RationalPoint F G.X) *
      ((m * dynamicCocharPoint χ t ^ r : dynamicLeviPoints χ) : RationalPoint F G.X) =
      ((m₀ * m * dynamicCocharPoint χ t ^ r : dynamicLeviPoints χ) : RationalPoint F G.X) := by
    rw [mul_assoc]
    rfl
  rw [hpt, ← mul_assoc, ← key, mul_inv]
  have h₁ := dynamicHalfModulus_ne_zero χ m₀
  have h₂ := dynamicHalfModulus_ne_zero χ (m * dynamicCocharPoint χ t ^ r)
  field_simp

/-- The cyclic subgroup of `Z(χ)(F)` generated by `χ(t)`; it is central. -/
abbrev dynamicCocharSubgroup : Subgroup (dynamicLeviPoints χ) :=
  Subgroup.zpowers (dynamicCocharPoint χ t)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
theorem dynamicCocharSubgroup_central :
    ∀ z ∈ dynamicCocharSubgroup χ t, ∀ m : dynamicLeviPoints χ, z * m = m * z := by
  intro z hz m
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← hk]
  exact ((dynamicCocharPoint_commute χ t m).zpow_left k).eq

omit [Smooth G.X.hom] in
/-- **Uniqueness along the powers of `χ(t)`, for right-finite functions.** Two functions on
`M` that are finite under right translation by `⟨χ(t)⟩` and are constant terms of the same `f`
are equal. -/
theorem IsDynamicConstantTerm.eq_of_isRightFinite {f : RationalPoint F G.X → ℂ}
    {f₁ f₂ : dynamicLeviPoints χ → ℂ}
    (h₁ : HarishChandraSchwartz.IsRightFinite (dynamicCocharSubgroup χ t) f₁)
    (h₂ : HarishChandraSchwartz.IsRightFinite (dynamicCocharSubgroup χ t) f₂)
    (hf₁ : IsDynamicConstantTerm χ t f f₁) (hf₂ : IsDynamicConstantTerm χ t f f₂) :
    f₁ = f₂ := by
  let gL : dynamicLeviPoints χ := dynamicCocharPoint χ t
  let Z : Subgroup (dynamicLeviPoints χ) := dynamicCocharSubgroup χ t
  let s : Z := ⟨gL, Subgroup.mem_zpowers gL⟩
  have hspow : ∀ r : ℕ, ((s ^ r : Z) : dynamicLeviPoints χ) = gL ^ r := fun r =>
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
  obtain ⟨r₁, hr₁⟩ := hf₁ m
  obtain ⟨r₂, hr₂⟩ := hf₂ m
  refine ⟨{z | ∃ r, max r₁ r₂ ≤ r ∧ z = s ^ r}, ⟨s ^ max r₁ r₂, max r₁ r₂, le_rfl, rfl⟩,
    ?_, ?_⟩
  · rintro c ⟨r, hr, rfl⟩ x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨r + 1, hr.trans (Nat.le_succ r), (pow_succ s r).symm⟩
  · rintro c ⟨r, hr, rfl⟩
    rw [hspow r, ← hr₁ r (le_of_max_le_left hr), ← hr₂ r (le_of_max_le_right hr)]

omit [Smooth G.X.hom] in
/-- **Uniqueness in Proposition I.6.2 along the powers of `χ(t)`.** Two elements of `A(M)` (each
a coefficient of an admissible representation of `M = Z(χ)(F)`) that are constant terms of the
same function `f` along the powers of `χ(t)` are equal. -/
theorem eq_of_isDynamicConstantTerm {f : RationalPoint F G.X → ℂ}
    {f₁ f₂ : dynamicLeviPoints χ → ℂ}
    (h₁ : ∃ B : SmoothRep.{0, u, uV} ℂ (dynamicLeviPoints χ), IsAdmissible B.representation ∧
      f₁ ∈ HarishChandraSchwartz.coefficientFunctionSpace B)
    (h₂ : ∃ B : SmoothRep.{0, u, uW} ℂ (dynamicLeviPoints χ), IsAdmissible B.representation ∧
      f₂ ∈ HarishChandraSchwartz.coefficientFunctionSpace B)
    (hf₁ : IsDynamicConstantTerm χ t f f₁) (hf₂ : IsDynamicConstantTerm χ t f f₂) :
    f₁ = f₂ := by
  obtain ⟨B₁, hB₁, hf₁B⟩ := h₁
  obtain ⟨B₂, hB₂, hf₂B⟩ := h₂
  exact hf₁.eq_of_isRightFinite χ t
    (HarishChandraSchwartz.isRightFinite_of_mem_coefficientFunctionSpace hB₁ _
      (dynamicCocharSubgroup_central χ t) hf₁B)
    (HarishChandraSchwartz.isRightFinite_of_mem_coefficientFunctionSpace hB₂ _
      (dynamicCocharSubgroup_central χ t) hf₂B) hf₂

/-- `f` has a constant term along the powers of `χ(t)` that is finite under right translation by
`⟨χ(t)⟩` (by `eq_of_isRightFinite` it is then unique). -/
def HasDynamicConstantTerm (f : RationalPoint F G.X → ℂ) : Prop :=
  ∃ fP : dynamicLeviPoints χ → ℂ,
    HarishChandraSchwartz.IsRightFinite (dynamicCocharSubgroup χ t) fP ∧
      IsDynamicConstantTerm χ t f fP

open Classical in
/-- **The constant term `f_P` along the powers of `χ(t)`** (Waldspurger's `f_P`, I.6.2): the
unique right-finite constant term of `f` when it exists, and `0` otherwise. For `f ∈ A(ρ)`
with `ρ` admissible it exists and lies in `A(M)` (`dynamicConstantTerm_spec`). -/
def dynamicConstantTerm (f : RationalPoint F G.X → ℂ) : dynamicLeviPoints χ → ℂ :=
  if h : HasDynamicConstantTerm χ t f then h.choose else 0

omit [Smooth G.X.hom] in
theorem HasDynamicConstantTerm.isRightFinite {f : RationalPoint F G.X → ℂ}
    (h : HasDynamicConstantTerm χ t f) :
    HarishChandraSchwartz.IsRightFinite (dynamicCocharSubgroup χ t)
      (dynamicConstantTerm χ t f) := by
  rw [dynamicConstantTerm, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.1

omit [Smooth G.X.hom] in
theorem HasDynamicConstantTerm.isDynamicConstantTerm {f : RationalPoint F G.X → ℂ}
    (h : HasDynamicConstantTerm χ t f) :
    IsDynamicConstantTerm χ t f (dynamicConstantTerm χ t f) := by
  rw [dynamicConstantTerm, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.2

omit [Smooth G.X.hom] in
/-- Every right-finite constant term of `f` is `dynamicConstantTerm χ t f`. -/
theorem dynamicConstantTerm_eq {f : RationalPoint F G.X → ℂ} {fP : dynamicLeviPoints χ → ℂ}
    (hR : HarishChandraSchwartz.IsRightFinite (dynamicCocharSubgroup χ t) fP)
    (h : IsDynamicConstantTerm χ t f fP) : dynamicConstantTerm χ t f = fP :=
  (HasDynamicConstantTerm.isDynamicConstantTerm χ t ⟨fP, hR, h⟩).eq_of_isRightFinite χ t
    (HasDynamicConstantTerm.isRightFinite χ t ⟨fP, hR, h⟩) hR h

omit [Smooth G.X.hom] in
theorem dynamicConstantTerm_add {f₁ f₂ : RationalPoint F G.X → ℂ}
    (h₁ : HasDynamicConstantTerm χ t f₁) (h₂ : HasDynamicConstantTerm χ t f₂) :
    dynamicConstantTerm χ t (f₁ + f₂) = dynamicConstantTerm χ t f₁ + dynamicConstantTerm χ t f₂ :=
  dynamicConstantTerm_eq χ t (h₁.isRightFinite χ t |>.add (h₂.isRightFinite χ t))
    ((h₁.isDynamicConstantTerm χ t).add χ t (h₂.isDynamicConstantTerm χ t))

omit [Smooth G.X.hom] in
theorem dynamicConstantTerm_smul {f : RationalPoint F G.X → ℂ}
    (h : HasDynamicConstantTerm χ t f) (c : ℂ) :
    dynamicConstantTerm χ t (c • f) = c • dynamicConstantTerm χ t f :=
  dynamicConstantTerm_eq χ t ((h.isRightFinite χ t).smul c)
    ((h.isDynamicConstantTerm χ t).smul χ t c)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
theorem isRightFinite_comp_mul_right {φ : dynamicLeviPoints χ → ℂ}
    (h : HarishChandraSchwartz.IsRightFinite (dynamicCocharSubgroup χ t) φ)
    (m₀ : dynamicLeviPoints χ) :
    HarishChandraSchwartz.IsRightFinite (dynamicCocharSubgroup χ t) (fun y => φ (y * m₀)) := by
  obtain ⟨W, hW, hφ, hWZ⟩ := h
  let L : (dynamicLeviPoints χ → ℂ) →ₗ[ℂ] (dynamicLeviPoints χ → ℂ) :=
    { toFun := fun ψ y => ψ (y * m₀)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨W.map L, inferInstance, ⟨φ, hφ, rfl⟩, ?_⟩
  rintro x hx _ ⟨ψ, hψ, rfl⟩
  refine ⟨fun y => ψ (y * x), hWZ x hx ψ hψ, ?_⟩
  funext y
  change ψ (y * m₀ * x) = ψ (y * x * m₀)
  rw [mul_assoc, ← dynamicCocharSubgroup_central χ t x hx m₀, ← mul_assoc]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
theorem isRightFinite_comp_mul_left {φ : dynamicLeviPoints χ → ℂ}
    (h : HarishChandraSchwartz.IsRightFinite (dynamicCocharSubgroup χ t) φ)
    (m₀ : dynamicLeviPoints χ) :
    HarishChandraSchwartz.IsRightFinite (dynamicCocharSubgroup χ t) (fun y => φ (m₀ * y)) := by
  obtain ⟨W, hW, hφ, hWZ⟩ := h
  let L : (dynamicLeviPoints χ → ℂ) →ₗ[ℂ] (dynamicLeviPoints χ → ℂ) :=
    { toFun := fun ψ y => ψ (m₀ * y)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨W.map L, inferInstance, ⟨φ, hφ, rfl⟩, ?_⟩
  rintro x hx _ ⟨ψ, hψ, rfl⟩
  refine ⟨fun y => ψ (y * x), hWZ x hx ψ hψ, ?_⟩
  funext y
  change ψ (m₀ * y * x) = ψ (m₀ * (y * x))
  rw [mul_assoc]

omit [Smooth G.X.hom] in
/-- **`(ρ(m₀) f)_P = δ_U(m₀)^{1/2} ρ(m₀) f_P`** for `m₀ ∈ Z(χ)(F)`. -/
theorem dynamicConstantTerm_mul_right {f : RationalPoint F G.X → ℂ}
    (h : HasDynamicConstantTerm χ t f) (m₀ : dynamicLeviPoints χ) :
    dynamicConstantTerm χ t (fun x => f (x * (m₀ : RationalPoint F G.X))) =
      fun y => dynamicHalfModulus χ m₀ * dynamicConstantTerm χ t f (y * m₀) :=
  dynamicConstantTerm_eq χ t
    (((isRightFinite_comp_mul_right χ t (h.isRightFinite χ t) m₀)).smul (dynamicHalfModulus χ m₀))
    ((h.isDynamicConstantTerm χ t).mul_right χ t m₀)

omit [Smooth G.X.hom] in
/-- **`(λ(m₀⁻¹) f)_P = δ_U(m₀)^{1/2} λ(m₀⁻¹) f_P`** for `m₀ ∈ Z(χ)(F)`, i.e. the constant term of
`x ↦ f(m₀ x)` is `y ↦ δ_U(m₀)^{1/2} f_P(m₀ y)`. -/
theorem dynamicConstantTerm_mul_left {f : RationalPoint F G.X → ℂ}
    (h : HasDynamicConstantTerm χ t f) (m₀ : dynamicLeviPoints χ) :
    dynamicConstantTerm χ t (fun x => f ((m₀ : RationalPoint F G.X) * x)) =
      fun y => dynamicHalfModulus χ m₀ * dynamicConstantTerm χ t f (m₀ * y) :=
  dynamicConstantTerm_eq χ t
    (((isRightFinite_comp_mul_left χ t (h.isRightFinite χ t) m₀)).smul (dynamicHalfModulus χ m₀))
    ((h.isDynamicConstantTerm χ t).mul_left χ t m₀)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- **Existence in Proposition I.6.2 for one coefficient.** For a stable pairing `b` of the
dynamic data, the Library's constant term `m ↦ b(ǰ(ℓ), π_P(m) j(v))` (normalized by `δ_U`) of the
coefficient `x ↦ ℓ(ρ(x) v)` has the constant-term property along the powers of `χ(t)`. -/
theorem isDynamicConstantTerm_coefficientConstantTerm
    (ρ : Representation ℂ (RationalPoint F G.X) V) (hρ : IsAdmissible ρ)
    {b : Coinvariants (smoothContragredient ρ) (unipotentPoints (Dynamic.inverseCocharacter χ))
        →ₗ[ℂ] Coinvariants ρ (unipotentPoints χ) →ₗ[ℂ] ℂ}
    (hb : (dynamicCasselmanPairingData χ t ht).IsStablePairing ρ hρ.1 b)
    (ℓ : SmoothDual ρ) (v : V) :
    IsDynamicConstantTerm χ t (fun x => smoothDualPairing ρ ℓ (ρ x v))
      ((dynamicCasselmanPairingData χ t ht).coefficientConstantTerm ρ b
        (dynamicParabolicModulus χ) ℓ v) := by
  intro m
  let D := dynamicCasselmanPairingData χ t ht
  have hA : D.Admits ρ hρ.1 := dynamicCasselmanPairingData_admits χ t ht ρ hρ
  obtain ⟨K, -, Fs, hFs, h⟩ := (hb.hasAsymptotics hA).exists_coefficientConstantTerm hρ.1
    (dynamicParabolicModulus χ) ℓ v m
  have hg : D.g⁻¹ = cocharPoint χ t := dynamicCasselmanPairingData_g_inv χ t ht
  have hcon : D.IsContractingElement (cocharPoint χ t) := hg ▸ D.isContractingElement_inv
  have hev := eventually_cocharPoint_pow_conj_mem_ambient χ t ht (Fs : Set (RationalPoint F G.X))
    Fs.finite_toSet.isCompact hFs (K : Set (RationalPoint F G.X))
    (K.isOpen.mem_nhds K.one_mem)
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨r₀, fun r hr => ?_⟩
  have hc := D.isContractingElement_pow hcon (cocharPoint_mem_centralizer χ t) r
  have key := h (dynamicCocharPoint χ t ^ r)
    (by rw [coe_dynamicCocharPoint_pow]; exact hc)
    (by
      intro n hn
      rw [coe_dynamicCocharPoint_pow]
      exact hr₀ r hr n hn)
  exact key

include ht in
/-- **Existence in Proposition I.6.2 along the powers of `χ(t)`, with the radical
invariances.** For an admissible `ρ` there is one admissible smooth representation `B` of
`M = Z(χ)(F)` (the normalized Jacquet module of `ρ` along `U(χ)(F)`) such that every
`f ∈ A(ρ)` has a constant term `f_P ∈ A(B)` along the powers of `χ(t)`, which is also a constant
term of `x ↦ f(x n)` for `n ∈ U(χ)(F)` and of `x ↦ f(n x)` for `n ∈ U(χ⁻¹)(F)`. -/
theorem exists_dynamicConstantTerm (ρ : Representation ℂ (RationalPoint F G.X) V)
    (hρ : IsAdmissible ρ) :
    ∃ B : SmoothRep.{0, u, uV} ℂ (dynamicLeviPoints χ), IsAdmissible B.representation ∧
      ∀ f ∈ HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1),
        ∃ fP ∈ HarishChandraSchwartz.coefficientFunctionSpace B,
          IsDynamicConstantTerm χ t f fP ∧
          (∀ n ∈ unipotentPoints χ, IsDynamicConstantTerm χ t (fun x => f (x * n)) fP) ∧
          (∀ n ∈ unipotentPoints (Dynamic.inverseCocharacter χ),
            IsDynamicConstantTerm χ t (fun x => f (n * x)) fP) := by
  let D := dynamicCasselmanPairingData χ t ht
  have hA : D.Admits ρ hρ.1 := dynamicCasselmanPairingData_admits χ t ht ρ hρ
  obtain ⟨b, hb⟩ := D.exists_isStablePairing hA
  have hδ := isOpen_ker_dynamicParabolicModulus χ
  have hbasis : HasIwahoriContractionBasis D.Nbar D.M D.N :=
    (hasOppositeIwahoriContractionBasis_cocharPoint χ t ht).hasIwahoriContractionBasis
  let B : SmoothRep.{0, u, uV} ℂ (dynamicLeviPoints χ) :=
    SmoothRep.of (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar (dynamicParabolicModulus χ))
      (isSmooth_normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar _ hδ hρ.1)
  refine ⟨B, isAdmissible_normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar _ hδ hρ.1
    (isAdmissible_action_of_iwahoriContraction ρ hρ D.Nbar D.M D.N D.hMNbar hbasis), ?_⟩
  let W : Submodule ℂ (RationalPoint F G.X → ℂ) :=
    { carrier := {f | ∃ fP ∈ HarishChandraSchwartz.coefficientFunctionSpace B,
        IsDynamicConstantTerm χ t f fP ∧
        (∀ n ∈ unipotentPoints χ, IsDynamicConstantTerm χ t (fun x => f (x * n)) fP) ∧
        (∀ n ∈ unipotentPoints (Dynamic.inverseCocharacter χ),
          IsDynamicConstantTerm χ t (fun x => f (n * x)) fP)}
      add_mem' := by
        rintro f₁ f₂ ⟨g₁, hg₁, h₁, hU₁, hO₁⟩ ⟨g₂, hg₂, h₂, hU₂, hO₂⟩
        exact ⟨g₁ + g₂, Submodule.add_mem _ hg₁ hg₂, h₁.add χ t h₂,
          fun n hn => (hU₁ n hn).add χ t (hU₂ n hn),
          fun n hn => (hO₁ n hn).add χ t (hO₂ n hn)⟩
      zero_mem' := ⟨0, Submodule.zero_mem _, isDynamicConstantTerm_zero χ t,
        fun _ _ => isDynamicConstantTerm_zero χ t, fun _ _ => isDynamicConstantTerm_zero χ t⟩
      smul_mem' := by
        rintro c f ⟨g, hg, h, hU, hO⟩
        exact ⟨c • g, Submodule.smul_mem _ c hg, h.smul χ t c,
          fun n hn => (hU n hn).smul χ t c, fun n hn => (hO n hn).smul χ t c⟩ }
  have hle : HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1) ≤ W := by
    refine iSup_le fun ℓ => ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨D.coefficientConstantTerm ρ b (dynamicParabolicModulus χ) ℓ x,
      hb.coefficientConstantTerm_mem_coefficientFunctionSpace hA _ hδ ℓ x,
      isDynamicConstantTerm_coefficientConstantTerm χ t ht ρ hρ hb ℓ x, ?_, ?_⟩
    · intro n hn
      have e : D.coefficientConstantTerm ρ b (dynamicParabolicModulus χ) ℓ (ρ n x) =
          D.coefficientConstantTerm ρ b (dynamicParabolicModulus χ) ℓ x := by
        funext m
        simp only [StablePairingData.coefficientConstantTerm]
        congr 2
        exact mk_apply_subgroup ρ D.Nbar ⟨n, hn⟩ x
      have h := isDynamicConstantTerm_coefficientConstantTerm χ t ht ρ hρ hb ℓ (ρ n x)
      rw [e] at h
      have hfun : (fun y => smoothDualPairing ρ ℓ (ρ y (ρ n x))) =
          fun y => matrixCoefficient (SmoothRep.of ρ hρ.1).representation ℓ.val x (y * n) := by
        funext y
        change smoothDualPairing ρ ℓ (ρ y (ρ n x)) = smoothDualPairing ρ ℓ (ρ (y * n) x)
        rw [map_mul, Module.End.mul_apply]
      exact hfun ▸ h
    · intro n hn
      have hn' : n⁻¹ ∈ D.N := inv_mem hn
      have e : D.coefficientConstantTerm ρ b (dynamicParabolicModulus χ)
          (smoothContragredient ρ n⁻¹ ℓ) x =
          D.coefficientConstantTerm ρ b (dynamicParabolicModulus χ) ℓ x := by
        funext m
        simp only [StablePairingData.coefficientConstantTerm]
        congr 2
        exact mk_apply_subgroup (smoothContragredient ρ) D.N ⟨n⁻¹, hn'⟩ ℓ
      have h := isDynamicConstantTerm_coefficientConstantTerm χ t ht ρ hρ hb
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

include ht in
/-- **Waldspurger, Proposition I.6.2, for actual dynamic parabolic subgroups, along the powers
of `χ(t)`.** For an admissible smooth representation `ρ` of `G(F)` and `f ∈ A(ρ)`, there is a
unique function `f_P` on `M = Z(χ)(F)` lying in `A(M)` (a coefficient of an admissible smooth
representation of `M` on a space in the universe of `ρ`'s space) such that for every `m ∈ M`
`δ_U(m χ(t)^r)^{-1/2} f(m χ(t)^r) = f_P(m χ(t)^r)` for all sufficiently large `r`. No structural
hypothesis is used. -/
theorem existsUnique_dynamicConstantTerm (ρ : Representation ℂ (RationalPoint F G.X) V)
    (hρ : IsAdmissible ρ) {f : RationalPoint F G.X → ℂ}
    (hf : f ∈ HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1)) :
    ∃! fP : dynamicLeviPoints χ → ℂ,
      (∃ B : SmoothRep.{0, u, uV} ℂ (dynamicLeviPoints χ), IsAdmissible B.representation ∧
        fP ∈ HarishChandraSchwartz.coefficientFunctionSpace B) ∧
      IsDynamicConstantTerm χ t f fP := by
  obtain ⟨B, hB, hex⟩ := exists_dynamicConstantTerm χ t ht ρ hρ
  obtain ⟨fP, hfPB, hfP, -, -⟩ := hex f hf
  exact ⟨fP, ⟨⟨B, hB, hfPB⟩, hfP⟩, fun f' ⟨h', hf'⟩ =>
    eq_of_isDynamicConstantTerm χ t h' ⟨B, hB, hfPB⟩ hf' hfP⟩

include ht in
/-- **The constant term of `f ∈ A(ρ)`.** For admissible `ρ` and `f ∈ A(ρ)`, `f` has a constant
term along the powers of `χ(t)`; `dynamicConstantTerm χ t f` is this constant term and lies in
`A(M)`. -/
theorem dynamicConstantTerm_spec (ρ : Representation ℂ (RationalPoint F G.X) V)
    (hρ : IsAdmissible ρ) {f : RationalPoint F G.X → ℂ}
    (hf : f ∈ HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1)) :
    HasDynamicConstantTerm χ t f ∧ IsDynamicConstantTerm χ t f (dynamicConstantTerm χ t f) ∧
      ∃ B : SmoothRep.{0, u, uV} ℂ (dynamicLeviPoints χ), IsAdmissible B.representation ∧
        dynamicConstantTerm χ t f ∈ HarishChandraSchwartz.coefficientFunctionSpace B := by
  obtain ⟨B, hB, hex⟩ := exists_dynamicConstantTerm χ t ht ρ hρ
  obtain ⟨fP, hfPB, hfP, -, -⟩ := hex f hf
  have hR := HarishChandraSchwartz.isRightFinite_of_mem_coefficientFunctionSpace hB _
    (dynamicCocharSubgroup_central χ t) hfPB
  have e := dynamicConstantTerm_eq χ t hR hfP
  exact ⟨⟨fP, hR, hfP⟩, e ▸ hfP, B, hB, e ▸ hfPB⟩

include ht in
/-- **Invariance under the radical: `(ρ(n) f)_P = f_P`** for `n ∈ U(χ)(F)` and `f ∈ A(ρ)`. -/
theorem dynamicConstantTerm_mul_radical (ρ : Representation ℂ (RationalPoint F G.X) V)
    (hρ : IsAdmissible ρ) {f : RationalPoint F G.X → ℂ}
    (hf : f ∈ HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1))
    {n : RationalPoint F G.X} (hn : n ∈ unipotentPoints χ) :
    dynamicConstantTerm χ t (fun x => f (x * n)) = dynamicConstantTerm χ t f := by
  obtain ⟨B, hB, hex⟩ := exists_dynamicConstantTerm χ t ht ρ hρ
  obtain ⟨fP, hfPB, hfP, hU, -⟩ := hex f hf
  have hR := HarishChandraSchwartz.isRightFinite_of_mem_coefficientFunctionSpace hB _
    (dynamicCocharSubgroup_central χ t) hfPB
  rw [dynamicConstantTerm_eq χ t hR (hU n hn), dynamicConstantTerm_eq χ t hR hfP]

include ht in
/-- **Invariance under the opposite radical: `(λ(n) f)_P = f_P`** for `n ∈ U(χ⁻¹)(F)` and
`f ∈ A(ρ)`, i.e. the constant term of `x ↦ f(n x)` is `f_P`. -/
theorem dynamicConstantTerm_oppositeRadical_mul (ρ : Representation ℂ (RationalPoint F G.X) V)
    (hρ : IsAdmissible ρ) {f : RationalPoint F G.X → ℂ}
    (hf : f ∈ HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1))
    {n : RationalPoint F G.X} (hn : n ∈ unipotentPoints (Dynamic.inverseCocharacter χ)) :
    dynamicConstantTerm χ t (fun x => f (n * x)) = dynamicConstantTerm χ t f := by
  obtain ⟨B, hB, hex⟩ := exists_dynamicConstantTerm χ t ht ρ hρ
  obtain ⟨fP, hfPB, hfP, -, hO⟩ := hex f hf
  have hR := HarishChandraSchwartz.isRightFinite_of_mem_coefficientFunctionSpace hB _
    (dynamicCocharSubgroup_central χ t) hfPB
  rw [dynamicConstantTerm_eq χ t hR (hO n hn), dynamicConstantTerm_eq χ t hR hfP]

end ConstantTerm

end Langlands.Jacquet

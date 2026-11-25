import Langlands.Global.Arithmetic.SUnitIdelePowerQuotient
import Langlands.Global.IdeleClosedSubgroupDensity

/-!
# The `S`-idèle class group and its narrow variant

For a number field `K` and a set `S` of finite places of `K`, let `U^S` be the group of idèles
whose component is `1` at every place of `S` and a unit of the valuation ring at every finite
place outside `S`, the archimedean components being arbitrary (`unitIdelesOutside S`), and `U^S_+`
the subgroup of those that are moreover positive at every real place
(`positiveUnitIdelesOutside S`). The **`S`-idèle class group** is `I_K / K^× U^S`
(`SIdeleClassGroup S`), the **narrow `S`-idèle class group** is `I_K / K^× U^S_+`
(`NarrowSIdeleClassGroup S`); both are quotients of the idèle class group, and the first is a
quotient of the second (`NarrowSIdeleClassGroup.toSIdeleClassGroup`).

Two facts about the idèle topology serve the description of the characters of the Galois group
of the maximal extension unramified outside `S`:

* a continuous homomorphism from the idèles to a discrete group of exponent dividing `n ≠ 0`
  that kills the integral local units at the finite places outside `S` kills `U^S_+`
  (`positiveUnitIdelesOutside_le_ker`): the positive archimedean idèles are `n`-th powers, and
  an idèle of integral units that is `1` on `S` is a limit of finite products of local units;
* for finite `S`, a subgroup of the idèles that contains all `n`-th powers and `U^S_+` is open
  (`isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le`): it contains the open subgroup of the
  idèles that are units outside `S`, `n`-th powers at the places of `S` and `n`-th powers at the
  archimedean places.

Finally, the square of an element of `U^S` lies in `U^S_+`, and if `K` has no real place the two
groups are equal; so a homomorphism from the narrow group to a group of odd exponent, or any
homomorphism if `K` is totally complex, factors through `SIdeleClassGroup S`.

## References

Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter VIII, §3, p. 454: the
`S`-idèle class group `C_S(K) = I_K / K^× U_{K,S}`, where `S` contains the archimedean places and
`U_{K,S}` has components `1` at `S` and local units elsewhere. In that notation, for `S` a set of
finite places, `SIdeleClassGroup S` is `C_{S ∪ S_∞}(K)` modulo the image of all archimedean
components, and `NarrowSIdeleClassGroup S` is `C_{S ∪ S_∞}(K)` modulo the image of the archimedean
components positive at the real places (the identity component of `∏_{v | ∞} K_v^×`).
Neukirch, *Algebraic Number Theory*, Chapter V, p. 322: in characteristic `0` a subgroup of finite
index of `K_v^×` is open.
-/

noncomputable section

universe u

namespace Langlands.GaloisCohomology

open Langlands.Global IsDedekindDomain
open scoped NumberField

variable {K : Type u} [Field K] [NumberField K]

section Components

/-- The component at a finite place `w` of the idèle inserted at another finite place is `1`. -/
theorem finiteIdeleProjection_finiteIdeleInclusion_of_ne {v w : FinitePlace K} (h : w ≠ v)
    (a : (FiniteCompletion K v)ˣ) :
    finiteIdeleProjection K w (finiteIdeleInclusion K v a) = 1 := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_of_ne h _

/-- The archimedean components of an idèle inserted at a finite place are `1`. -/
theorem infiniteIdeleProjection_finiteIdeleInclusion (w : InfinitePlace K) (v : FinitePlace K)
    (a : (FiniteCompletion K v)ˣ) :
    infiniteIdeleProjection K w (finiteIdeleInclusion K v a) = 1 :=
  rfl

/-- The finite components of an archimedean idèle are `1`. -/
theorem finiteIdeleProjection_infiniteIdelesInclusion (v : FinitePlace K)
    (z : (InfiniteAdeles K)ˣ) :
    finiteIdeleProjection K v (infiniteIdelesInclusion K z) = 1 :=
  rfl

/-- The component at an archimedean place `w` of the archimedean idèle `z` is the component
of `z` at `w`. -/
theorem infiniteIdeleProjection_infiniteIdelesInclusion (w : InfinitePlace K)
    (z : (InfiniteAdeles K)ˣ) :
    infiniteIdeleProjection K w (infiniteIdelesInclusion K z) = ContinuousMulEquiv.piUnits z w :=
  rfl

end Components

section Subgroups

variable (K) in
/-- The idèles whose component at every real place is positive. -/
def positiveIdeles : Subgroup (Ideles K) where
  carrier := {x | ∀ (w : InfinitePlace K) (hw : w.IsReal),
    0 < NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
      (infiniteIdeleProjection K w x : InfiniteCompletion K w)}
  mul_mem' {x y} hx hy w hw := by
    rw [map_mul, Units.val_mul, map_mul]
    exact mul_pos (hx w hw) (hy w hw)
  one_mem' w hw := by
    rw [map_one, Units.val_one, map_one]
    exact one_pos
  inv_mem' {x} hx w hw := by
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_pos.2 (hx w hw)

/-- Membership in `positiveIdeles K`. -/
theorem mem_positiveIdeles {x : Ideles K} :
    x ∈ positiveIdeles K ↔ ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
        (infiniteIdeleProjection K w x : InfiniteCompletion K w) :=
  Iff.rfl

/-- The square of an idèle is positive at every real place. -/
theorem sq_mem_positiveIdeles (x : Ideles K) : x ^ 2 ∈ positiveIdeles K := by
  intro w hw
  rw [map_pow, Units.val_pow_eq_pow_val, map_pow]
  have h0 : NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
      (infiniteIdeleProjection K w x : InfiniteCompletion K w) ≠ 0 := by
    simp
  positivity

/-- If `K` has no real place, every idèle is positive. -/
theorem positiveIdeles_eq_top [NumberField.IsTotallyComplex K] : positiveIdeles K = ⊤ :=
  eq_top_iff.2 fun _ _ w hw =>
    absurd hw (NumberField.InfinitePlace.not_isReal_iff_isComplex.2
      (NumberField.IsTotallyComplex.isComplex w))

/-- The idèles whose component is `1` at every place of `S` and a unit of the valuation ring at
every finite place outside `S`; the archimedean components are arbitrary. -/
def unitIdelesOutside (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (Ideles K) where
  carrier := {x | (∀ v ∈ S, finiteIdeleProjection K v x = 1) ∧
    ∀ v ∉ S, finiteIdeleProjection K v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units}
  mul_mem' {x y} hx hy := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [map_mul, hx.1 v hv, hy.1 v hv, one_mul]
    · rw [map_mul]
      exact Subgroup.mul_mem _ (hx.2 v hv) (hy.2 v hv)
  one_mem' := ⟨fun v _ => map_one _, fun v _ => by rw [map_one]; exact Subgroup.one_mem _⟩
  inv_mem' {x} hx := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [map_inv, hx.1 v hv, inv_one]
    · rw [map_inv]
      exact Subgroup.inv_mem _ (hx.2 v hv)

/-- Membership in `unitIdelesOutside S`. -/
theorem mem_unitIdelesOutside {S : Set (HeightOneSpectrum (𝓞 K))} {x : Ideles K} :
    x ∈ unitIdelesOutside S ↔ (∀ v ∈ S, finiteIdeleProjection K v x = 1) ∧
      ∀ v ∉ S,
        finiteIdeleProjection K v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units :=
  Iff.rfl

/-- A unit of a finite completion is a unit of the valuation ring exactly when its valuation is
`1`. -/
theorem mem_units_iff_valued_eq_one {v : FinitePlace K} (a : (FiniteCompletion K v)ˣ) :
    a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units ↔
      Valued.v (a : FiniteCompletion K v) = 1 := by
  refine ⟨fun ha => le_antisymm ha.1 ?_, fun ha => ⟨?_, ?_⟩⟩
  · calc (1 : WithZero (Multiplicative ℤ))
        = Valued.v (a : FiniteCompletion K v) *
            Valued.v ((a⁻¹ : (FiniteCompletion K v)ˣ) : FiniteCompletion K v) := by
          rw [← map_mul, Units.mul_inv, map_one]
      _ ≤ Valued.v (a : FiniteCompletion K v) := mul_le_of_le_one_right' ha.2
  · change Valued.v (a : FiniteCompletion K v) ≤ 1
    exact ha.le
  · change Valued.v (((a⁻¹ : (FiniteCompletion K v)ˣ)) : FiniteCompletion K v) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]

/-- Membership in `unitIdelesOutside S`, read on valuations. -/
theorem mem_unitIdelesOutside_iff_valued {S : Set (HeightOneSpectrum (𝓞 K))} {x : Ideles K} :
    x ∈ unitIdelesOutside S ↔ (∀ v ∈ S, finiteIdeleProjection K v x = 1) ∧
      ∀ v ∉ S, Valued.v (finiteIdeleProjection K v x : FiniteCompletion K v) = 1 := by
  simp only [mem_unitIdelesOutside, mem_units_iff_valued_eq_one]

/-- The elements of `unitIdelesOutside S` that are positive at every real place. -/
def positiveUnitIdelesOutside (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (Ideles K) :=
  unitIdelesOutside S ⊓ positiveIdeles K

/-- Membership in `positiveUnitIdelesOutside S`. -/
theorem mem_positiveUnitIdelesOutside {S : Set (HeightOneSpectrum (𝓞 K))} {x : Ideles K} :
    x ∈ positiveUnitIdelesOutside S ↔ x ∈ unitIdelesOutside S ∧ x ∈ positiveIdeles K :=
  Subgroup.mem_inf

/-- `U^S_+ ⊆ U^S`. -/
theorem positiveUnitIdelesOutside_le_unitIdelesOutside (S : Set (HeightOneSpectrum (𝓞 K))) :
    positiveUnitIdelesOutside S ≤ unitIdelesOutside S :=
  inf_le_left

/-- The square of an element of `unitIdelesOutside S` is positive at every real place. -/
theorem sq_mem_positiveUnitIdelesOutside {S : Set (HeightOneSpectrum (𝓞 K))} {x : Ideles K}
    (hx : x ∈ unitIdelesOutside S) : x ^ 2 ∈ positiveUnitIdelesOutside S :=
  mem_positiveUnitIdelesOutside.2 ⟨pow_mem hx 2, sq_mem_positiveIdeles x⟩

/-- If `K` has no real place, the positivity condition is empty. -/
theorem positiveUnitIdelesOutside_eq [NumberField.IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    positiveUnitIdelesOutside S = unitIdelesOutside S := by
  rw [positiveUnitIdelesOutside, positiveIdeles_eq_top, inf_top_eq]

/-- An integral local unit at a finite place outside `S`, inserted as an idèle, lies in
`positiveUnitIdelesOutside S`. -/
theorem finiteIdeleInclusion_mem_positiveUnitIdelesOutside {S : Set (HeightOneSpectrum (𝓞 K))}
    {v : FinitePlace K} (hv : v ∉ S) {a : (FiniteCompletion K v)ˣ}
    (ha : a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    finiteIdeleInclusion K v a ∈ positiveUnitIdelesOutside S := by
  refine mem_positiveUnitIdelesOutside.2 ⟨⟨fun w hw => ?_, fun w hw => ?_⟩, fun w hw => ?_⟩
  · exact finiteIdeleProjection_finiteIdeleInclusion_of_ne (fun h : w = v => hv (h ▸ hw)) a
  · by_cases h : w = v
    · subst h
      rwa [finiteIdeleProjection_inclusion]
    · rw [finiteIdeleProjection_finiteIdeleInclusion_of_ne h]
      exact Subgroup.one_mem _
  · rw [infiniteIdeleProjection_finiteIdeleInclusion, Units.val_one, map_one]
    exact one_pos

end Subgroups

section Quotients

/-- The subgroup `K^× U^S` of the idèles. -/
def sIdeleClassSubgroup (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (Ideles K) :=
  principalIdeles K ⊔ unitIdelesOutside S

/-- The subgroup `K^× U^S_+` of the idèles. -/
def narrowSIdeleClassSubgroup (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (Ideles K) :=
  principalIdeles K ⊔ positiveUnitIdelesOutside S

/-- `K^× U^S_+ ⊆ K^× U^S`. -/
theorem narrowSIdeleClassSubgroup_le (S : Set (HeightOneSpectrum (𝓞 K))) :
    narrowSIdeleClassSubgroup S ≤ sIdeleClassSubgroup S :=
  sup_le_sup_left (positiveUnitIdelesOutside_le_unitIdelesOutside S) _

/-- The `S`-idèle class group `I_K / K^× U^S`: the idèles modulo the principal idèles and the
idèles that are `1` at the places of `S`, local units at the other finite places and arbitrary at
the archimedean places. -/
abbrev SIdeleClassGroup (S : Set (HeightOneSpectrum (𝓞 K))) : Type u :=
  Ideles K ⧸ sIdeleClassSubgroup S

/-- The narrow `S`-idèle class group `I_K / K^× U^S_+`: as `SIdeleClassGroup S`, with only the
archimedean components positive at the real places divided out. -/
abbrev NarrowSIdeleClassGroup (S : Set (HeightOneSpectrum (𝓞 K))) : Type u :=
  Ideles K ⧸ narrowSIdeleClassSubgroup S

namespace SIdeleClassGroup

variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The class of an idèle in the `S`-idèle class group. -/
def mk : Ideles K →* SIdeleClassGroup S :=
  QuotientGroup.mk' _

/-- Every class is the class of an idèle. -/
theorem mk_surjective : Function.Surjective (mk S) :=
  QuotientGroup.mk'_surjective _

/-- The kernel of the class map. -/
theorem ker_mk : (mk S).ker = sIdeleClassSubgroup S :=
  QuotientGroup.ker_mk' _

/-- An idèle has trivial class exactly when it lies in the subgroup divided out. -/
theorem mk_eq_one_iff {x : Ideles K} : mk S x = 1 ↔ x ∈ sIdeleClassSubgroup S :=
  QuotientGroup.eq_one_iff _

/-- Principal idèles have trivial class. -/
theorem mk_diagonalUnits (a : Kˣ) : mk S (diagonalUnits K a) = 1 :=
  (mk_eq_one_iff S).2 (Subgroup.mem_sup_left ⟨a, rfl⟩)

variable {S} in
/-- The idèles of the unit subgroup have trivial class. -/
theorem mk_eq_one_of_mem {x : Ideles K} (hx : x ∈ unitIdelesOutside S) : mk S x = 1 :=
  (mk_eq_one_iff S).2 (Subgroup.mem_sup_right hx)

/-- The principal idèles lie in the subgroup divided out. -/
theorem principalIdeles_le : principalIdeles K ≤ sIdeleClassSubgroup S :=
  le_sup_left

/-- The `S`-idèle class group as a quotient of the idèle class group. -/
def ofIdeleClasses : IdeleClasses K →* SIdeleClassGroup S :=
  QuotientGroup.map _ _ (MonoidHom.id _) (principalIdeles_le S)

/-- The map from the idèle class group on classes of idèles. -/
theorem ofIdeleClasses_ideleClassMap (x : Ideles K) :
    ofIdeleClasses S (ideleClassMap K x) = mk S x :=
  rfl

/-- The map from the idèle class group is surjective. -/
theorem ofIdeleClasses_surjective : Function.Surjective (ofIdeleClasses S) := fun y => by
  obtain ⟨x, rfl⟩ := mk_surjective S y
  exact ⟨ideleClassMap K x, rfl⟩

/-- Two homomorphisms out of the `S`-idèle class group that agree on classes of idèles are
equal. -/
theorem hom_ext {G : Type*} [Monoid G] {f g : SIdeleClassGroup S →* G}
    (h : ∀ x : Ideles K, f (mk S x) = g (mk S x)) : f = g :=
  QuotientGroup.monoidHom_ext _ (MonoidHom.ext h)

end SIdeleClassGroup

namespace NarrowSIdeleClassGroup

variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The class of an idèle in the narrow `S`-idèle class group. -/
def mk : Ideles K →* NarrowSIdeleClassGroup S :=
  QuotientGroup.mk' _

/-- Every class is the class of an idèle. -/
theorem mk_surjective : Function.Surjective (mk S) :=
  QuotientGroup.mk'_surjective _

/-- The kernel of the class map. -/
theorem ker_mk : (mk S).ker = narrowSIdeleClassSubgroup S :=
  QuotientGroup.ker_mk' _

/-- An idèle has trivial class exactly when it lies in the subgroup divided out. -/
theorem mk_eq_one_iff {x : Ideles K} : mk S x = 1 ↔ x ∈ narrowSIdeleClassSubgroup S :=
  QuotientGroup.eq_one_iff _

/-- Principal idèles have trivial class. -/
theorem mk_diagonalUnits (a : Kˣ) : mk S (diagonalUnits K a) = 1 :=
  (mk_eq_one_iff S).2 (Subgroup.mem_sup_left ⟨a, rfl⟩)

variable {S} in
/-- The idèles of the unit subgroup have trivial class. -/
theorem mk_eq_one_of_mem {x : Ideles K} (hx : x ∈ positiveUnitIdelesOutside S) : mk S x = 1 :=
  (mk_eq_one_iff S).2 (Subgroup.mem_sup_right hx)

/-- The principal idèles lie in the subgroup divided out. -/
theorem principalIdeles_le : principalIdeles K ≤ narrowSIdeleClassSubgroup S :=
  le_sup_left

/-- The narrow `S`-idèle class group as a quotient of the idèle class group. -/
def ofIdeleClasses : IdeleClasses K →* NarrowSIdeleClassGroup S :=
  QuotientGroup.map _ _ (MonoidHom.id _) (principalIdeles_le S)

/-- The map from the idèle class group on classes of idèles. -/
theorem ofIdeleClasses_ideleClassMap (x : Ideles K) :
    ofIdeleClasses S (ideleClassMap K x) = mk S x :=
  rfl

/-- The map from the idèle class group is surjective. -/
theorem ofIdeleClasses_surjective : Function.Surjective (ofIdeleClasses S) := fun y => by
  obtain ⟨x, rfl⟩ := mk_surjective S y
  exact ⟨ideleClassMap K x, rfl⟩

/-- Two homomorphisms out of the narrow `S`-idèle class group that agree on classes of idèles
are equal. -/
theorem hom_ext {G : Type*} [Monoid G] {f g : NarrowSIdeleClassGroup S →* G}
    (h : ∀ x : Ideles K, f (mk S x) = g (mk S x)) : f = g :=
  QuotientGroup.monoidHom_ext _ (MonoidHom.ext h)

/-- The `S`-idèle class group as a quotient of the narrow one. -/
def toSIdeleClassGroup : NarrowSIdeleClassGroup S →* SIdeleClassGroup S :=
  QuotientGroup.map _ _ (MonoidHom.id _) (narrowSIdeleClassSubgroup_le S)

/-- The surjection to `SIdeleClassGroup S` on classes of idèles. -/
theorem toSIdeleClassGroup_mk (x : Ideles K) :
    toSIdeleClassGroup S (mk S x) = SIdeleClassGroup.mk S x :=
  rfl

/-- The map to `SIdeleClassGroup S` is surjective. -/
theorem toSIdeleClassGroup_surjective : Function.Surjective (toSIdeleClassGroup S) := fun y => by
  obtain ⟨x, rfl⟩ := SIdeleClassGroup.mk_surjective S y
  exact ⟨mk S x, rfl⟩

end NarrowSIdeleClassGroup

end Quotients

section Roots

omit [NumberField K] in
/-- For `n ≠ 0`, a unit of the completion at an archimedean place `w`, positive if `w` is real,
is an `n`-th power. -/
theorem exists_pow_eq_of_pos {w : InfinitePlace K} {n : ℕ} (hn : n ≠ 0)
    (a : (InfiniteCompletion K w)ˣ)
    (ha : ∀ hw : w.IsReal,
      0 < NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
        (a : InfiniteCompletion K w)) :
    ∃ b : (InfiniteCompletion K w)ˣ, b ^ n = a := by
  by_cases hw : w.IsReal
  · let φ := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have hpos : 0 < φ (a : InfiniteCompletion K w) := ha hw
    have hs : φ.symm (φ (a : InfiniteCompletion K w) ^ ((n : ℝ)⁻¹)) ≠ 0 := by
      simp [(Real.rpow_pos_of_pos hpos _).ne']
    refine ⟨Units.mk0 _ hs, ?_⟩
    apply Units.ext
    apply φ.injective
    simp [Real.rpow_inv_natCast_pow hpos.le hn]
  · have htop := Langlands.ClassFieldTheory.Global.infiniteUnitPowers_eq_top_of_isComplex w
      (NumberField.InfinitePlace.not_isReal_iff_isComplex.1 hw) n hn
    exact (Langlands.ClassFieldTheory.Global.mem_infiniteUnitPowers_iff w n a).1
      (htop ▸ Subgroup.mem_top a)

/-- For `n ≠ 0`, an archimedean idèle that is positive at every real place is the `n`-th power of
an archimedean idèle. -/
theorem exists_pow_eq_of_infiniteIdelesInclusion_mem {n : ℕ} (hn : n ≠ 0)
    (z : (InfiniteAdeles K)ˣ) (hz : infiniteIdelesInclusion K z ∈ positiveIdeles K) :
    ∃ y : (InfiniteAdeles K)ˣ, y ^ n = z := by
  choose b hb using fun w => exists_pow_eq_of_pos hn (ContinuousMulEquiv.piUnits z w) (hz w)
  refine ⟨ContinuousMulEquiv.piUnits.symm b, ContinuousMulEquiv.piUnits.injective ?_⟩
  rw [map_pow, ContinuousMulEquiv.apply_symm_apply]
  funext w
  rw [Pi.pow_apply, hb w]

end Roots

section Closure

open Langlands.Global.HeckeFunctionalEquation Langlands.Global.IdeleDensity

open Classical in
/-- An idèle of integral units that is `1` on `S` lies in every closed subgroup of the idèles that
contains the integral local units at all finite places outside `S`. -/
theorem integralUnitIdeles_mem_of_isClosed {H : Subgroup (Ideles K)}
    (hH : IsClosed (H : Set (Ideles K))) {S : Set (HeightOneSpectrum (𝓞 K))}
    (hloc : ∀ v ∉ S, ∀ a : (v.adicCompletionIntegers K)ˣ,
      integralUnitIdeles K (Pi.mulSingle v a) ∈ H)
    (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) (hu : ∀ v ∈ S, u v = 1) :
    integralUnitIdeles K u ∈ H := by
  classical
  have hcl : IsClosed ((integralUnitIdeles K) ⁻¹' (H : Set (Ideles K))) :=
    hH.preimage (integralUnitIdeles K).continuous
  have hmem : u ∈ closure ((integralUnitIdeles K) ⁻¹' (H : Set (Ideles K))) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    rw [nhds_pi, Filter.mem_pi'] at hN
    obtain ⟨T, t, ht, hTN⟩ := hN
    let u₁ : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ :=
      ∏ v ∈ T, Pi.mulSingle v (u v)
    have hu₁ : ∀ j, u₁ j = if j ∈ T then u j else 1 := by
      intro j
      simp only [u₁, Finset.prod_apply]
      exact Finset.prod_pi_mulSingle j u T
    refine ⟨u₁, hTN fun j hj => ?_, ?_⟩
    · have hj' : j ∈ T := hj
      simp only [hu₁ j, hj', ↓reduceIte]
      exact mem_of_mem_nhds (ht j)
    · change integralUnitIdeles K u₁ ∈ H
      simp only [u₁, map_prod]
      apply H.prod_mem
      intro v _
      by_cases hvS : v ∈ S
      · rw [hu v hvS, Pi.mulSingle_one, map_one]
        exact H.one_mem
      · exact hloc v hvS _
  rw [hcl.closure_eq] at hmem
  exact hmem

/-- An element of `(Submonoid.ofClass (v.adicCompletionIntegers K)).units` as a unit of the
valuation ring. -/
def integralUnitOfMem {v : FinitePlace K} (a : (FiniteCompletion K v)ˣ)
    (ha : a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    (v.adicCompletionIntegers K)ˣ where
  val := ⟨a, ha.1⟩
  inv := ⟨((a⁻¹ : (FiniteCompletion K v)ˣ) : FiniteCompletion K v), ha.2⟩
  val_inv := Subtype.ext a.mul_inv
  inv_val := Subtype.ext a.inv_mul

/-- An idèle of `unitIdelesOutside S` is its archimedean part times an idèle of integral units
that is `1` on `S`. -/
theorem exists_eq_infiniteIdelesInclusion_mul_integralUnitIdeles {S : Set (HeightOneSpectrum (𝓞 K))}
    {x : Ideles K} (hx : x ∈ unitIdelesOutside S) :
    ∃ u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ, (∀ v ∈ S, u v = 1) ∧
      x = infiniteIdelesInclusion K (ideleProductEquiv K x).1 * integralUnitIdeles K u := by
  classical
  have hmem : ∀ v : FinitePlace K,
      finiteIdeleProjection K v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
    intro v
    by_cases hv : v ∈ S
    · rw [hx.1 v hv]
      exact Subgroup.one_mem _
    · exact hx.2 v hv
  refine ⟨fun v => integralUnitOfMem _ (hmem v), fun v hv => ?_, ?_⟩
  · apply Units.ext
    apply Subtype.ext
    change ((finiteIdeleProjection K v x : (FiniteCompletion K v)ˣ) : FiniteCompletion K v) = 1
    rw [hx.1 v hv, Units.val_one]
  · apply idele_ext
    · rw [map_mul, infPart_infiniteIdelesInclusion, infPart_integralUnitIdeles, mul_one]
      rfl
    · intro v
      rw [map_mul, coord_infiniteIdelesInclusion, coord_integralUnitIdeles, one_mul]
      rfl

/-- A continuous homomorphism from the idèles to a discrete group of exponent dividing `n ≠ 0`
that kills the integral local units at the finite places outside `S` kills
`positiveUnitIdelesOutside S`. -/
theorem positiveUnitIdelesOutside_le_ker {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (Λ : Ideles K →ₜ* G) {n : ℕ} (hn : n ≠ 0) (hG : ∀ g : G, g ^ n = 1)
    {S : Set (HeightOneSpectrum (𝓞 K))}
    (hloc : ∀ v ∉ S, ∀ a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units,
      Λ (finiteIdeleInclusion K v a) = 1) :
    positiveUnitIdelesOutside S ≤ (Λ : Ideles K →* G).ker := by
  intro x hx
  obtain ⟨hxU, hxpos⟩ := mem_positiveUnitIdelesOutside.1 hx
  obtain ⟨u, hu, hxu⟩ := exists_eq_infiniteIdelesInclusion_mul_integralUnitIdeles hxU
  have hinf : infiniteIdelesInclusion K (ideleProductEquiv K x).1 ∈ positiveIdeles K :=
    fun w hw => hxpos w hw
  obtain ⟨y, hy⟩ := exists_pow_eq_of_infiniteIdelesInclusion_mem hn _ hinf
  have hH : IsClosed (((Λ : Ideles K →* G).ker : Subgroup (Ideles K)) : Set (Ideles K)) := by
    rw [MonoidHom.coe_ker]
    exact (isClosed_discrete {1}).preimage Λ.continuous
  have hint : integralUnitIdeles K u ∈ (Λ : Ideles K →* G).ker := by
    refine integralUnitIdeles_mem_of_isClosed hH (fun v hv a => ?_) u hu
    erw [integralUnitIdeles_mulSingle]
    rw [MonoidHom.mem_ker]
    exact hloc v hv _
      ⟨(a : v.adicCompletionIntegers K).2, (a⁻¹ : (v.adicCompletionIntegers K)ˣ).val.2⟩
  rw [MonoidHom.mem_ker] at hint ⊢
  rw [hxu, map_mul, ← hy, map_pow, map_pow, hG, one_mul]
  exact hint

end Closure

section Openness

open Langlands.Global.Arithmetic

/-- An archimedean component of the idèle with prescribed archimedean part and components in the
local factors of `SUnitIdeleTopology.model`. -/
theorem infiniteIdeleProjection_assemble (T : Finset (HeightOneSpectrum (𝓞 K)))
    (m : SUnitIdeleTopology.model K T) (w : InfinitePlace K) :
    infiniteIdeleProjection K w (SUnitIdeleTopology.assemble K T m) =
      ContinuousMulEquiv.piUnits m.1 w :=
  rfl

/-- For finite `S` and `n ≠ 0`, a subgroup of the idèles that contains every `n`-th power and
`positiveUnitIdelesOutside S` is open: it contains the open set of the idèles that are units at
the finite places outside `S` and `n`-th powers at the places of `S` and at the archimedean
places. -/
theorem isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) {n : ℕ} (hn : n ≠ 0) (N : Subgroup (Ideles K))
    (hpow : ∀ x : Ideles K, x ^ n ∈ N) (hU : positiveUnitIdelesOutside S ≤ N) :
    IsOpen (N : Set (Ideles K)) := by
  classical
  set T := hS.toFinset with hT
  have hmemT : ∀ v, v ∈ T ↔ v ∈ S := fun v => hS.mem_toFinset
  let W : Set (Ideles K) := (IdeleSUnits.sUnitIdeles K T : Set (Ideles K)) ∩
    ((⋂ v ∈ S, (finiteIdeleProjection K v) ⁻¹'
        (((powMonoidHom n : (FiniteCompletion K v)ˣ →* (FiniteCompletion K v)ˣ).range :
          Subgroup (FiniteCompletion K v)ˣ) : Set (FiniteCompletion K v)ˣ)) ∩
      (fun x => ContinuousMulEquiv.piUnits (ideleProductEquiv K x).1) ⁻¹'
        Set.univ.pi fun w =>
          (((powMonoidHom n : (InfiniteCompletion K w)ˣ →* (InfiniteCompletion K w)ˣ).range :
            Subgroup (InfiniteCompletion K w)ˣ) : Set (InfiniteCompletion K w)ˣ))
  have hWo : IsOpen W := by
    refine (SUnitIdeleTopology.isOpen_sUnitIdeles K T).inter (IsOpen.inter ?_ ?_)
    · exact hS.isOpen_biInter fun v _ =>
        (SUnitIdelePowerQuotient.isOpen_finite_powers v n hn).preimage
          (finiteIdeleProjection K v).continuous
    · exact (isOpen_set_pi Set.finite_univ fun w _ =>
        SUnitIdelePowerQuotient.isOpen_infinite_powers w n hn).preimage
          (ContinuousMulEquiv.piUnits.continuous.comp
            (continuous_fst.comp (ideleProductEquiv K).continuous))
  have h1W : (1 : Ideles K) ∈ W := by
    refine ⟨Subgroup.one_mem _, ?_, fun w _ => ?_⟩
    · exact Set.mem_iInter₂.2 fun v _ => by
        rw [Set.mem_preimage, map_one]
        exact Subgroup.one_mem _
    · change ContinuousMulEquiv.piUnits (ideleProductEquiv K 1).1 w ∈ _
      rw [map_one, Prod.fst_one, map_one]
      exact Subgroup.one_mem _
  refine N.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hWo.mem_nhds h1W) ?_)
  rintro x ⟨hxT, hxS, hxinf⟩
  have hxS' : ∀ v ∈ S, ∃ b : (FiniteCompletion K v)ˣ, b ^ n = finiteIdeleProjection K v x :=
    fun v hv => Set.mem_iInter₂.1 hxS v hv
  have hxinf' : ∀ w : InfinitePlace K, ∃ b : (InfiniteCompletion K w)ˣ,
      b ^ n = ContinuousMulEquiv.piUnits (ideleProductEquiv K x).1 w :=
    fun w => hxinf w (Set.mem_univ w)
  choose b hb using hxinf'
  let g : ∀ v : FinitePlace K, SUnitIdeleTopology.localFactor K T v := fun v =>
    if h : v ∈ S then ⟨Classical.choose (hxS' v h), by
      simp [SUnitIdeleTopology.localFactor, (hmemT v).2 h]⟩ else 1
  have hg : ∀ v (h : v ∈ S), ((g v : (FiniteCompletion K v)ˣ)) ^ n = finiteIdeleProjection K v x :=
    fun v h => by
      simp only [g, h, ↓reduceDIte]
      exact Classical.choose_spec (hxS' v h)
  have hg' : ∀ v, v ∉ S → (g v : (FiniteCompletion K v)ˣ) = 1 := fun v h => by
    simp only [g, h, ↓reduceDIte]
    rfl
  let y : Ideles K := SUnitIdeleTopology.assemble K T (ContinuousMulEquiv.piUnits.symm b, g)
  have hz : x * (y ^ n)⁻¹ ∈ positiveUnitIdelesOutside S := by
    refine mem_positiveUnitIdelesOutside.2 ⟨⟨fun v hv => ?_, fun v hv => ?_⟩, fun w hw => ?_⟩
    · rw [map_mul, map_inv, map_pow, SUnitIdeleTopology.finiteIdeleProjection_assemble, hg v hv,
        mul_inv_cancel]
    · rw [map_mul, map_inv, map_pow, SUnitIdeleTopology.finiteIdeleProjection_assemble, hg' v hv,
        one_pow, inv_one, mul_one]
      apply (mem_units_iff_valued_eq_one _).2
      have := IdeleSUnits.mem_sUnitIdeles_iff.1 hxT v ((hmemT v).not.2 hv)
      exact (IdeleSUnits.ideleExponent_eq_one_iff v x).1 this
    · rw [map_mul, map_inv, map_pow, infiniteIdeleProjection_assemble,
        ContinuousMulEquiv.apply_symm_apply, hb w]
      change 0 < NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
        (((ContinuousMulEquiv.piUnits (ideleProductEquiv K x).1 w *
          (ContinuousMulEquiv.piUnits (ideleProductEquiv K x).1 w)⁻¹ :
            (InfiniteCompletion K w)ˣ)) : InfiniteCompletion K w)
      rw [mul_inv_cancel, Units.val_one, map_one]
      exact one_pos
  have hx : x = x * (y ^ n)⁻¹ * y ^ n := by group
  rw [SetLike.mem_coe, hx]
  exact N.mul_mem (hU hz) (hpow y)

end Openness

section Parity

/-- In a group in which `g ^ n = 1` for every `g`, with `n` odd, an element of order dividing `2`
is `1`. -/
theorem eq_one_of_sq_eq_one_of_odd {G : Type*} [Group G] {n : ℕ} (hn : Odd n) {g : G}
    (h2 : g ^ 2 = 1) (hg : g ^ n = 1) : g = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rwa [pow_succ, pow_mul, h2, one_pow, one_mul] at hg

/-- Every element of `ℤ/n`, written multiplicatively, has order dividing `n`. -/
theorem zmod_pow_eq_one {n : ℕ} (z : Multiplicative (ZMod n)) : z ^ n = 1 := by
  change Multiplicative.ofAdd (n • Multiplicative.toAdd z) = Multiplicative.ofAdd 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

namespace NarrowSIdeleClassGroup

variable (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ)

/-- Precomposition with `toSIdeleClassGroup S`, on homomorphisms to `ℤ/n`. -/
def precompToSIdeleClassGroup :
    (SIdeleClassGroup S →* Multiplicative (ZMod n)) →*
      (NarrowSIdeleClassGroup S →* Multiplicative (ZMod n)) :=
  MonoidHom.compHom' (toSIdeleClassGroup S)

/-- Precomposition on classes of idèles. -/
theorem precompToSIdeleClassGroup_apply_mk (f : SIdeleClassGroup S →* Multiplicative (ZMod n))
    (x : Ideles K) :
    precompToSIdeleClassGroup S n f (mk S x) = f (SIdeleClassGroup.mk S x) :=
  rfl

/-- Precomposition with the surjection `toSIdeleClassGroup S` is injective. -/
theorem precompToSIdeleClassGroup_injective :
    Function.Injective (precompToSIdeleClassGroup S n) := fun _ _ h =>
  (MonoidHom.cancel_right (toSIdeleClassGroup_surjective S)).1 h

/-- If `n` is odd or `K` has no real place, every homomorphism from the narrow `S`-idèle class
group to `ℤ/n` factors through the `S`-idèle class group: it kills the image of
`unitIdelesOutside S`, whose squares lie in `positiveUnitIdelesOutside S`. -/
theorem precompToSIdeleClassGroup_surjective (h : Odd n ∨ NumberField.IsTotallyComplex K) :
    Function.Surjective (precompToSIdeleClassGroup S n) := by
  intro ψ
  have hle : sIdeleClassSubgroup S ≤ (ψ.comp (mk S)).ker := by
    refine sup_le ?_ fun u hu => ?_
    · rintro _ ⟨a, rfl⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, mk_diagonalUnits, map_one]
    · rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      rcases h with hn | hK
      · refine eq_one_of_sq_eq_one_of_odd hn ?_ (zmod_pow_eq_one _)
        rw [← map_pow, ← map_pow, mk_eq_one_of_mem (sq_mem_positiveUnitIdelesOutside hu),
          map_one]
      · rw [mk_eq_one_of_mem (by rwa [positiveUnitIdelesOutside_eq]), map_one]
  exact ⟨QuotientGroup.lift _ _ hle, hom_ext S fun _ => rfl⟩

/-- If `n` is odd or `K` has no real place, homomorphisms from the `S`-idèle class group to `ℤ/n`
are the homomorphisms from the narrow `S`-idèle class group, by precomposition with
`toSIdeleClassGroup S`. -/
def precompToSIdeleClassGroupEquiv (h : Odd n ∨ NumberField.IsTotallyComplex K) :
    (SIdeleClassGroup S →* Multiplicative (ZMod n)) ≃*
      (NarrowSIdeleClassGroup S →* Multiplicative (ZMod n)) :=
  MulEquiv.ofBijective (precompToSIdeleClassGroup S n)
    ⟨precompToSIdeleClassGroup_injective S n, precompToSIdeleClassGroup_surjective S n h⟩

/-- The isomorphism `precompToSIdeleClassGroupEquiv` is precomposition. -/
theorem precompToSIdeleClassGroupEquiv_apply (h : Odd n ∨ NumberField.IsTotallyComplex K)
    (f : SIdeleClassGroup S →* Multiplicative (ZMod n)) :
    precompToSIdeleClassGroupEquiv S n h f = precompToSIdeleClassGroup S n f :=
  rfl

end NarrowSIdeleClassGroup

end Parity

end Langlands.GaloisCohomology

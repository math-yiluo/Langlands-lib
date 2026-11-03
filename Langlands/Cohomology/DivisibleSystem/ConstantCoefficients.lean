import Langlands.Cohomology.DivisibleSystem.PermutationProjective
import Langlands.Cohomology.DivisibleSystem.ReductionAdic
import Langlands.Cohomology.DivisibleSystem.Resolution
import Langlands.Cohomology.DivisibleSystem.SmoothLocallyConstant
import Langlands.Cohomology.DivisibleSystem.StandardResolution
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RepresentationTheory.Coinvariants

/-!
# Constant coefficient systems

The constant `ℓ`-divisible systems `{R / ℓ ^ m R}`, with trivial group actions, and their
realizations as smooth locally constant sheaves. For `R = ℤ` the levels are `ℤ / ℓ ^ m ℤ`, the
coefficients of the constant sheaves resolved in Harris's Lemma 2.2.

* `scalarSystem R ℓ hℓ` is the published `reductionSystem ℓ R` of the `R`-module `R`, for `ℓ` a
  non-zero-divisor of `R` (`hℓ`). `scalarSystemObjIso` identifies level `m` with
  `R ⧸ Ideal.span {ℓ ^ m}`; under it `j` is the reduction and `i` is multiplication by
  `ℓ ^ (m - m')`. `intSystem ℓ hℓ` is the case `R = ℤ`, `ℓ ≠ 0`, with levels `ZMod (ℓ ^ m)`.
* `trivialRepSystem hℓ Γ` and `smoothTrivialSystem hℓ G` give these modules the trivial action
  of a group `Γ`, resp. the trivial smooth action of a topological group `G`;
  `trivialStandardResolutionSystem hℓ Γ` is the published system of standard resolutions along
  `Ind_1^Γ Res_1^Γ` for finite `Γ`, and `smoothTrivialSystemRestrictionIso` restricts the smooth
  system to a subgroup.
* `constantSheafSystem hℓ G X` is the system of locally constant sheaves of
  `smoothTrivialSystem hℓ G` on a `G`-space `X`; `constantGodementResolutionSystem` is the
  published system of smooth Godement resolutions of its levels, under the hypothesis
  `SmoothGodementZeroExactStatement R G X`. `constantSheafSystemRestrictIso` and
  `constantSheafSystemInduceIso` compare the constant systems on `G ×ᴴ X` and on `X` under the
  published equivalence `smoothRestrictionSystemEquivalence`.
* `intTrivialRepSystem` and `intConstantSheafSystem` are the cases `R = ℤ`, with level
  isomorphisms to `ZMod (ℓ ^ m)`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Langlands.Cohomology

section Regular

/-- In a domain of characteristic zero, a nonzero natural number is a non-zero-divisor. -/
lemma isSMulRegular_natCast {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) : IsSMulRegular R (ℓ : R) :=
  fun a b h => mul_left_cancel₀ (Nat.cast_ne_zero.2 hℓ) (by simpa only [smul_eq_mul] using h)

variable (R : Type u) [CommRing R] (ℓ : ℕ)

/-- Multiplication by `ℓ` is a monomorphism on `R` if `ℓ` is a non-zero-divisor of `R`. -/
lemma mono_powSMul_one_self (hℓ : IsSMulRegular R (ℓ : R)) :
    Mono (powSMul ℓ 1 (ModuleCat.of R R)) :=
  (ModuleCat.mono_iff_injective _).2 fun a b h => hℓ (by
    have h' : (powSMul ℓ 1 (ModuleCat.of R R)).hom a = (powSMul ℓ 1 (ModuleCat.of R R)).hom b := h
    rwa [DivisibleSystem.powSMul_moduleCat_hom_apply, DivisibleSystem.powSMul_moduleCat_hom_apply,
      pow_one] at h')

end Regular

section TrivialFunctor

variable (R : Type u) [CommRing R] (Γ : Type u) [Group Γ]

/-- The trivial-representation functor is a right adjoint, so it preserves limits. -/
instance repTrivialFunctor_preservesLimits : PreservesLimits (Rep.trivialFunctor.{u} R Γ) :=
  (Rep.coinvariantsAdjunction R Γ).rightAdjoint_preservesLimits

/-- The trivial-representation functor is a left adjoint, so it preserves colimits. -/
instance repTrivialFunctor_preservesColimits : PreservesColimits (Rep.trivialFunctor.{u} R Γ) :=
  (Rep.invariantsAdjunction R Γ).leftAdjoint_preservesColimits

/-- The trivial-representation functor is additive. -/
instance repTrivialFunctor_additive : (Rep.trivialFunctor.{u} R Γ).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The trivial smooth representation functor is a left adjoint, so it preserves colimits. -/
instance smoothTrivialFunctor_preservesColimits :
    PreservesColimits (smoothTrivialFunctor.{u, u, u} R G) :=
  (smoothTrivialAdjunction R G).leftAdjoint_preservesColimits

/-- The trivial smooth representation functor preserves finite limits, since its composite with
the forgetful functor to representations is the trivial-representation functor. -/
instance smoothTrivialFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (smoothTrivialFunctor.{u, u, u} R G) := by
  have : PreservesFiniteLimits (smoothTrivialFunctor.{u, u, u} R G ⋙ SmoothRep.toRep) :=
    inferInstanceAs (PreservesFiniteLimits (Rep.trivialFunctor.{u} R G))
  exact preservesFiniteLimits_of_reflects_of_preserves _ SmoothRep.toRep

/-- The trivial smooth representation functor is additive. -/
instance smoothTrivialFunctor_additive : (smoothTrivialFunctor.{u, u, u} R G).Additive :=
  Functor.additive_of_preserves_binary_products _

end TrivialFunctor

namespace DivisibleSystem

section Scalar

variable (R : Type u) [CommRing R] (ℓ : ℕ)

/-- The image of multiplication by `ℓ ^ m` on `R` is the ideal `(ℓ ^ m)`. -/
lemma range_powSMul_self (m : ℕ) :
    LinearMap.range (powSMul ℓ m (ModuleCat.of R R)).hom = Ideal.span {(ℓ : R) ^ m} := by
  ext x
  rw [LinearMap.mem_range, Ideal.mem_span_singleton']
  refine exists_congr fun y => ?_
  rw [powSMul_moduleCat_hom_apply, smul_eq_mul, mul_comm]

/-- The `ℓ`-divisible system `{R / ℓ ^ m R}` of `R`-modules, for `ℓ` a non-zero-divisor of
`R`. -/
def scalarSystem (hℓ : IsSMulRegular R (ℓ : R)) : DivisibleSystem (ModuleCat.{u} R) ℓ :=
  haveI := mono_powSMul_one_self R ℓ hℓ
  reductionSystem ℓ (ModuleCat.of R R)

variable {R ℓ} (hℓ : IsSMulRegular R (ℓ : R))

/-- The tower of `scalarSystem` is the reduction tower of `R`. -/
@[simp]
lemma scalarSystem_tower : (scalarSystem R ℓ hℓ).tower = reductionTower ℓ (ModuleCat.of R R) :=
  rfl

/-- The maps `i` of `scalarSystem` are the maps `reductionInclusion`. -/
lemma scalarSystem_inclusion {m' m : ℕ} (h : m' < m) :
    (scalarSystem R ℓ hℓ).inclusion h = reductionInclusion ℓ (ModuleCat.of R R) h :=
  rfl

/-- The reduction map `R ⟶ R / ℓ ^ m R` onto level `m` of `scalarSystem`. -/
def scalarπ (m : ℕ) : ModuleCat.of R R ⟶ (scalarSystem R ℓ hℓ).obj m :=
  reductionπ ℓ (ModuleCat.of R R) m

/-- The reduction map onto a level of `scalarSystem` is an epimorphism. -/
instance (m : ℕ) : Epi (scalarπ hℓ m) :=
  inferInstanceAs (Epi (reductionπ ℓ (ModuleCat.of R R) m))

/-- The maps `j` of `scalarSystem` commute with the reduction maps from `R`. -/
@[reassoc (attr := simp)]
lemma scalarπ_projection {m' m : ℕ} (h : m' ≤ m) :
    scalarπ hℓ m ≫ (scalarSystem R ℓ hℓ).projection h = scalarπ hℓ m' :=
  reductionπ_map ℓ (ModuleCat.of R R) (homOfLE h).op

/-- The map `i` sends the class of `r` to the class of `ℓ ^ (m - m') r`. -/
@[reassoc]
lemma scalarπ_inclusion {m' m : ℕ} (h : m' < m) :
    scalarπ hℓ m' ≫ (scalarSystem R ℓ hℓ).inclusion h =
      powSMul ℓ (m - m') (ModuleCat.of R R) ≫ scalarπ hℓ m :=
  reductionπ_inclusion ℓ (ModuleCat.of R R) h

/-- Level `m` of `scalarSystem` is the `R`-module `R / ℓ ^ m R`. -/
def scalarSystemObjIso (m : ℕ) :
    (scalarSystem R ℓ hℓ).obj m ≅ ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}) :=
  ModuleCat.cokernelIsoRangeQuotient (powSMul ℓ m (ModuleCat.of R R)) ≪≫
    (Submodule.quotEquivOfEq _ _ (range_powSMul_self R ℓ m)).toModuleIso

/-- `scalarSystemObjIso` sends the class of `r` to the class of `r`. -/
@[reassoc (attr := simp)]
lemma scalarπ_scalarSystemObjIso_hom (m : ℕ) :
    scalarπ hℓ m ≫ (scalarSystemObjIso hℓ m).hom =
      ModuleCat.ofHom (Ideal.span {(ℓ : R) ^ m}).mkQ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change (Submodule.quotEquivOfEq _ _ (range_powSMul_self R ℓ m))
    ((ModuleCat.cokernelIsoRangeQuotient (powSMul ℓ m (ModuleCat.of R R))).hom
      ((cokernel.π (powSMul ℓ m (ModuleCat.of R R))).hom x)) = Submodule.Quotient.mk x
  rw [ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply]
  rfl

variable (R ℓ) in
/-- For `m' ≤ m`, the ideal `(ℓ ^ m)` is contained in `(ℓ ^ m')`. -/
lemma span_pow_le_span_pow {m' m : ℕ} (h : m' ≤ m) :
    Ideal.span {(ℓ : R) ^ m} ≤ Ideal.span {(ℓ : R) ^ m'} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)

variable (R ℓ) in
/-- For `m' ≤ m`, multiplication by `ℓ ^ (m - m')` maps the ideal `(ℓ ^ m')` into `(ℓ ^ m)`. -/
lemma span_pow_le_comap_mulLeft {m' m : ℕ} (h : m' ≤ m) :
    Ideal.span {(ℓ : R) ^ m'} ≤
      Submodule.comap (LinearMap.mulLeft R ((ℓ : R) ^ (m - m'))) (Ideal.span {(ℓ : R) ^ m}) := by
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_left_comm, ← pow_add,
    Nat.sub_add_cancel h]
  exact Ideal.mem_span_singleton'.2 ⟨y, rfl⟩

/-- Under `scalarSystemObjIso`, the maps `j` of `scalarSystem` are the reductions
`R / ℓ ^ m R ⟶ R / ℓ ^ m' R`. -/
@[reassoc]
lemma projection_scalarSystemObjIso_hom {m' m : ℕ} (h : m' ≤ m) :
    (scalarSystem R ℓ hℓ).projection h ≫ (scalarSystemObjIso hℓ m').hom =
      (scalarSystemObjIso hℓ m).hom ≫
        ModuleCat.ofHom (Submodule.factor (span_pow_le_span_pow R ℓ h)) := by
  rw [← cancel_epi (scalarπ hℓ m), scalarπ_projection_assoc, scalarπ_scalarSystemObjIso_hom,
    scalarπ_scalarSystemObjIso_hom_assoc]
  exact ModuleCat.hom_ext (LinearMap.ext fun x => rfl)

/-- Under `scalarSystemObjIso`, the maps `i` of `scalarSystem` are multiplication by
`ℓ ^ (m - m')`, `R / ℓ ^ m' R ⟶ R / ℓ ^ m R`. -/
@[reassoc]
lemma inclusion_scalarSystemObjIso_hom {m' m : ℕ} (h : m' < m) :
    (scalarSystem R ℓ hℓ).inclusion h ≫ (scalarSystemObjIso hℓ m).hom =
      (scalarSystemObjIso hℓ m').hom ≫
        ModuleCat.ofHom (Submodule.mapQ _ _ (LinearMap.mulLeft R ((ℓ : R) ^ (m - m')))
          (span_pow_le_comap_mulLeft R ℓ h.le)) := by
  rw [← cancel_epi (scalarπ hℓ m'), scalarπ_inclusion_assoc, scalarπ_scalarSystemObjIso_hom,
    scalarπ_scalarSystemObjIso_hom_assoc]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change Submodule.Quotient.mk ((powSMul ℓ (m - m') (ModuleCat.of R R)).hom x) =
    Submodule.Quotient.mk ((ℓ : R) ^ (m - m') * x)
  rw [powSMul_moduleCat_hom_apply, smul_eq_mul]

end Scalar

section Int

variable (ℓ : ℕ) (hℓ : ℓ ≠ 0)

/-- The `ℓ`-divisible system `{ℤ / ℓ ^ m ℤ}` of abelian groups, for `ℓ ≠ 0`. -/
abbrev intSystem : DivisibleSystem (ModuleCat.{0} ℤ) ℓ :=
  scalarSystem ℤ ℓ (isSMulRegular_natCast hℓ)

/-- Level `m` of `intSystem` is `ZMod (ℓ ^ m)`. -/
def intSystemObjIso (m : ℕ) : (intSystem ℓ hℓ).obj m ≅ ModuleCat.of ℤ (ZMod (ℓ ^ m)) :=
  scalarSystemObjIso _ m ≪≫
    ((Ideal.quotEquivOfEq (by rw [Nat.cast_pow])).trans
      (Int.quotientSpanNatEquivZMod (ℓ ^ m))).toAddEquiv.toIntLinearEquiv.toModuleIso

/-- `intSystemObjIso` sends the class of an integer `n` to `n : ZMod (ℓ ^ m)`. -/
@[reassoc (attr := simp)]
lemma scalarπ_intSystemObjIso_hom (m : ℕ) :
    scalarπ (isSMulRegular_natCast hℓ) m ≫ (intSystemObjIso ℓ hℓ m).hom =
      ModuleCat.ofHom (Int.castAddHom (ZMod (ℓ ^ m))).toIntLinearMap := by
  rw [intSystemObjIso, Iso.trans_hom, scalarπ_scalarSystemObjIso_hom_assoc]
  exact ModuleCat.hom_ext (LinearMap.ext fun x => rfl)

end Int

section TrivialRep

variable {R : Type u} [CommRing R] {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R)) (Γ : Type u) [Group Γ]

/-- The `ℓ`-divisible system `{R / ℓ ^ m R}` with the trivial action of a group `Γ`. -/
def trivialRepSystem : DivisibleSystem (Rep.{u} R Γ) ℓ :=
  (scalarSystem R ℓ hℓ).map (Rep.trivialFunctor R Γ)

/-- Level `m` of `trivialRepSystem` is `R / ℓ ^ m R` with the trivial action of `Γ`. -/
def trivialRepSystemObjIso (m : ℕ) :
    (trivialRepSystem hℓ Γ).obj m ≅ Rep.trivial R Γ (R ⧸ Ideal.span {(ℓ : R) ^ m}) :=
  (Rep.trivialFunctor R Γ).mapIso (scalarSystemObjIso hℓ m)

/-- The standard resolutions along `Ind_1^Γ Res_1^Γ` of the levels of `trivialRepSystem`, for a
finite group `Γ`. -/
abbrev trivialStandardResolutionSystem [Finite Γ] :
    DivisibleSystem (ChainComplex (Rep.{u} R Γ) ℕ) ℓ :=
  groupStandardResolutionSystem.{u, u, u} (trivialRepSystem hℓ Γ)

end TrivialRep

section SmoothTrivial

variable {R : Type u} [CommRing R] {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
  (G : Type u) [Group G] [TopologicalSpace G]

/-- The `ℓ`-divisible system `{R / ℓ ^ m R}` with the trivial smooth action of `G`. -/
def smoothTrivialSystem : DivisibleSystem (SmoothRep.{u, u, u} R G) ℓ :=
  (scalarSystem R ℓ hℓ).map (smoothTrivialFunctor.{u, u, u} R G)

/-- Level `m` of `smoothTrivialSystem` is `R / ℓ ^ m R` with the trivial smooth action of `G`. -/
def smoothTrivialSystemObjIso (m : ℕ) :
    (smoothTrivialSystem hℓ G).obj m ≅
      (smoothTrivialFunctor.{u, u, u} R G).obj (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})) :=
  (smoothTrivialFunctor.{u, u, u} R G).mapIso (scalarSystemObjIso hℓ m)

variable (R) {G} [IsTopologicalGroup G] (H : Subgroup G)

/-- The restriction to a subgroup `H` of a trivial smooth representation of `G` is the trivial
smooth representation of `H`. -/
def smoothTrivialRestrictionIso :
    smoothTrivialFunctor.{u, u, u} R G ⋙ Langlands.Induction.smoothRestriction.{u, u, u} R H ≅
      smoothTrivialFunctor.{u, u, u} R H :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    simp only [Iso.refl_hom]
    rfl)

variable {R}

/-- The restriction of `smoothTrivialSystem` of `G` to a subgroup `H` is `smoothTrivialSystem`
of `H`. -/
def smoothTrivialSystemRestrictionIso :
    (smoothRestrictionSystemFunctor R ℓ H).obj (smoothTrivialSystem hℓ G) ≅
      smoothTrivialSystem hℓ H :=
  (mapFunctorCompIso ℓ _ _ _ (smoothTrivialRestrictionIso R H)).app (scalarSystem R ℓ hℓ)

end SmoothTrivial

section ConstantSheaf

open Langlands.Sheaf.Equivariant

variable {R : Type u} [CommRing R] {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X]

/-- The constant `ℓ`-divisible system `{R / ℓ ^ m R}` of `G`-equivariant smooth sheaves on `X`:
the locally constant sheaves of the trivial smooth representations `R / ℓ ^ m R`. -/
def constantSheafSystem : SmoothSheafDivisibleSystem R G X ℓ :=
  (smoothLocallyConstantSystemFunctor R ℓ G X).obj (smoothTrivialSystem hℓ G)

/-- Level `m` of `constantSheafSystem` is the locally constant sheaf of the trivial smooth
representation `R / ℓ ^ m R`. -/
def constantSheafSystemObjIso (m : ℕ) :
    (constantSheafSystem hℓ G X).obj m ≅
      (LocallyConstantSheaf.smoothFunctor R G X).obj
        ((smoothTrivialFunctor.{u, u, u} R G).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) :=
  (LocallyConstantSheaf.smoothFunctor R G X).mapIso (smoothTrivialSystemObjIso hℓ G m)

open Langlands.Sheaf.Equivariant.Godement Langlands.Cohomology.SmoothGodement

/-- The smooth Godement resolutions of the levels of `constantSheafSystem`, given that the
degree-zero smooth Godement functor is exact. -/
abbrev constantGodementResolutionSystem (h : SmoothGodementZeroExactStatement R G X) :
    DivisibleSystem (CochainComplex (SmoothTopologicalSheaf R G X) ℕ) ℓ :=
  smoothGodementResolutionSystem h (constantSheafSystem hℓ G X)

/-- Level `m` of `constantGodementResolutionSystem` is the smooth Godement complex of the
locally constant sheaf of the trivial smooth representation `R / ℓ ^ m R`. -/
def constantGodementResolutionSystemObjIso (h : SmoothGodementZeroExactStatement R G X)
    (m : ℕ) :
    (constantGodementResolutionSystem hℓ G X h).obj m ≅
      smoothComplex R G X ((LocallyConstantSheaf.smoothFunctor R G X).obj
        ((smoothTrivialFunctor.{u, u, u} R G).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})))) :=
  smoothGodementResolutionSystemObjIso h _ m ≪≫
    (smoothComplexFunctor R G X).mapIso (constantSheafSystemObjIso hℓ G X m)

end ConstantSheaf

section SpatialInduction

open Langlands.Sheaf.Equivariant Langlands.TopologicalInduction

variable {R : Type u} [CommRing R] {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
  (hH : IsOpen (H : Set G)) (X : Type u) [TopologicalSpace X] [MulAction H X]
  [ContinuousSMul H X] [HasStableNeighbourhoods H X]

/-- Restricting the constant system on `G ×ᴴ X` to the unit chart gives the constant system
on `X`. -/
def constantSheafSystemRestrictIso :
    letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
    (smoothRestrictionSystemEquivalence R H hH X ℓ).functor.obj
        (constantSheafSystem hℓ G (Space H X)) ≅ constantSheafSystem hℓ H X :=
  letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
  (smoothRestrictLocallyConstantSystemIso R H hH X ℓ).app (smoothTrivialSystem hℓ G) ≪≫
    (smoothLocallyConstantSystemFunctor R ℓ H X).mapIso (smoothTrivialSystemRestrictionIso hℓ H)

/-- Smooth spatial induction of the constant system on `X` is the constant system on
`G ×ᴴ X`. -/
def constantSheafSystemInduceIso :
    letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
    (smoothRestrictionSystemEquivalence R H hH X ℓ).inverse.obj (constantSheafSystem hℓ H X) ≅
      constantSheafSystem hℓ G (Space H X) :=
  letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
  (smoothRestrictionSystemEquivalence R H hH X ℓ).inverse.mapIso
      ((smoothLocallyConstantSystemFunctor R ℓ H X).mapIso
        (smoothTrivialSystemRestrictionIso hℓ H).symm) ≪≫
    (smoothInduceLocallyConstantSystemIso R H hH X ℓ).app (smoothTrivialSystem hℓ G)

end SpatialInduction

section IntCoefficients

open Langlands.Sheaf.Equivariant

variable (ℓ : ℕ) (hℓ : ℓ ≠ 0)

/-- The `ℓ`-divisible system `{ℤ / ℓ ^ m ℤ}` with the trivial action of a group `Γ`. -/
abbrev intTrivialRepSystem (Γ : Type) [Group Γ] : DivisibleSystem (Rep.{0} ℤ Γ) ℓ :=
  trivialRepSystem (isSMulRegular_natCast hℓ) Γ

/-- Level `m` of `intTrivialRepSystem` is `ZMod (ℓ ^ m)` with the trivial action of `Γ`. -/
def intTrivialRepSystemObjIso (Γ : Type) [Group Γ] (m : ℕ) :
    (intTrivialRepSystem ℓ hℓ Γ).obj m ≅ Rep.trivial ℤ Γ (ZMod (ℓ ^ m)) :=
  (Rep.trivialFunctor ℤ Γ).mapIso (intSystemObjIso ℓ hℓ m)

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X]

/-- The constant `ℓ`-divisible system `{ℤ / ℓ ^ m ℤ}` of `G`-equivariant smooth sheaves on
`X`. -/
abbrev intConstantSheafSystem : SmoothSheafDivisibleSystem ℤ G X ℓ :=
  constantSheafSystem (isSMulRegular_natCast hℓ) G X

/-- Level `m` of `intConstantSheafSystem` is the locally constant sheaf of the trivial smooth
representation `ZMod (ℓ ^ m)`. -/
def intConstantSheafSystemObjIso (m : ℕ) :
    (intConstantSheafSystem ℓ hℓ G X).obj m ≅
      (LocallyConstantSheaf.smoothFunctor ℤ G X).obj
        ((smoothTrivialFunctor.{0, 0, 0} ℤ G).obj (ModuleCat.of ℤ (ZMod (ℓ ^ m)))) :=
  (LocallyConstantSheaf.smoothFunctor ℤ G X).mapIso
    ((smoothTrivialFunctor.{0, 0, 0} ℤ G).mapIso (intSystemObjIso ℓ hℓ m))

end IntCoefficients

end DivisibleSystem

end Langlands.Cohomology

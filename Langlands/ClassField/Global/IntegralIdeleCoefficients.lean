import Langlands.ClassField.Global.Cohomology
import Langlands.ClassField.Global.IdeleCoefficientSequence
import Langlands.ClassField.Global.UnitTorsionSequence

/-! # The integral-idele coefficient diagram

For a number field `E` and a field `F` with `Algebra F E`, in independent universes: the
integral ideles `J∞ ⊆ J_E` (every finite coordinate a valuation unit), their image
`C∞ ⊆ C_E` in the idele class group and the quotient `C_E/C∞`, with the actions of
`E ≃ₐ[F] E` restricted from or induced by the published arithmetic actions on `J_E` and
`C_E`; the maps `(𝓞 E)ˣ → J∞ → C∞ → C_E`, `J∞ → J_E → C_E` and `C_E → C_E/C∞` as morphisms
of the additive coefficient representations, and their ordinary group cohomology.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

universe u v

section CoefficientHom

variable {G A B : Type v} [Group G] [CommGroup A] [CommGroup B]
  [MulDistribMulAction G A] [MulDistribMulAction G B]

/-- An equivariant homomorphism of multiplicative coefficient groups, as a morphism of the
additive coefficient representations over the lifted integers. -/
def equivariantCoefficientHom (f : A →* B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    NormalizedTwoCocycle.coefficientRepresentation G A ⟶
      NormalizedTwoCocycle.coefficientRepresentation G B :=
  Rep.ofHom
    { toLinearMap :=
        { toFun x := Additive.ofMul (f (@Additive.toMul A x))
          map_add' x y := congrArg Additive.ofMul
            (map_mul f (@Additive.toMul A x) (@Additive.toMul A y))
          map_smul' r x := congrArg Additive.ofMul (map_zpow f (@Additive.toMul A x) r.down) }
      isIntertwining' g := by
        ext x
        exact congrArg Additive.ofMul (hf g (@Additive.toMul A x)) }

@[simp] theorem equivariantCoefficientHom_apply (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (x : Additive A) :
    (equivariantCoefficientHom f hf).hom x = Additive.ofMul (f x.toMul) := rfl

end CoefficientHom

section Subgroups

variable (E : Type v) [Field E] [NumberField E]

/-- The integral ideles `J∞`: the ideles whose coordinate at every finite place `w` has
valuation one. The coordinates at the infinite places are unrestricted. -/
def integralIdeles : Subgroup (IdeleGroup (𝓞 E) E) where
  carrier := {x | ∀ w : HeightOneSpectrum (𝓞 E),
    Valued.v (ideleCoordinate w x : w.adicCompletion E) = 1}
  mul_mem' {x y} hx hy w := by
    rw [map_mul, Units.val_mul, map_mul, hx w, hy w, one_mul]
  one_mem' w := by
    rw [map_one, Units.val_one, map_one]
  inv_mem' {x} hx w := by
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, hx w, inv_one]

/-- The integral idele classes `C∞`: the image of `J∞` under the quotient `J_E → C_E`. -/
def integralIdeleClasses : Subgroup (IdeleClassGroup (𝓞 E) E) :=
  (integralIdeles E).map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 E) E))

instance integralIdeleClasses_normal : (integralIdeleClasses E).Normal :=
  ⟨fun n hn g => by rwa [mul_comm g n, mul_inv_cancel_right]⟩

/-- The quotient `C_E/C∞` of the idele class group by the integral idele classes. -/
abbrev IntegralIdeleClassQuotient := IdeleClassGroup (𝓞 E) E ⧸ integralIdeleClasses E

/-- The commutative group structure on `C_E/C∞`, stated directly: elaborating the generic
quotient instance for commutative groups on this double quotient times out. -/
instance integralIdeleClassQuotientCommGroup : CommGroup (IntegralIdeleClassQuotient E) where
  __ := (inferInstance : Group (IntegralIdeleClassQuotient E))
  mul_comm a b := QuotientGroup.induction_on a fun a => QuotientGroup.induction_on b fun b =>
    congrArg (QuotientGroup.mk' (integralIdeleClasses E)) (mul_comm a b)

variable {E}

theorem mem_integralIdeles_iff (x : IdeleGroup (𝓞 E) E) :
    x ∈ integralIdeles E ↔ ∀ w : HeightOneSpectrum (𝓞 E),
      Valued.v (ideleCoordinate w x : w.adicCompletion E) = 1 := Iff.rfl

/-- An idele is integral exactly when every finite coordinate is a local unit. -/
theorem mem_integralIdeles_iff_localUnits (x : IdeleGroup (𝓞 E) E) :
    x ∈ integralIdeles E ↔ ∀ w : HeightOneSpectrum (𝓞 E), ideleCoordinate w x ∈ localUnits w := by
  simp only [mem_integralIdeles_iff, mem_localUnits_iff]

theorem mem_integralIdeleClasses_iff (c : IdeleClassGroup (𝓞 E) E) :
    c ∈ integralIdeleClasses E ↔
      ∃ x ∈ integralIdeles E, (QuotientGroup.mk x : IdeleClassGroup (𝓞 E) E) = c :=
  Iff.rfl

theorem mk_mem_integralIdeleClasses {x : IdeleGroup (𝓞 E) E} (hx : x ∈ integralIdeles E) :
    (QuotientGroup.mk x : IdeleClassGroup (𝓞 E) E) ∈ integralIdeleClasses E :=
  ⟨x, hx, rfl⟩

/-- The image of a global unit of `𝓞 E` in a finite completion has valuation one. -/
theorem valued_algebraMap_ringIntegerUnit (u : (𝓞 E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (algebraMap (𝓞 E) (w.adicCompletion E) (u : 𝓞 E)) = 1 := by
  refine (valuedAdicCompletion_eq_valuation (K := E) w (u : 𝓞 E)).trans ?_
  rw [valuation_of_algebraMap, intValuation_eq_one_iff]
  exact fun h => w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)

variable (E)

/-- The principal embedding restricted to the units of `𝓞 E`, with values in `J∞`. -/
def ringIntegerUnitsToIntegralIdeles : (𝓞 E)ˣ →* integralIdeles E :=
  ((IdeleGroup.unitEmbedding (𝓞 E) E).comp (Units.map (algebraMap (𝓞 E) E : 𝓞 E →* E))).codRestrict
    (integralIdeles E) fun u w => valued_algebraMap_ringIntegerUnit u w

/-- The underlying idele of a global unit is its principal idele. -/
@[simp] theorem coe_ringIntegerUnitsToIntegralIdeles (u : (𝓞 E)ˣ) :
    (ringIntegerUnitsToIntegralIdeles E u : IdeleGroup (𝓞 E) E) =
      IdeleGroup.unitEmbedding (𝓞 E) E (Units.map (algebraMap (𝓞 E) E : 𝓞 E →* E) u) := rfl

/-- The quotient map `J∞ → C∞`, the restriction of `J_E → C_E`. -/
def integralIdelesToClasses : integralIdeles E →* integralIdeleClasses E :=
  (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 E) E)).subgroupMap (integralIdeles E)

/-- The class of an integral idele is its idele class. -/
@[simp] theorem coe_integralIdelesToClasses (x : integralIdeles E) :
    (integralIdelesToClasses E x : IdeleClassGroup (𝓞 E) E) =
      QuotientGroup.mk (x : IdeleGroup (𝓞 E) E) := rfl

theorem integralIdelesToClasses_surjective :
    Function.Surjective (integralIdelesToClasses E) :=
  MonoidHom.subgroupMap_surjective _ _

/-- The kernel of `J∞ → C∞` is the subgroup of integral principal ideles. -/
theorem integralIdelesToClasses_ker :
    (integralIdelesToClasses E).ker =
      (IdeleGroup.principalSubgroup (𝓞 E) E).comap (integralIdeles E).subtype := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.coe_subtype, ← OneMemClass.coe_eq_one,
    coe_integralIdelesToClasses, QuotientGroup.eq_one_iff]

/-- Global units of `𝓞 E` have trivial integral idele class. -/
theorem integralIdelesToClasses_ringIntegerUnitsToIntegralIdeles (u : (𝓞 E)ˣ) :
    integralIdelesToClasses E (ringIntegerUnitsToIntegralIdeles E u) = 1 := by
  apply Subtype.ext
  rw [coe_integralIdelesToClasses, coe_ringIntegerUnitsToIntegralIdeles, OneMemClass.coe_one,
    QuotientGroup.eq_one_iff]
  exact ⟨_, rfl⟩

end Subgroups

section Actions

variable (F : Type u) (E : Type v) [Field F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] relativeIdeleAction relativeIdeleClassAction

/-- The finite coordinate of a transported idele is the transport of the coordinate at the
corresponding place, so it has the same valuation. -/
theorem valued_ideleCoordinate_relativeIdeleAut (σ : E ≃ₐ[F] E) (x : IdeleGroup (𝓞 E) E)
    (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (ideleCoordinate w (relativeIdeleAut F E σ x) : w.adicCompletion E) =
      Valued.v (ideleCoordinate (finitePlaceEquiv σ.toRingEquiv w) x :
        (finitePlaceEquiv σ.toRingEquiv w).adicCompletion E) :=
  finiteCompletionEquiv_valuation σ.toRingEquiv w _

theorem relativeIdeleAut_mem_integralIdeles (σ : E ≃ₐ[F] E) {x : IdeleGroup (𝓞 E) E}
    (hx : x ∈ integralIdeles E) : relativeIdeleAut F E σ x ∈ integralIdeles E := fun w =>
  (valued_ideleCoordinate_relativeIdeleAut F E σ x w).trans (hx _)

theorem relativeIdeleClassAut_mem_integralIdeleClasses (σ : E ≃ₐ[F] E)
    {c : IdeleClassGroup (𝓞 E) E} (hc : c ∈ integralIdeleClasses E) :
    relativeIdeleClassAut F E σ c ∈ integralIdeleClasses E := by
  obtain ⟨x, hx, rfl⟩ := hc
  exact ⟨relativeIdeleAut F E σ x, relativeIdeleAut_mem_integralIdeles F E σ hx, rfl⟩

/-- The arithmetic automorphisms of `J_E` restricted to `J∞`. -/
def integralIdeleAut : (E ≃ₐ[F] E) →* MulAut (integralIdeles E) where
  toFun σ :=
    { toFun x := ⟨relativeIdeleAut F E σ (x : IdeleGroup (𝓞 E) E),
        relativeIdeleAut_mem_integralIdeles F E σ x.2⟩
      invFun x := ⟨relativeIdeleAut F E σ⁻¹ (x : IdeleGroup (𝓞 E) E),
        relativeIdeleAut_mem_integralIdeles F E σ⁻¹ x.2⟩
      left_inv x := Subtype.ext (inv_smul_smul σ (x : IdeleGroup (𝓞 E) E))
      right_inv x := Subtype.ext (smul_inv_smul σ (x : IdeleGroup (𝓞 E) E))
      map_mul' x y := Subtype.ext (map_mul (relativeIdeleAut F E σ) (x : IdeleGroup (𝓞 E) E) y) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (one_smul (E ≃ₐ[F] E) (x : IdeleGroup (𝓞 E) E))
  map_mul' σ τ := MulEquiv.ext fun x => Subtype.ext (mul_smul σ τ (x : IdeleGroup (𝓞 E) E))

@[simp] theorem coe_integralIdeleAut (σ : E ≃ₐ[F] E) (x : integralIdeles E) :
    (integralIdeleAut F E σ x : IdeleGroup (𝓞 E) E) = relativeIdeleAut F E σ x := rfl

/-- The arithmetic automorphisms of `C_E` restricted to `C∞`. -/
def integralIdeleClassAut : (E ≃ₐ[F] E) →* MulAut (integralIdeleClasses E) where
  toFun σ :=
    { toFun c := ⟨relativeIdeleClassAut F E σ (c : IdeleClassGroup (𝓞 E) E),
        relativeIdeleClassAut_mem_integralIdeleClasses F E σ c.2⟩
      invFun c := ⟨relativeIdeleClassAut F E σ⁻¹ (c : IdeleClassGroup (𝓞 E) E),
        relativeIdeleClassAut_mem_integralIdeleClasses F E σ⁻¹ c.2⟩
      left_inv c := Subtype.ext (inv_smul_smul σ (c : IdeleClassGroup (𝓞 E) E))
      right_inv c := Subtype.ext (smul_inv_smul σ (c : IdeleClassGroup (𝓞 E) E))
      map_mul' c d := Subtype.ext
        (map_mul (relativeIdeleClassAut F E σ) (c : IdeleClassGroup (𝓞 E) E) d) }
  map_one' := MulEquiv.ext fun c => Subtype.ext (one_smul (E ≃ₐ[F] E) (c : IdeleClassGroup (𝓞 E) E))
  map_mul' σ τ := MulEquiv.ext fun c =>
    Subtype.ext (mul_smul σ τ (c : IdeleClassGroup (𝓞 E) E))

@[simp] theorem coe_integralIdeleClassAut (σ : E ≃ₐ[F] E) (c : integralIdeleClasses E) :
    (integralIdeleClassAut F E σ c : IdeleClassGroup (𝓞 E) E) = relativeIdeleClassAut F E σ c :=
  rfl

/-- Each arithmetic automorphism of `C_E` maps `C∞` onto itself. -/
theorem integralIdeleClasses_map_relativeIdeleClassAut (σ : E ≃ₐ[F] E) :
    (integralIdeleClasses E).map (relativeIdeleClassAut F E σ : IdeleClassGroup (𝓞 E) E →*
      IdeleClassGroup (𝓞 E) E) = integralIdeleClasses E := by
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    exact relativeIdeleClassAut_mem_integralIdeleClasses F E σ hc
  · intro c hc
    exact ⟨relativeIdeleClassAut F E σ⁻¹ c,
      relativeIdeleClassAut_mem_integralIdeleClasses F E σ⁻¹ hc, smul_inv_smul σ c⟩

/-- The automorphisms of `C_E/C∞` induced by the arithmetic automorphisms of `C_E`. -/
def integralIdeleClassQuotientAut : (E ≃ₐ[F] E) →* MulAut (IntegralIdeleClassQuotient E) where
  toFun σ := QuotientGroup.congr (integralIdeleClasses E) (integralIdeleClasses E)
    (relativeIdeleClassAut F E σ) (integralIdeleClasses_map_relativeIdeleClassAut F E σ)
  map_one' := MulEquiv.ext fun c => QuotientGroup.induction_on c fun a =>
    congrArg (QuotientGroup.mk' (integralIdeleClasses E)) (one_smul (E ≃ₐ[F] E) a)
  map_mul' σ τ := MulEquiv.ext fun c => QuotientGroup.induction_on c fun a =>
    congrArg (QuotientGroup.mk' (integralIdeleClasses E)) (mul_smul σ τ a)

@[simp] theorem integralIdeleClassQuotientAut_mk (σ : E ≃ₐ[F] E) (c : IdeleClassGroup (𝓞 E) E) :
    integralIdeleClassQuotientAut F E σ (c : IntegralIdeleClassQuotient E) =
      (relativeIdeleClassAut F E σ c : IntegralIdeleClassQuotient E) := rfl

/-- The restricted action on `J∞`, installed explicitly. -/
@[instance_reducible]
def integralIdeleAction : MulDistribMulAction (E ≃ₐ[F] E) (integralIdeles E) where
  __ := MulAction.compHom _ (integralIdeleAut F E)
  smul_one σ := map_one (integralIdeleAut F E σ)
  smul_mul σ x y := map_mul (integralIdeleAut F E σ) x y

/-- The restricted action on `C∞`, installed explicitly. -/
@[instance_reducible]
def integralIdeleClassAction : MulDistribMulAction (E ≃ₐ[F] E) (integralIdeleClasses E) where
  __ := MulAction.compHom _ (integralIdeleClassAut F E)
  smul_one σ := map_one (integralIdeleClassAut F E σ)
  smul_mul σ c d := map_mul (integralIdeleClassAut F E σ) c d

/-- The induced action on `C_E/C∞`, installed explicitly. -/
@[instance_reducible]
def integralIdeleClassQuotientAction :
    MulDistribMulAction (E ≃ₐ[F] E) (IntegralIdeleClassQuotient E) where
  __ := MulAction.compHom _ (integralIdeleClassQuotientAut F E)
  smul_one σ := map_one (integralIdeleClassQuotientAut F E σ)
  smul_mul σ c d := map_mul (integralIdeleClassQuotientAut F E σ) c d

attribute [local instance] integralIdeleAction integralIdeleClassAction
  integralIdeleClassQuotientAction

theorem coe_integralIdele_smul (σ : E ≃ₐ[F] E) (x : integralIdeles E) :
    ((σ • x : integralIdeles E) : IdeleGroup (𝓞 E) E) = relativeIdeleAut F E σ x := rfl

theorem coe_integralIdeleClass_smul (σ : E ≃ₐ[F] E) (c : integralIdeleClasses E) :
    ((σ • c : integralIdeleClasses E) : IdeleClassGroup (𝓞 E) E) =
      relativeIdeleClassAut F E σ c := rfl

theorem integralIdeleClassQuotient_smul_mk (σ : E ≃ₐ[F] E) (c : IdeleClassGroup (𝓞 E) E) :
    σ • (c : IntegralIdeleClassQuotient E) =
      (relativeIdeleClassAut F E σ c : IntegralIdeleClassQuotient E) := rfl

/-- The additive wrapper of `J∞`, with the restricted arithmetic action. -/
abbrev integralIdeleRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E) :=
  NormalizedTwoCocycle.coefficientRepresentation (E ≃ₐ[F] E) (integralIdeles E)

/-- The additive wrapper of `C∞`, with the restricted arithmetic action. -/
abbrev integralIdeleClassRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E) :=
  NormalizedTwoCocycle.coefficientRepresentation (E ≃ₐ[F] E) (integralIdeleClasses E)

/-- The additive wrapper of `C_E/C∞`, with the induced arithmetic action. -/
abbrev integralIdeleClassQuotientRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E) :=
  NormalizedTwoCocycle.coefficientRepresentation (E ≃ₐ[F] E) (IntegralIdeleClassQuotient E)

@[simp] theorem integralIdeleRepresentation_apply (σ : E ≃ₐ[F] E)
    (x : Additive (integralIdeles E)) :
    (integralIdeleRepresentation F E).ρ σ x = Additive.ofMul (integralIdeleAut F E σ x.toMul) :=
  rfl

@[simp] theorem integralIdeleClassRepresentation_apply (σ : E ≃ₐ[F] E)
    (c : Additive (integralIdeleClasses E)) :
    (integralIdeleClassRepresentation F E).ρ σ c =
      Additive.ofMul (integralIdeleClassAut F E σ c.toMul) := rfl

@[simp] theorem integralIdeleClassQuotientRepresentation_apply (σ : E ≃ₐ[F] E)
    (c : Additive (IntegralIdeleClassQuotient E)) :
    (integralIdeleClassQuotientRepresentation F E).ρ σ c =
      Additive.ofMul (integralIdeleClassQuotientAut F E σ c.toMul) := rfl

section Units

attribute [local instance] Units.mulDistribMulActionRight

/-- The map `(𝓞 E)ˣ → J∞` is equivariant for the arithmetic unit action. -/
theorem ringIntegerUnitsToIntegralIdeles_smul (σ : E ≃ₐ[F] E) (u : (𝓞 E)ˣ) :
    ringIntegerUnitsToIntegralIdeles E (σ • u) = σ • ringIntegerUnitsToIntegralIdeles E u := by
  apply Subtype.ext
  rw [coe_integralIdele_smul, coe_ringIntegerUnitsToIntegralIdeles,
    coe_ringIntegerUnitsToIntegralIdeles, relativeIdeleAut_apply, ideleEquiv_diagonal]
  exact congrArg (IdeleGroup.unitEmbedding (𝓞 E) E) (Units.ext rfl)

/-- The principal embedding `(𝓞 E)ˣ → J∞` as a morphism of representations. -/
def ringIntegerUnitsToIntegralIdelesHom :
    ringIntegerUnitsRepresentation F E ⟶ integralIdeleRepresentation F E :=
  equivariantCoefficientHom (ringIntegerUnitsToIntegralIdeles E)
    (ringIntegerUnitsToIntegralIdeles_smul F E)

@[simp] theorem ringIntegerUnitsToIntegralIdelesHom_apply (u : Additive (𝓞 E)ˣ) :
    (ringIntegerUnitsToIntegralIdelesHom F E).hom u =
      Additive.ofMul (ringIntegerUnitsToIntegralIdeles E u.toMul) := rfl

end Units

/-- The inclusion `J∞ → J_E` as a morphism of representations. -/
def integralIdeleInclusion : integralIdeleRepresentation F E ⟶ relativeIdeleRepresentation F E :=
  equivariantCoefficientHom (integralIdeles E).subtype fun _ _ => rfl

/-- The quotient `J_E → C_E` as a morphism of representations, for independent universes. -/
def relativeIdeleClassProjection :
    relativeIdeleRepresentation F E ⟶ relativeIdeleClassRepresentation F E :=
  equivariantCoefficientHom (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 E) E))
    fun _ _ => rfl

/-- The quotient `J∞ → C∞` as a morphism of representations. -/
def integralIdelesToClassesHom :
    integralIdeleRepresentation F E ⟶ integralIdeleClassRepresentation F E :=
  equivariantCoefficientHom (integralIdelesToClasses E) fun _ _ => rfl

/-- The inclusion `C∞ → C_E` as a morphism of representations. -/
def integralIdeleClassInclusion :
    integralIdeleClassRepresentation F E ⟶ relativeIdeleClassRepresentation F E :=
  equivariantCoefficientHom (integralIdeleClasses E).subtype fun _ _ => rfl

/-- The quotient `C_E → C_E/C∞` as a morphism of representations. -/
def integralIdeleClassQuotientProjection :
    relativeIdeleClassRepresentation F E ⟶ integralIdeleClassQuotientRepresentation F E :=
  equivariantCoefficientHom (QuotientGroup.mk' (integralIdeleClasses E)) fun _ _ => rfl

@[simp] theorem integralIdeleInclusion_apply (x : Additive (integralIdeles E)) :
    (integralIdeleInclusion F E).hom x = Additive.ofMul (x.toMul : IdeleGroup (𝓞 E) E) := rfl

@[simp] theorem relativeIdeleClassProjection_apply (x : Additive (IdeleGroup (𝓞 E) E)) :
    (relativeIdeleClassProjection F E).hom x =
      Additive.ofMul (QuotientGroup.mk x.toMul : IdeleClassGroup (𝓞 E) E) := rfl

@[simp] theorem integralIdelesToClassesHom_apply (x : Additive (integralIdeles E)) :
    (integralIdelesToClassesHom F E).hom x =
      Additive.ofMul (integralIdelesToClasses E x.toMul) := rfl

@[simp] theorem integralIdeleClassInclusion_apply (c : Additive (integralIdeleClasses E)) :
    (integralIdeleClassInclusion F E).hom c =
      Additive.ofMul (c.toMul : IdeleClassGroup (𝓞 E) E) := rfl

@[simp] theorem integralIdeleClassQuotientProjection_apply
    (c : Additive (IdeleClassGroup (𝓞 E) E)) :
    (integralIdeleClassQuotientProjection F E).hom c =
      Additive.ofMul (QuotientGroup.mk c.toMul : IntegralIdeleClassQuotient E) := rfl

/-- `(𝓞 E)ˣ → J∞ → J_E` is the principal embedding of the global units. -/
theorem ringIntegerUnitsToIntegralIdelesHom_comp_integralIdeleInclusion_apply
    (u : Additive (𝓞 E)ˣ) :
    (ringIntegerUnitsToIntegralIdelesHom F E ≫ integralIdeleInclusion F E).hom u =
      Additive.ofMul (IdeleGroup.unitEmbedding (𝓞 E) E
        (Units.map (algebraMap (𝓞 E) E : 𝓞 E →* E) u.toMul)) := rfl

/-- `J∞ → C∞ → C_E` is the quotient of the underlying idele. -/
theorem integralIdelesToClassesHom_comp_integralIdeleClassInclusion_apply
    (x : Additive (integralIdeles E)) :
    (integralIdelesToClassesHom F E ≫ integralIdeleClassInclusion F E).hom x =
      Additive.ofMul (QuotientGroup.mk (x.toMul : IdeleGroup (𝓞 E) E) :
        IdeleClassGroup (𝓞 E) E) := rfl

/-- The square `J∞ → C∞ → C_E` and `J∞ → J_E → C_E` commutes. -/
@[reassoc]
theorem integralIdelesToClassesHom_comp_integralIdeleClassInclusion :
    integralIdelesToClassesHom F E ≫ integralIdeleClassInclusion F E =
      integralIdeleInclusion F E ≫ relativeIdeleClassProjection F E := rfl

/-- `(𝓞 E)ˣ → J∞ → C∞` is zero. -/
@[reassoc (attr := simp)]
theorem ringIntegerUnitsToIntegralIdelesHom_comp_integralIdelesToClassesHom :
    ringIntegerUnitsToIntegralIdelesHom F E ≫ integralIdelesToClassesHom F E = 0 := by
  ext u
  exact congrArg Additive.ofMul
    (integralIdelesToClasses_ringIntegerUnitsToIntegralIdeles E (@Additive.toMul (𝓞 E)ˣ u))

/-- `C∞ → C_E → C_E/C∞` is zero. -/
@[reassoc (attr := simp)]
theorem integralIdeleClassInclusion_comp_integralIdeleClassQuotientProjection :
    integralIdeleClassInclusion F E ≫ integralIdeleClassQuotientProjection F E = 0 := by
  ext c
  exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff _).2
    (@Additive.toMul (integralIdeleClasses E) c).2)

theorem integralIdeleInclusion_injective : Function.Injective (integralIdeleInclusion F E).hom :=
  fun _ _ h => congrArg Additive.ofMul (Subtype.ext
    (congrArg (@Additive.toMul (IdeleGroup (𝓞 E) E)) h))

theorem integralIdelesToClassesHom_surjective :
    Function.Surjective (integralIdelesToClassesHom F E).hom := by
  intro c
  obtain ⟨x, hx⟩ := integralIdelesToClasses_surjective E (@Additive.toMul _ c)
  exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩

/-- The short complex `C∞ → C_E → C_E/C∞`. -/
def integralIdeleClassSequence :
    ShortComplex (Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E)) :=
  ShortComplex.mk (integralIdeleClassInclusion F E) (integralIdeleClassQuotientProjection F E)
    (integralIdeleClassInclusion_comp_integralIdeleClassQuotientProjection F E)

/-- The sequence `C∞ → C_E → C_E/C∞` is short exact. -/
theorem integralIdeleClassSequence_shortExact : (integralIdeleClassSequence F E).ShortExact := by
  refine repShortExact_of_values _ ?_ ?_ ?_
  · intro a b h
    exact congrArg Additive.ofMul (Subtype.ext
      (congrArg (@Additive.toMul (IdeleClassGroup (𝓞 E) E)) h))
  · intro c hc
    have hc' : (QuotientGroup.mk (@Additive.toMul (IdeleClassGroup (𝓞 E) E) c) :
        IntegralIdeleClassQuotient E) = 1 := congrArg Additive.toMul hc
    exact ⟨Additive.ofMul (⟨@Additive.toMul (IdeleClassGroup (𝓞 E) E) c,
      (QuotientGroup.eq_one_iff _).1 hc'⟩ : integralIdeleClasses E), rfl⟩
  · intro q
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (@Additive.toMul (IntegralIdeleClassQuotient E) q)
    exact ⟨Additive.ofMul c, congrArg Additive.ofMul hc⟩

/-- Ordinary group cohomology of `J∞` in every degree. -/
abbrev integralIdeleCohomology (n : ℕ) :
    ModuleCat.{v} NormalizedTwoCocycle.CoefficientScalars.{v} :=
  groupCohomology (integralIdeleRepresentation F E) n

/-- Ordinary group cohomology of `C∞` in every degree. -/
abbrev integralIdeleClassCohomology (n : ℕ) :
    ModuleCat.{v} NormalizedTwoCocycle.CoefficientScalars.{v} :=
  groupCohomology (integralIdeleClassRepresentation F E) n

/-- Ordinary group cohomology of `C_E/C∞` in every degree. -/
abbrev integralIdeleClassQuotientCohomology (n : ℕ) :
    ModuleCat.{v} NormalizedTwoCocycle.CoefficientScalars.{v} :=
  groupCohomology (integralIdeleClassQuotientRepresentation F E) n

/-- Ordinary group cohomology of the global units `(𝓞 E)ˣ` in every degree. -/
abbrev ringIntegerUnitsCohomology (n : ℕ) :
    ModuleCat.{v} NormalizedTwoCocycle.CoefficientScalars.{v} :=
  groupCohomology (ringIntegerUnitsRepresentation F E) n

/-- `Hⁿ((𝓞 E)ˣ) → Hⁿ(J∞)`. -/
abbrev ringIntegerUnitsToIntegralIdeleCohomologyMap (n : ℕ) :
    ringIntegerUnitsCohomology F E n ⟶ integralIdeleCohomology F E n :=
  groupCohomology.map (MonoidHom.id _) (ringIntegerUnitsToIntegralIdelesHom F E) n

/-- `Hⁿ(J∞) → Hⁿ(J_E)`. -/
abbrev integralIdeleInclusionCohomologyMap (n : ℕ) :
    integralIdeleCohomology F E n ⟶ relativeIdeleCohomology F E n :=
  groupCohomology.map (MonoidHom.id _) (integralIdeleInclusion F E) n

/-- `Hⁿ(J∞) → Hⁿ(C∞)`. -/
abbrev integralIdelesToClassesCohomologyMap (n : ℕ) :
    integralIdeleCohomology F E n ⟶ integralIdeleClassCohomology F E n :=
  groupCohomology.map (MonoidHom.id _) (integralIdelesToClassesHom F E) n

/-- `Hⁿ(C∞) → Hⁿ(C_E)`. -/
abbrev integralIdeleClassInclusionCohomologyMap (n : ℕ) :
    integralIdeleClassCohomology F E n ⟶ relativeIdeleClassCohomology F E n :=
  groupCohomology.map (MonoidHom.id _) (integralIdeleClassInclusion F E) n

/-- `Hⁿ(C_E) → Hⁿ(C_E/C∞)`. -/
abbrev integralIdeleClassQuotientCohomologyMap (n : ℕ) :
    relativeIdeleClassCohomology F E n ⟶ integralIdeleClassQuotientCohomology F E n :=
  groupCohomology.map (MonoidHom.id _) (integralIdeleClassQuotientProjection F E) n

end Actions

section SameUniverse

variable (F E : Type u) [Field F] [Field E] [NumberField E] [Algebra F E]

/-- For fields in one universe the quotient morphism is the published `ideleQuotientCoefficients`. -/
theorem relativeIdeleClassProjection_eq_ideleQuotientCoefficients :
    relativeIdeleClassProjection F E = ideleQuotientCoefficients F E := rfl

end SameUniverse

end Langlands.ClassField.Global

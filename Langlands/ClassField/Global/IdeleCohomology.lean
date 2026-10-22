import Langlands.ClassField.Global.CohomologyMaps

/-! # The idele group as a Galois representation and its finite-place coordinates

The relative automorphism action of `Gal(E/F)` on the actual idele group `J_E`, the
representation and cohomology it defines, the `w`-coordinate `J_E → E_wˣ` at a finite place,
and its arithmetic equivariance along `decompositionHom v w : Gal(E_w/F_v) → Gal(E/F)`; the
resulting morphisms of representations between `J_E` and `E_wˣ` and the maps they induce on
group cohomology.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory FundamentalClass

universe u v

section Action

variable (K : Type u) (E : Type v) [Field K] [Field E] [NumberField E] [Algebra K E]

/-- The relative automorphism action on the actual idele group. -/
def relativeIdeleAut :
    (E ≃ₐ[K] E) →* (IdeleGroup (𝓞 E) E ≃* IdeleGroup (𝓞 E) E) where
  toFun σ := (ideleEquiv σ.toRingEquiv).toMulEquiv
  map_one' := congrArg ContinuousMulEquiv.toMulEquiv ideleEquiv_refl
  map_mul' σ τ := congrArg ContinuousMulEquiv.toMulEquiv
    (ideleEquiv_trans τ.toRingEquiv σ.toRingEquiv)

@[simp] theorem relativeIdeleAut_apply (σ : E ≃ₐ[K] E) (x : IdeleGroup (𝓞 E) E) :
    relativeIdeleAut K E σ x = ideleEquiv σ.toRingEquiv x := rfl

theorem continuous_relativeIdeleAut (σ : E ≃ₐ[K] E) :
    Continuous (relativeIdeleAut K E σ) :=
  (ideleEquiv σ.toRingEquiv).continuous

/-- The relative action on ideles, installed explicitly. -/
@[instance_reducible]
def relativeIdeleAction : MulDistribMulAction (E ≃ₐ[K] E) (IdeleGroup (𝓞 E) E) where
  __ := MulAction.compHom (IdeleGroup (𝓞 E) E) (relativeIdeleAut K E)
  smul_one σ := map_one (relativeIdeleAut K E σ)
  smul_mul σ a b := map_mul (relativeIdeleAut K E σ) a b

attribute [local instance] relativeIdeleAction

theorem relativeIdele_smul (σ : E ≃ₐ[K] E) (x : IdeleGroup (𝓞 E) E) :
    σ • x = ideleEquiv σ.toRingEquiv x := rfl

/-- The additive wrapper of the actual idele group `J_E`, with its arithmetic action. -/
abbrev relativeIdeleRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[K] E) :=
  NormalizedTwoCocycle.coefficientRepresentation (E ≃ₐ[K] E) (IdeleGroup (𝓞 E) E)

@[simp] theorem relativeIdeleRepresentation_apply (σ : E ≃ₐ[K] E)
    (a : Additive (IdeleGroup (𝓞 E) E)) :
    (relativeIdeleRepresentation K E).ρ σ a =
      Additive.ofMul (relativeIdeleAut K E σ a.toMul) := rfl

/-- Ordinary relative group cohomology of the idele group in every degree. -/
abbrev relativeIdeleCohomology (n : ℕ) :
    ModuleCat.{v} NormalizedTwoCocycle.CoefficientScalars.{v} :=
  groupCohomology (relativeIdeleRepresentation K E) n

end Action

section Coordinate

variable {E : Type u} [Field E] [NumberField E]

/-- The `w`-coordinate `J_E → E_wˣ` of an idele at a finite place `w`. -/
def ideleCoordinate (w : HeightOneSpectrum (𝓞 E)) :
    IdeleGroup (𝓞 E) E →* (w.adicCompletion E)ˣ :=
  Units.map
    { toFun := fun x : AdeleRing (𝓞 E) E => x.2 w
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

@[simp] theorem ideleCoordinate_val (w : HeightOneSpectrum (𝓞 E)) (x : IdeleGroup (𝓞 E) E) :
    (ideleCoordinate w x : w.adicCompletion E) = (x : AdeleRing (𝓞 E) E).2 w := rfl

/-- The `w`-coordinate of the idele with a single coordinate `x` at `w` is `x`. -/
@[simp] theorem ideleCoordinate_ofAdicCompletion_self (w : HeightOneSpectrum (𝓞 E))
    (x : (w.adicCompletion E)ˣ) :
    ideleCoordinate w (IdeleGroup.ofAdicCompletion (𝓞 E) E w x) = x := by
  classical
  apply Units.ext
  change Pi.mulSingle w (x : w.adicCompletion E) w = x
  simp

/-- The idele with a single coordinate at `w` has trivial coordinates at all other places. -/
theorem ideleCoordinate_ofAdicCompletion_of_ne {w w' : HeightOneSpectrum (𝓞 E)} (h : w' ≠ w)
    (x : (w.adicCompletion E)ˣ) :
    ideleCoordinate w' (IdeleGroup.ofAdicCompletion (𝓞 E) E w x) = 1 := by
  classical
  apply Units.ext
  change Pi.mulSingle w (x : w.adicCompletion E) w' = 1
  simp [h]

/-- The `w`-coordinate of a principal idele is the image of the field element in `E_w`. -/
@[simp] theorem ideleCoordinate_unitEmbedding (w : HeightOneSpectrum (𝓞 E)) (a : Eˣ) :
    (ideleCoordinate w (IdeleGroup.unitEmbedding (𝓞 E) E a) : w.adicCompletion E) =
      algebraMap E (w.adicCompletion E) a := rfl

/-- The isomorphism induced on ideles by `e` sends the idele with a single coordinate `x` at
`q = finitePlaceEquiv e p` to the idele with a single coordinate at `p`, the transport of `x`
along any continuous ring homomorphism which extends `e` on the dense image of the field. -/
theorem ideleEquiv_ofAdicCompletion_of_eq {K L : Type u} [Field K] [NumberField K] [Field L]
    [NumberField L] (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L))
    (q : HeightOneSpectrum (𝓞 K)) (h : finitePlaceEquiv e p = q)
    (φ : q.adicCompletion K →+* p.adicCompletion L) (hφ : Continuous φ)
    (hφe : ∀ a : K, φ (algebraMap K (q.adicCompletion K) a) =
      algebraMap L (p.adicCompletion L) (e a))
    (x : (q.adicCompletion K)ˣ) :
    ideleEquiv e (IdeleGroup.ofAdicCompletion (𝓞 K) K q x) =
      IdeleGroup.ofAdicCompletion (𝓞 L) L p (Units.map φ.toMonoidHom x) := by
  subst h
  have hφ' : ∀ y, φ y = finiteCompletionEquiv e p y := by
    intro y
    have h := (denseRange_algebraMap K (finitePlaceEquiv e p)).equalizer hφ
      (continuous_finiteCompletionEquiv e p) (by
        funext a
        exact (hφe a).trans (finiteCompletionEquiv_coe e p a).symm)
    exact congrFun h y
  rw [ideleEquiv_ofAdicCompletion]
  congr 1
  exact Units.ext (hφ' _).symm

end Coordinate

section Decomposition

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Normal F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The `w`-coordinate is equivariant along `decompositionHom v w`: the `w`-coordinate of
`decompositionHom v w σ • x` is `σ` applied to the `w`-coordinate of `x`. -/
theorem ideleCoordinate_relativeIdeleAut_decompositionHom
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
    (x : IdeleGroup (𝓞 E) E) :
    ideleCoordinate w (relativeIdeleAut F E (decompositionHom v w σ) x) =
      Units.map σ.toRingEquiv.toMonoidHom (ideleCoordinate w x) := by
  apply Units.ext
  change finiteCompletionEquiv (decompositionHom v w σ).toRingEquiv w
      ((x : AdeleRing (𝓞 E) E).2 (finitePlaceEquiv (decompositionHom v w σ).toRingEquiv w)) =
    σ ((x : AdeleRing (𝓞 E) E).2 w)
  exact adicCompletion_coordinate_eq (finitePlaceEquiv_decompositionHom v w σ)
    (finiteCompletionEquiv (decompositionHom v w σ).toRingEquiv w) σ
    (continuous_finiteCompletionEquiv _ w) (continuous_localAut v w σ)
    (fun a => (finiteCompletionEquiv_coe _ w a).trans (algebraMap_decompositionHom v w σ a))
    (x : AdeleRing (𝓞 E) E).2

/-- The single-coordinate embedding `E_wˣ → J_E` is equivariant along `decompositionHom v w`. -/
theorem relativeIdeleAut_decompositionHom_ofAdicCompletion
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
    (x : (w.adicCompletion E)ˣ) :
    relativeIdeleAut F E (decompositionHom v w σ) (IdeleGroup.ofAdicCompletion (𝓞 E) E w x) =
      IdeleGroup.ofAdicCompletion (𝓞 E) E w (Units.map σ.toRingEquiv.toMonoidHom x) :=
  ideleEquiv_ofAdicCompletion_of_eq _ w w (finitePlaceEquiv_decompositionHom v w σ)
    (σ : w.adicCompletion E →+* w.adicCompletion E) (continuous_localAut v w σ)
    (fun a => (algebraMap_decompositionHom v w σ a).symm) x

/-- The `w`-coordinate on the additive coefficient modules, linear over the lifted integers. -/
def ideleCoordinateLinear :
    (relativeIdeleRepresentation F E).V →ₗ[ULift.{u} ℤ]
      (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)).V where
  toFun x := Additive.ofMul (ideleCoordinate w (@Additive.toMul (IdeleGroup (𝓞 E) E) x))
  map_add' x y := congrArg Additive.ofMul (map_mul (ideleCoordinate w)
    (@Additive.toMul (IdeleGroup (𝓞 E) E) x) (@Additive.toMul (IdeleGroup (𝓞 E) E) y))
  map_smul' r x := congrArg Additive.ofMul (map_zpow (ideleCoordinate w)
    (@Additive.toMul (IdeleGroup (𝓞 E) E) x) r.down)

omit [Normal F E] in
/-- The value of `ideleCoordinateLinear`. -/
theorem ideleCoordinateLinear_apply (x : (relativeIdeleRepresentation F E).V) :
    ideleCoordinateLinear v w x =
      Additive.ofMul (ideleCoordinate w (@Additive.toMul (IdeleGroup (𝓞 E) E) x)) :=
  rfl

/-- The local projection `J_E → E_wˣ` (the `w`-coordinate), a morphism of representations of
`Gal(E_w/F_v)` with `J_E` restricted along `decompositionHom v w`. -/
def ideleLocalProjection :
    Rep.res (decompositionHom v w) (relativeIdeleRepresentation F E) ⟶
      unitsRepresentation (padicField v).Carrier (w.adicCompletion E) :=
  Rep.ofHom
    { toLinearMap := ideleCoordinateLinear v w
      isIntertwining' σ := by
        ext x
        exact congrArg Additive.ofMul
          (ideleCoordinate_relativeIdeleAut_decompositionHom v w σ
            (@Additive.toMul (IdeleGroup (𝓞 E) E) x)) }

/-- The single-coordinate embedding `E_wˣ → J_E` on the additive coefficient modules. -/
def ideleEmbeddingLinear :
    (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)).V →ₗ[ULift.{u} ℤ]
      (relativeIdeleRepresentation F E).V where
  toFun x := Additive.ofMul (IdeleGroup.ofAdicCompletion (𝓞 E) E w
    (@Additive.toMul (w.adicCompletion E)ˣ x))
  map_add' x y := congrArg Additive.ofMul (map_mul (IdeleGroup.ofAdicCompletion (𝓞 E) E w)
    (@Additive.toMul (w.adicCompletion E)ˣ x) (@Additive.toMul (w.adicCompletion E)ˣ y))
  map_smul' r x := congrArg Additive.ofMul (map_zpow (IdeleGroup.ofAdicCompletion (𝓞 E) E w)
    (@Additive.toMul (w.adicCompletion E)ˣ x) r.down)

omit [Normal F E] in
/-- The value of `ideleEmbeddingLinear`. -/
theorem ideleEmbeddingLinear_apply
    (x : (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)).V) :
    ideleEmbeddingLinear v w x = Additive.ofMul (IdeleGroup.ofAdicCompletion (𝓞 E) E w
      (@Additive.toMul (w.adicCompletion E)ˣ x)) :=
  rfl

/-- The local embedding `E_wˣ → J_E` (single coordinate at `w`), a morphism of representations
of `Gal(E_w/F_v)` with `J_E` restricted along `decompositionHom v w`. -/
def ideleLocalEmbedding :
    unitsRepresentation (padicField v).Carrier (w.adicCompletion E) ⟶
      Rep.res (decompositionHom v w) (relativeIdeleRepresentation F E) :=
  Rep.ofHom
    { toLinearMap := ideleEmbeddingLinear v w
      isIntertwining' σ := by
        ext x
        exact congrArg Additive.ofMul
          (relativeIdeleAut_decompositionHom_ofAdicCompletion v w σ
            (@Additive.toMul (w.adicCompletion E)ˣ x)).symm }

/-- The local projection is a retraction of the local embedding. -/
@[reassoc (attr := simp)]
theorem ideleLocalEmbedding_comp_ideleLocalProjection :
    ideleLocalEmbedding v w ≫ ideleLocalProjection v w = 𝟙 _ := by
  ext x
  exact congrArg Additive.ofMul (ideleCoordinate_ofAdicCompletion_self w
    (@Additive.toMul (w.adicCompletion E)ˣ x))

/-- The map `Hⁿ(Gal(E/F), J_E) → Hⁿ(Gal(E_w/F_v), E_wˣ)`: restriction along
`decompositionHom v w` followed by the `w`-coordinate. -/
abbrev ideleLocalMap (n : ℕ) :
    relativeIdeleCohomology F E n ⟶
      relativeCohomology (padicField v).Carrier (w.adicCompletion E) n :=
  groupCohomology.map (decompositionHom v w) (ideleLocalProjection v w) n

/-- The map `Hⁿ(Gal(E_w/F_v), E_wˣ) → Hⁿ(Gal(E_w/F_v), J_E)` induced by the local embedding. -/
abbrev ideleLocalInclusion (n : ℕ) :
    relativeCohomology (padicField v).Carrier (w.adicCompletion E) n ⟶
      groupCohomology (Rep.res (decompositionHom v w) (relativeIdeleRepresentation F E)) n :=
  groupCohomology.map (MonoidHom.id _) (ideleLocalEmbedding v w) n

/-- The localization `Eˣ → E_wˣ` on the additive coefficient modules. -/
def unitsLocalizationLinear :
    (unitsRepresentation F E).V →ₗ[ULift.{u} ℤ]
      (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)).V where
  toFun x := Additive.ofMul (Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom
    (@Additive.toMul Eˣ x))
  map_add' x y := congrArg Additive.ofMul
    (map_mul (Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom)
      (@Additive.toMul Eˣ x) (@Additive.toMul Eˣ y))
  map_smul' r x := congrArg Additive.ofMul
    (map_zpow (Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom)
      (@Additive.toMul Eˣ x) r.down)

omit [Normal F E] in
/-- The value of `unitsLocalizationLinear`. -/
theorem unitsLocalizationLinear_apply (x : (unitsRepresentation F E).V) :
    unitsLocalizationLinear v w x = Additive.ofMul
      (Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom (@Additive.toMul Eˣ x)) :=
  rfl

/-- The localization `Eˣ → E_wˣ`, a morphism of representations of `Gal(E_w/F_v)` with `Eˣ`
restricted along `decompositionHom v w`. -/
def unitsLocalization :
    Rep.res (decompositionHom v w) (unitsRepresentation F E) ⟶
      unitsRepresentation (padicField v).Carrier (w.adicCompletion E) :=
  Rep.ofHom
    { toLinearMap := unitsLocalizationLinear v w
      isIntertwining' σ := by
        ext x
        exact congrArg Additive.ofMul (Units.ext
          (algebraMap_decompositionHom v w σ ((@Additive.toMul Eˣ x : Eˣ) : E))) }

/-- The local component `Hⁿ(Gal(E/F), Eˣ) → Hⁿ(Gal(E_w/F_v), E_wˣ)` of a global class:
restriction along `decompositionHom v w` with coefficients changed by `Eˣ → E_wˣ`. -/
abbrev unitsLocalMap (n : ℕ) :
    relativeCohomology F E n ⟶
      relativeCohomology (padicField v).Carrier (w.adicCompletion E) n :=
  groupCohomology.map (decompositionHom v w) (unitsLocalization v w) n

end Decomposition

end Langlands.ClassField.Global

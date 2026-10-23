import Langlands.ClassField.Global.IdeleSemilocal
import Langlands.ClassField.Global.ReciprocityStatement
import Langlands.ClassField.Global.IdeleCoefficientSequence

/-! # Archimedean components of idele cohomology in degree two -/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.ClassFieldTheory.Local
open CategoryTheory Limits Reciprocity

section Coordinate

variable {E : Type u} [Field E] [NumberField E]

/-- The coordinate `J_E → E_wˣ` of an idele at an infinite place `w`: the `w`-component of its
infinite adele part. -/
def ideleInfiniteCoordinate (w : InfinitePlace E) : IdeleGroup (𝓞 E) E →* (w.Completion)ˣ :=
  Units.map
    { toFun := fun x : AdeleRing (𝓞 E) E => x.1 w
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

@[simp] theorem ideleInfiniteCoordinate_val (w : InfinitePlace E) (x : IdeleGroup (𝓞 E) E) :
    (ideleInfiniteCoordinate w x : w.Completion) = (x : AdeleRing (𝓞 E) E).1 w := rfl

/-- The `w`-coordinate of the idele with a single coordinate `y` at `w` is `y`. -/
@[simp] theorem ideleInfiniteCoordinate_ofCompletion_self (w : InfinitePlace E)
    (y : (w.Completion)ˣ) :
    ideleInfiniteCoordinate w (IdeleGroup.ofCompletion (𝓞 E) E w y) = y := by
  classical
  apply Units.ext
  change Pi.mulSingle w (y : w.Completion) w = y
  simp

/-- The idele with a single coordinate at `w` has trivial coordinates at all other infinite
places. -/
theorem ideleInfiniteCoordinate_ofCompletion_of_ne {w w' : InfinitePlace E} (h : w' ≠ w)
    (y : (w.Completion)ˣ) :
    ideleInfiniteCoordinate w' (IdeleGroup.ofCompletion (𝓞 E) E w y) = 1 := by
  classical
  apply Units.ext
  change Pi.mulSingle w (y : w.Completion) w' = 1
  simp [h]

/-- The `w`-coordinate of a principal idele is the image of the field element in `E_w`. -/
@[simp] theorem ideleInfiniteCoordinate_unitEmbedding (w : InfinitePlace E) (a : Eˣ) :
    (ideleInfiniteCoordinate w (IdeleGroup.unitEmbedding (𝓞 E) E a) : w.Completion) =
      algebraMap E w.Completion a := rfl

/-- An idele has infinite adele part `1` exactly when all its infinite coordinates are `1`. -/
theorem ideleInfinite_eq_one_iff (x : IdeleGroup (𝓞 E) E) :
    (x : AdeleRing (𝓞 E) E).1 = 1 ↔ ∀ w, ideleInfiniteCoordinate w x = 1 := by
  constructor
  · intro h w
    exact Units.ext (congrFun h w)
  · intro h
    funext w
    exact congrArg Units.val (h w)

/-- The idele with infinite coordinates `a w` and finite part `1`. -/
def ideleOfInfiniteCoordinates (a : ∀ w : InfinitePlace E, (w.Completion)ˣ) :
    IdeleGroup (𝓞 E) E where
  val := ((fun w => (a w : w.Completion) : InfiniteAdeleRing E), 1)
  inv := ((fun w => (((a w)⁻¹ : (w.Completion)ˣ) : w.Completion) : InfiniteAdeleRing E), 1)
  val_inv := Prod.ext (funext fun w => Units.mul_inv (a w)) (mul_one _)
  inv_val := Prod.ext (funext fun w => Units.inv_mul (a w)) (mul_one _)

@[simp] theorem ideleInfiniteCoordinate_ideleOfInfiniteCoordinates
    (a : ∀ w : InfinitePlace E, (w.Completion)ˣ) (w : InfinitePlace E) :
    ideleInfiniteCoordinate w (ideleOfInfiniteCoordinates a) = a w :=
  Units.ext rfl

end Coordinate

section Action

variable {F E : Type u} [Field F] [Field E] [NumberField E] [Algebra F E]

/-- The coordinate of `g • x` at an infinite place `w` is the transport of the coordinate of `x`
at `infinitePlaceEquiv g w`. -/
theorem ideleInfiniteCoordinate_relativeIdeleAut (g : E ≃ₐ[F] E) (w : InfinitePlace E)
    (x : IdeleGroup (𝓞 E) E) :
    (ideleInfiniteCoordinate w (relativeIdeleAut F E g x) : w.Completion) =
      infiniteCompletionEquiv g.toRingEquiv w
        ((x : AdeleRing (𝓞 E) E).1 (w.comap g.toRingEquiv.toRingHom)) :=
  rfl

omit [NumberField E] in
/-- The pullback `infinitePlaceEquiv g w` is Mathlib's action `g⁻¹ • w`. -/
theorem infinitePlaceEquiv_eq_inv_smul (g : E ≃ₐ[F] E) (w : InfinitePlace E) :
    infinitePlaceEquiv g.toRingEquiv w = g⁻¹ • w := by
  ext
  rfl

omit [NumberField E] in
theorem infinitePlaceEquiv_mul (g h : E ≃ₐ[F] E) (w : InfinitePlace E) :
    infinitePlaceEquiv (g * h).toRingEquiv w =
      infinitePlaceEquiv h.toRingEquiv (infinitePlaceEquiv g.toRingEquiv w) := by
  ext
  rfl

omit [NumberField E] in
/-- `g` fixes `w` for the pullback action iff `g` lies in Mathlib's stabilizer of `w`. -/
theorem infinitePlaceEquiv_eq_self_iff (g : E ≃ₐ[F] E) (w : InfinitePlace E) :
    infinitePlaceEquiv g.toRingEquiv w = w ↔ g ∈ MulAction.stabilizer (E ≃ₐ[F] E) w := by
  rw [infinitePlaceEquiv_eq_inv_smul, ← MulAction.mem_stabilizer_iff, Subgroup.inv_mem_iff]

omit [NumberField E] in
/-- A complex conjugation of `w` fixes `w`. -/
theorem mem_stabilizer_of_isConj {w : InfinitePlace E} {c : E ≃ₐ[F] E}
    (hc : ComplexEmbedding.IsConj w.embedding c) :
    c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w := by
  rw [← w.mk_embedding, InfinitePlace.mem_stabilizer_mk_iff]
  exact Or.inr hc

omit [NumberField E] in
/-- The value under the canonical embedding into `ℂ` of an element of `E` in a completion. -/
theorem extensionEmbedding_algebraMap (w : InfinitePlace E) (a : E) :
    InfinitePlace.Completion.extensionEmbedding w (algebraMap E w.Completion a) =
      w.embedding a :=
  InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs w.1 a)

omit [NumberField E] in
/-- If `c` is the complex conjugation of `w`, its extension to the completions acts as complex
conjugation on complex values. -/
theorem extensionEmbedding_infiniteCompletionEquiv_of_isConj {w : InfinitePlace E}
    {c : E ≃ₐ[F] E} (hc : ComplexEmbedding.IsConj w.embedding c)
    (z : (infinitePlaceEquiv c.toRingEquiv w).Completion) :
    InfinitePlace.Completion.extensionEmbedding w (infiniteCompletionEquiv c.toRingEquiv w z) =
      star (InfinitePlace.Completion.extensionEmbedding
        (infinitePlaceEquiv c.toRingEquiv w) z) := by
  have hw : infinitePlaceEquiv c.toRingEquiv w = w :=
    (infinitePlaceEquiv_eq_self_iff c w).2 (mem_stabilizer_of_isConj hc)
  induction z using InfinitePlace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
        (continuous_infiniteCompletionMap _ w))
      (continuous_star.comp
        (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous)
  | ih a =>
    have h1 := infiniteCompletionMap_coe c.toRingEquiv.toRingHom w (WithAbs.ofAbs a)
    change InfinitePlace.Completion.extensionEmbedding w
        (infiniteCompletionMap c.toRingEquiv.toRingHom w
          (algebraMap E _ (WithAbs.ofAbs a))) = _
    rw [h1, extensionEmbedding_algebraMap]
    change _ = star (InfinitePlace.Completion.extensionEmbedding
      (infinitePlaceEquiv c.toRingEquiv w) (algebraMap E _ (WithAbs.ofAbs a)))
    rw [extensionEmbedding_algebraMap, congrArg InfinitePlace.embedding hw]
    exact hc.eq _

/-- If `c` is the complex conjugation of `w`, the complex value of the `w`-coordinate of `c • x`
is the complex conjugate of that of `x`. -/
theorem extensionEmbedding_ideleInfiniteCoordinate_of_isConj {w : InfinitePlace E}
    {c : E ≃ₐ[F] E} (hc : ComplexEmbedding.IsConj w.embedding c) (x : IdeleGroup (𝓞 E) E) :
    InfinitePlace.Completion.extensionEmbedding w
        (ideleInfiniteCoordinate w (relativeIdeleAut F E c x)) =
      star (InfinitePlace.Completion.extensionEmbedding w (ideleInfiniteCoordinate w x)) := by
  have hw : infinitePlaceEquiv c.toRingEquiv w = w :=
    (infinitePlaceEquiv_eq_self_iff c w).2 (mem_stabilizer_of_isConj hc)
  have key : ∀ p, p = w → InfinitePlace.Completion.extensionEmbedding p
      (ideleInfiniteCoordinate p x) =
        InfinitePlace.Completion.extensionEmbedding w (ideleInfiniteCoordinate w x) := by
    rintro _ rfl
    rfl
  exact (extensionEmbedding_infiniteCompletionEquiv_of_isConj hc
    (ideleInfiniteCoordinate (infinitePlaceEquiv c.toRingEquiv w) x :
      (infinitePlaceEquiv c.toRingEquiv w).Completion)).trans (congrArg star (key _ hw))

/-- The `w`-coordinates of `g • x` and `g • y` agree iff the coordinates of `x` and `y` at
`infinitePlaceEquiv g w` agree. -/
theorem ideleInfiniteCoordinate_relativeIdeleAut_eq_iff (g : E ≃ₐ[F] E) (w : InfinitePlace E)
    (x y : IdeleGroup (𝓞 E) E) :
    ideleInfiniteCoordinate w (relativeIdeleAut F E g x) =
        ideleInfiniteCoordinate w (relativeIdeleAut F E g y) ↔
      ideleInfiniteCoordinate (infinitePlaceEquiv g.toRingEquiv w) x =
        ideleInfiniteCoordinate (infinitePlaceEquiv g.toRingEquiv w) y := by
  rw [Units.ext_iff, Units.ext_iff, ideleInfiniteCoordinate_relativeIdeleAut,
    ideleInfiniteCoordinate_relativeIdeleAut]
  exact (infiniteCompletionEquiv g.toRingEquiv w).injective.eq_iff

omit [Algebra F E] in
/-- Transport of an equality of coordinates along an equality of places. -/
theorem ideleInfiniteCoordinate_congr {p w : InfinitePlace E} (h : p = w)
    {x y : IdeleGroup (𝓞 E) E}
    (hxy : ideleInfiniteCoordinate w x = ideleInfiniteCoordinate w y) :
    ideleInfiniteCoordinate p x = ideleInfiniteCoordinate p y := by
  subst h
  exact hxy

/-- If `g` fixes `w`, the `w`-coordinate of `g • x` only depends on the `w`-coordinate of `x`. -/
theorem ideleInfiniteCoordinate_relativeIdeleAut_congr {g : E ≃ₐ[F] E} {w : InfinitePlace E}
    (hg : infinitePlaceEquiv g.toRingEquiv w = w) {x y : IdeleGroup (𝓞 E) E}
    (hxy : ideleInfiniteCoordinate w x = ideleInfiniteCoordinate w y) :
    ideleInfiniteCoordinate w (relativeIdeleAut F E g x) =
      ideleInfiniteCoordinate w (relativeIdeleAut F E g y) :=
  (ideleInfiniteCoordinate_relativeIdeleAut_eq_iff g w x y).2
    (ideleInfiniteCoordinate_congr hg hxy)

/-- If the coordinate of `x` at `infinitePlaceEquiv g w` is `1`, so is the `w`-coordinate of
`g • x`. -/
theorem ideleInfiniteCoordinate_relativeIdeleAut_eq_one (g : E ≃ₐ[F] E) (w : InfinitePlace E)
    {x : IdeleGroup (𝓞 E) E}
    (hx : ideleInfiniteCoordinate (infinitePlaceEquiv g.toRingEquiv w) x = 1) :
    ideleInfiniteCoordinate w (relativeIdeleAut F E g x) = 1 := by
  have h := (ideleInfiniteCoordinate_relativeIdeleAut_eq_iff g w x 1).2
    (hx.trans (map_one _).symm)
  rw [map_one, map_one] at h
  exact h

/-- The single-coordinate idele at `w`, translated by `g`, has trivial coordinate at every `w'`
with `infinitePlaceEquiv g w' ≠ w`. -/
theorem ideleInfiniteCoordinate_relativeIdeleAut_ofCompletion_of_ne (g : E ≃ₐ[F] E)
    {w w' : InfinitePlace E} (h : infinitePlaceEquiv g.toRingEquiv w' ≠ w)
    (y : (w.Completion)ˣ) :
    ideleInfiniteCoordinate w' (relativeIdeleAut F E g (IdeleGroup.ofCompletion (𝓞 E) E w y)) =
      1 :=
  ideleInfiniteCoordinate_relativeIdeleAut_eq_one g w'
    (ideleInfiniteCoordinate_ofCompletion_of_ne h y)

theorem relativeIdeleAut_mul_apply (g h : E ≃ₐ[F] E) (x : IdeleGroup (𝓞 E) E) :
    relativeIdeleAut F E (g * h) x = relativeIdeleAut F E g (relativeIdeleAut F E h x) := by
  rw [map_mul]
  rfl

/-- The action preserves ideles with finite part `1`. -/
theorem relativeIdeleAut_finite_eq_one (g : E ≃ₐ[F] E) {x : IdeleGroup (𝓞 E) E}
    (hx : (x : AdeleRing (𝓞 E) E).2 = 1) :
    ((relativeIdeleAut F E g x : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E).2 = 1 := by
  change finiteAdeleEquiv g.toRingEquiv (x : AdeleRing (𝓞 E) E).2 = 1
  rw [hx, map_one]

omit [Algebra F E] in
/-- An idele with finite part `1` and trivial coordinates away from `w` is the single-coordinate
idele of its `w`-coordinate. -/
theorem idele_eq_ofCompletion {w : InfinitePlace E} {x : IdeleGroup (𝓞 E) E}
    (hfin : (x : AdeleRing (𝓞 E) E).2 = 1)
    (hw : ∀ u, u ≠ w → ideleInfiniteCoordinate u x = 1) :
    x = IdeleGroup.ofCompletion (𝓞 E) E w (ideleInfiniteCoordinate w x) := by
  classical
  apply Units.ext
  apply Prod.ext
  · funext u
    change (x : AdeleRing (𝓞 E) E).1 u = Pi.mulSingle w ((x : AdeleRing (𝓞 E) E).1 w) u
    by_cases h : u = w
    · subst h
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne h]
      exact congrArg Units.val (hw u h)
  · exact hfin

/-- If `g` fixes `w`, then `g` maps the single-coordinate ideles at `w` to themselves. -/
theorem relativeIdeleAut_ofCompletion_of_eq {g : E ≃ₐ[F] E} {w : InfinitePlace E}
    (hg : infinitePlaceEquiv g.toRingEquiv w = w) (y : (w.Completion)ˣ) :
    relativeIdeleAut F E g (IdeleGroup.ofCompletion (𝓞 E) E w y) =
      IdeleGroup.ofCompletion (𝓞 E) E w
        (ideleInfiniteCoordinate w (relativeIdeleAut F E g (IdeleGroup.ofCompletion (𝓞 E) E w y))) := by
  apply idele_eq_ofCompletion (relativeIdeleAut_finite_eq_one g rfl)
  intro u hu
  apply ideleInfiniteCoordinate_relativeIdeleAut_ofCompletion_of_ne
  intro h
  exact hu ((infinitePlaceEquiv g.toRingEquiv).injective (h.trans hg.symm))

end Action

section Local

variable {F E : Type u} [Field F] [Field E] [NumberField E] [Algebra F E]

variable (F) in
/-- The action of the stabilizer `D_w` of an infinite place `w` on `E_wˣ`: `d • y` is the
`w`-coordinate of `d • ι_w(y)`, where `ι_w(y)` is the idele with coordinate `y` at `w` and `1`
elsewhere. -/
@[instance_reducible]
def infiniteLocalAction (w : InfinitePlace E) :
    MulDistribMulAction (MulAction.stabilizer (E ≃ₐ[F] E) w) (w.Completion)ˣ where
  smul d y := ideleInfiniteCoordinate w
    (relativeIdeleAut F E d (IdeleGroup.ofCompletion (𝓞 E) E w y))
  one_smul y := by
    change ideleInfiniteCoordinate w
      (relativeIdeleAut F E 1 (IdeleGroup.ofCompletion (𝓞 E) E w y)) = y
    rw [map_one]
    exact ideleInfiniteCoordinate_ofCompletion_self w y
  mul_smul d d' y := by
    change ideleInfiniteCoordinate w (relativeIdeleAut F E ((d : E ≃ₐ[F] E) * d')
        (IdeleGroup.ofCompletion (𝓞 E) E w y)) =
      ideleInfiniteCoordinate w (relativeIdeleAut F E d (IdeleGroup.ofCompletion (𝓞 E) E w
        (ideleInfiniteCoordinate w
          (relativeIdeleAut F E d' (IdeleGroup.ofCompletion (𝓞 E) E w y)))))
    rw [relativeIdeleAut_mul_apply]
    exact ideleInfiniteCoordinate_relativeIdeleAut_congr
      ((infinitePlaceEquiv_eq_self_iff _ w).2 d.2)
      (ideleInfiniteCoordinate_ofCompletion_self w _).symm
  smul_mul d y z := by
    change ideleInfiniteCoordinate w
        (relativeIdeleAut F E d (IdeleGroup.ofCompletion (𝓞 E) E w (y * z))) =
      ideleInfiniteCoordinate w (relativeIdeleAut F E d (IdeleGroup.ofCompletion (𝓞 E) E w y)) *
        ideleInfiniteCoordinate w (relativeIdeleAut F E d (IdeleGroup.ofCompletion (𝓞 E) E w z))
    rw [map_mul, map_mul, map_mul]
  smul_one d := by
    change ideleInfiniteCoordinate w
      (relativeIdeleAut F E d (IdeleGroup.ofCompletion (𝓞 E) E w 1)) = 1
    rw [map_one, map_one, map_one]

variable (F) in
/-- The local coefficient module `E_wˣ` of the stabilizer `D_w` of an infinite place `w`. -/
abbrev infiniteLocalRepresentation (w : InfinitePlace E) :
    Rep.{u} NormalizedTwoCocycle.CoefficientScalars.{u} (MulAction.stabilizer (E ≃ₐ[F] E) w) :=
  @NormalizedTwoCocycle.coefficientRepresentation _ (w.Completion)ˣ _ _ (infiniteLocalAction F w)

theorem infiniteLocalRepresentation_apply (w : InfinitePlace E)
    (d : MulAction.stabilizer (E ≃ₐ[F] E) w) (a : Additive (w.Completion)ˣ) :
    (infiniteLocalRepresentation F w).ρ d a = Additive.ofMul (ideleInfiniteCoordinate w
      (relativeIdeleAut F E d (IdeleGroup.ofCompletion (𝓞 E) E w a.toMul))) :=
  rfl

variable (F) in
/-- The `w`-coordinate on the additive coefficient modules. -/
def infiniteCoordinateLinear (w : InfinitePlace E) :
    (relativeIdeleRepresentation F E).V →ₗ[NormalizedTwoCocycle.CoefficientScalars.{u}]
      (infiniteLocalRepresentation F w).V where
  toFun x := Additive.ofMul (ideleInfiniteCoordinate w (@Additive.toMul (IdeleGroup (𝓞 E) E) x))
  map_add' x y := congrArg Additive.ofMul (map_mul (ideleInfiniteCoordinate w)
    (@Additive.toMul (IdeleGroup (𝓞 E) E) x) (@Additive.toMul (IdeleGroup (𝓞 E) E) y))
  map_smul' r x := congrArg Additive.ofMul (map_zpow (ideleInfiniteCoordinate w)
    (@Additive.toMul (IdeleGroup (𝓞 E) E) x) r.down)

variable (F) in
/-- The local projection `J_E → E_wˣ` (the `w`-coordinate), a morphism of representations of the
stabilizer `D_w`. -/
def infiniteLocalProjection (w : InfinitePlace E) :
    Rep.res (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype (relativeIdeleRepresentation F E) ⟶
      infiniteLocalRepresentation F w :=
  Rep.ofHom
    { toLinearMap := infiniteCoordinateLinear F w
      isIntertwining' d := by
        ext x
        exact congrArg Additive.ofMul (ideleInfiniteCoordinate_relativeIdeleAut_congr
          ((infinitePlaceEquiv_eq_self_iff _ w).2 d.2)
          (ideleInfiniteCoordinate_ofCompletion_self w _).symm) }

variable (F) in
/-- The single-coordinate embedding `E_wˣ → J_E` on the additive coefficient modules. -/
def infiniteEmbeddingLinear (w : InfinitePlace E) :
    (infiniteLocalRepresentation F w).V →ₗ[NormalizedTwoCocycle.CoefficientScalars.{u}]
      (relativeIdeleRepresentation F E).V where
  toFun y := Additive.ofMul (IdeleGroup.ofCompletion (𝓞 E) E w (@Additive.toMul (w.Completion)ˣ y))
  map_add' x y := congrArg Additive.ofMul (map_mul (IdeleGroup.ofCompletion (𝓞 E) E w)
    (@Additive.toMul (w.Completion)ˣ x) (@Additive.toMul (w.Completion)ˣ y))
  map_smul' r x := congrArg Additive.ofMul (map_zpow (IdeleGroup.ofCompletion (𝓞 E) E w)
    (@Additive.toMul (w.Completion)ˣ x) r.down)

variable (F) in
/-- The local embedding `E_wˣ → J_E` (single coordinate at `w`), a morphism of representations of
the stabilizer `D_w`. -/
def infiniteLocalEmbedding (w : InfinitePlace E) :
    infiniteLocalRepresentation F w ⟶
      Rep.res (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype (relativeIdeleRepresentation F E) :=
  Rep.ofHom
    { toLinearMap := infiniteEmbeddingLinear F w
      isIntertwining' d := by
        ext y
        exact congrArg Additive.ofMul (relativeIdeleAut_ofCompletion_of_eq
          ((infinitePlaceEquiv_eq_self_iff _ w).2 d.2) _).symm }

variable (F) in
/-- The semilocal projection `J_E ⟶ Coind(E_wˣ)` along the stabilizer of `w`,
`x ↦ (g ↦ (g • x)_w)`: the morphism adjoint to the local projection. -/
def infiniteSemilocalProjection (w : InfinitePlace E) :
    relativeIdeleRepresentation F E ⟶
      Rep.coind (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype (infiniteLocalRepresentation F w) :=
  Rep.resCoindToHom _ _ _ (infiniteLocalProjection F w)

/-- The value of the semilocal projection at `g` is the `w`-coordinate of `g • x`. -/
theorem infiniteSemilocalProjection_apply (w : InfinitePlace E)
    (x : (relativeIdeleRepresentation F E).V) (g : E ≃ₐ[F] E) :
    ((infiniteSemilocalProjection F w).hom x).1 g =
      Additive.ofMul (ideleInfiniteCoordinate w
        (relativeIdeleAut F E g (@Additive.toMul (IdeleGroup (𝓞 E) E) x))) :=
  rfl

/-- The map `Hⁿ(Gal(E/F), J_E) ⟶ Hⁿ(D_w, E_wˣ)` induced by the local projection factors through
the semilocal projection and the Shapiro map. -/
theorem map_infiniteSemilocalProjection_comp_shapiroMapOf (w : InfinitePlace E) (n : ℕ) :
    groupCohomology.map (MonoidHom.id _) (infiniteSemilocalProjection F w) n ≫
        Shapiro.shapiroMapOf (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype _ n =
      groupCohomology.map (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype
        (infiniteLocalProjection F w) n :=
  Shapiro.map_resCoindToHom_comp_shapiroMapOf _ _ n

/-- The semilocal projection at `w` determines the coordinates at all places of the orbit
of `w`. -/
theorem ideleInfiniteCoordinate_eq_of_infiniteSemilocalProjection_eq (w : InfinitePlace E)
    {x y : (relativeIdeleRepresentation F E).V}
    (h : (infiniteSemilocalProjection F w).hom x = (infiniteSemilocalProjection F w).hom y)
    (g : E ≃ₐ[F] E) :
    ideleInfiniteCoordinate (infinitePlaceEquiv g.toRingEquiv w)
        (@Additive.toMul (IdeleGroup (𝓞 E) E) x) =
      ideleInfiniteCoordinate (infinitePlaceEquiv g.toRingEquiv w)
        (@Additive.toMul (IdeleGroup (𝓞 E) E) y) := by
  have hg : ideleInfiniteCoordinate w
      (relativeIdeleAut F E g (@Additive.toMul (IdeleGroup (𝓞 E) E) x)) =
      ideleInfiniteCoordinate w
        (relativeIdeleAut F E g (@Additive.toMul (IdeleGroup (𝓞 E) E) y)) :=
    congrArg (fun f => Additive.toMul (f.1 g)) h
  exact (ideleInfiniteCoordinate_relativeIdeleAut_eq_iff g w _ _).1 hg

variable (w : InfinitePlace E)
  [Fintype ((E ≃ₐ[F] E) ⧸ (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype.range)]

variable (F) in
/-- The semilocal section `Coind(E_wˣ) ⟶ J_E` along the stabilizer of `w`: the coset sum
`f ↦ ∑_{g D_w} g • ι_w (f g⁻¹)` of the single-coordinate embedding `ι_w`. -/
def infiniteSemilocalSection :
    Rep.coind (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype (infiniteLocalRepresentation F w) ⟶
      relativeIdeleRepresentation F E :=
  Shapiro.coindSum _ (infiniteLocalEmbedding F w)

/-- The semilocal section is a section of the semilocal projection. -/
@[reassoc (attr := simp)]
theorem infiniteSemilocalSection_comp_infiniteSemilocalProjection :
    infiniteSemilocalSection F w ≫ infiniteSemilocalProjection F w = 𝟙 _ :=
  Shapiro.coindSum_comp_resCoindToHom _ _ _
    (fun a => congrArg Additive.ofMul (ideleInfiniteCoordinate_ofCompletion_self w
      (@Additive.toMul (w.Completion)ˣ a)))
    (fun g hg a => congrArg Additive.ofMul
      (ideleInfiniteCoordinate_relativeIdeleAut_ofCompletion_of_ne g
        (fun h => hg (MonoidHom.mem_range.2
          ⟨⟨g, (infinitePlaceEquiv_eq_self_iff g w).1 h⟩, rfl⟩))
        (@Additive.toMul (w.Completion)ˣ a)))

/-- The semilocal projection of the semilocal section of `β` is `β`. -/
theorem infiniteSemilocalProjection_infiniteSemilocalSection
    (β : Rep.coind (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype
      (infiniteLocalRepresentation F w)) :
    (infiniteSemilocalProjection F w).hom ((infiniteSemilocalSection F w).hom β) = β :=
  congrArg (fun φ => φ.hom β) (infiniteSemilocalSection_comp_infiniteSemilocalProjection w)

/-- Section after projection does not change the coordinates at the places of the orbit
of `w`. -/
theorem ideleInfiniteCoordinate_infiniteSemilocalSection_infiniteSemilocalProjection
    (x : (relativeIdeleRepresentation F E).V) (g : E ≃ₐ[F] E) :
    ideleInfiniteCoordinate (infinitePlaceEquiv g.toRingEquiv w)
        (@Additive.toMul (IdeleGroup (𝓞 E) E)
          ((infiniteSemilocalSection F w).hom ((infiniteSemilocalProjection F w).hom x))) =
      ideleInfiniteCoordinate (infinitePlaceEquiv g.toRingEquiv w)
        (@Additive.toMul (IdeleGroup (𝓞 E) E) x) :=
  ideleInfiniteCoordinate_eq_of_infiniteSemilocalProjection_eq w
    (infiniteSemilocalProjection_infiniteSemilocalSection w _) g

end Local

section Invariant

variable {F E : Type u} [Field F] [Field E] [NumberField E] [Algebra F E]

theorem rationalClass_half_ne_zero : rationalClass (1 / 2 : ℚ) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 ((QuotientAddGroup.eq_zero_iff _).1 h)
  rw [zsmul_eq_mul, mul_one] at hn
  have h2 : (2 * n : ℚ) = 1 := by rw [hn]; norm_num
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

/-- The idele `f(c,c) · f(1,1)`, in multiplicative notation, of a `2`-cochain with values
in `J_E`. -/
def ideleConjugationValue (c : E ≃ₐ[F] E)
    (f : (E ≃ₐ[F] E) × (E ≃ₐ[F] E) → (relativeIdeleRepresentation F E).V) :
    IdeleGroup (𝓞 E) E :=
  @Additive.toMul (IdeleGroup (𝓞 E) E) (f (c, c) + f (1, 1))

theorem ideleConjugationValue_add (c : E ≃ₐ[F] E)
    (f g : (E ≃ₐ[F] E) × (E ≃ₐ[F] E) → (relativeIdeleRepresentation F E).V) :
    ideleConjugationValue c (f + g) = ideleConjugationValue c f * ideleConjugationValue c g := by
  unfold ideleConjugationValue
  rw [Pi.add_apply, Pi.add_apply, add_add_add_comm]
  rfl

/-- For an involution `c`, the idele `f(c,c) · f(1,1)` of a `2`-cocycle is fixed by `c`. -/
theorem ideleConjugationValue_fixed
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) {c : E ≃ₐ[F] E}
    (hc : c * c = 1) :
    relativeIdeleAut F E c (ideleConjugationValue c f) = ideleConjugationValue c f := by
  have h := (groupCohomology.mem_cocycles₂_iff f).1 f.2 c c c
  rw [hc, groupCohomology.cocycles₂_map_one_fst f c, groupCohomology.cocycles₂_map_one_snd f c,
    ← map_add ((relativeIdeleRepresentation F E).ρ c), add_comm (f (1, 1))] at h
  exact (congrArg (fun y : (relativeIdeleRepresentation F E).V =>
    @Additive.toMul (IdeleGroup (𝓞 E) E) y) h).symm

/-- At the complex conjugation `c` of `w`, the complex value of the `w`-coordinate of
`f(c,c) · f(1,1)` is real for a `2`-cocycle `f`. -/
theorem extensionEmbedding_ideleConjugationValue_im (w : InfinitePlace E)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) {c : E ≃ₐ[F] E}
    (hc : ComplexEmbedding.IsConj w.embedding c) :
    (InfinitePlace.Completion.extensionEmbedding w
      (ideleInfiniteCoordinate w (ideleConjugationValue c f))).im = 0 := by
  have h := extensionEmbedding_ideleInfiniteCoordinate_of_isConj hc (ideleConjugationValue c f)
  rw [ideleConjugationValue_fixed f (conjugation_mul_self w hc)] at h
  have h2 := congrArg Complex.im h
  rw [Complex.star_def, Complex.conj_im] at h2
  linarith

variable (F) in
open Classical in
/-- The archimedean invariant at the infinite place `w` of a `2`-cocycle of `J_E`: `0` unless
some nontrivial `c ∈ Gal(E/F)` fixes `w`, in which case it is the sign class of the complex
value of the `w`-coordinate of `f(c,c) · f(1,1)`, for the chosen such `c` (the complex
conjugation of `w`). -/
def archimedeanIdeleCocycleHom (w : InfinitePlace E) :
    groupCohomology.cocycles₂ (relativeIdeleRepresentation F E) →+ RationalModIntegers where
  toFun f :=
    if h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1 then
      signClass (InfinitePlace.Completion.extensionEmbedding w
        (ideleInfiniteCoordinate w (ideleConjugationValue h.choose f)))
    else 0
  map_zero' := by
    split_ifs with h
    · have : ideleConjugationValue h.choose
          ⇑(0 : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) = 1 := by
        unfold ideleConjugationValue
        rw [show ⇑(0 : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) = 0 from rfl,
          Pi.zero_apply, Pi.zero_apply, add_zero]
        rfl
      rw [this, map_one, Units.val_one, map_one]
      simp [signClass]
    · rfl
  map_add' f g := by
    split_ifs with h
    · have hc := isConj_of_mem_stabilizer w h.choose_spec.1 h.choose_spec.2
      rw [show ⇑(f + g) = ⇑f + ⇑g from rfl, ideleConjugationValue_add, map_mul, Units.val_mul,
        map_mul]
      exact signClass_mul (extensionEmbedding_ideleConjugationValue_im w f hc)
        (extensionEmbedding_ideleConjugationValue_im w g hc)
        ((map_ne_zero _).2 (Units.ne_zero _)) ((map_ne_zero _).2 (Units.ne_zero _))
    · rw [add_zero]

open Classical in
/-- The value of the archimedean cocycle invariant when some nontrivial `c` fixes `w`. -/
theorem archimedeanIdeleCocycleHom_apply_of_exists {w : InfinitePlace E}
    (h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) :
    archimedeanIdeleCocycleHom F w f =
      signClass (InfinitePlace.Completion.extensionEmbedding w
        (ideleInfiniteCoordinate w (ideleConjugationValue h.choose f))) := by
  change dite _ _ _ = _
  split_ifs
  rfl

open Classical in
/-- The archimedean cocycle invariant vanishes when only the identity fixes `w`. -/
theorem archimedeanIdeleCocycleHom_apply_of_not_exists {w : InfinitePlace E}
    (h : ¬∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) :
    archimedeanIdeleCocycleHom F w f = 0 := by
  change dite _ _ _ = _
  split_ifs
  rfl

/-- The archimedean cocycle invariant vanishes on coboundaries. -/
theorem archimedeanIdeleCocycleHom_coboundary (w : InfinitePlace E)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E))
    (hf : ⇑f ∈ groupCohomology.coboundaries₂ (relativeIdeleRepresentation F E)) :
    archimedeanIdeleCocycleHom F w f = 0 := by
  obtain ⟨b, hb⟩ := hf
  by_cases h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1
  · rw [archimedeanIdeleCocycleHom_apply_of_exists h]
    have hc := isConj_of_mem_stabilizer w h.choose_spec.1 h.choose_spec.2
    have hcc := conjugation_mul_self w hc
    have hsum : f (h.choose, h.choose) + f (1, 1) =
        (relativeIdeleRepresentation F E).ρ h.choose (b h.choose) + b h.choose := by
      rw [← congrFun hb (h.choose, h.choose), ← congrFun hb (1, 1)]
      change ((relativeIdeleRepresentation F E).ρ h.choose (b h.choose) -
          b (h.choose * h.choose) + b h.choose) +
          ((relativeIdeleRepresentation F E).ρ 1 (b 1) - b (1 * 1) + b 1) = _
      rw [hcc, mul_one, map_one, Module.End.one_apply]
      abel
    have hval : ideleConjugationValue h.choose f =
        relativeIdeleAut F E h.choose (@Additive.toMul (IdeleGroup (𝓞 E) E) (b h.choose)) *
          @Additive.toMul (IdeleGroup (𝓞 E) E) (b h.choose) := by
      unfold ideleConjugationValue
      rw [hsum]
      rfl
    rw [hval, map_mul, Units.val_mul, map_mul, extensionEmbedding_ideleInfiniteCoordinate_of_isConj hc]
    exact signClass_star_mul_self _
  · exact archimedeanIdeleCocycleHom_apply_of_not_exists h f

variable (F) in
/-- The archimedean local invariant at the infinite place `w` of a class in
`H²(Gal(E/F), J_E)`. -/
def archimedeanIdeleInvariant (w : InfinitePlace E) :
    relativeIdeleCohomology F E 2 →+ RationalModIntegers :=
  H2Lift (archimedeanIdeleCocycleHom F w) (archimedeanIdeleCocycleHom_coboundary w)

theorem archimedeanIdeleInvariant_H2π (w : InfinitePlace E)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) :
    archimedeanIdeleInvariant F w (groupCohomology.H2π _ f) = archimedeanIdeleCocycleHom F w f :=
  H2Lift_H2π _ _ f

/-- The `2`-cochain `f(c,c) · f(1,1)` of the principal image of a `2`-cocycle of `Eˣ` is the
principal idele of `f(c,c) · f(1,1)`. -/
theorem ideleConjugationValue_principalIdeleCocycles₂ (c : E ≃ₐ[F] E)
    (z : groupCohomology.cocycles₂ (unitsRepresentation F E)) :
    ideleConjugationValue c (principalIdeleCocycles₂ F E z) =
      IdeleGroup.unitEmbedding (𝓞 E) E (conjugationValue c z) := by
  change IdeleGroup.unitEmbedding (𝓞 E) E (@Additive.toMul Eˣ (z (c, c))) *
      IdeleGroup.unitEmbedding (𝓞 E) E (@Additive.toMul Eˣ (z (1, 1))) =
    IdeleGroup.unitEmbedding (𝓞 E) E
      (@Additive.toMul Eˣ (z (c, c)) * @Additive.toMul Eˣ (z (1, 1)))
  exact (map_mul _ _ _).symm

/-- The archimedean invariant of the image of a class of `H²(Gal(E/F), Eˣ)` in
`H²(Gal(E/F), J_E)` is its archimedean invariant `archimedeanInvariant w`. -/
theorem archimedeanIdeleInvariant_principalIdeleCohomologyMap (w : InfinitePlace E)
    (x : relativeCohomology F E 2) :
    archimedeanIdeleInvariant F w (principalIdeleCohomologyMap F E 2 x) =
      archimedeanInvariant w x := by
  obtain ⟨z, rfl⟩ := H2π_surjective x
  rw [principalIdeleCohomologyMap_H2π, archimedeanIdeleInvariant_H2π, archimedeanInvariant,
    H2Lift_H2π]
  by_cases h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1
  · rw [archimedeanIdeleCocycleHom_apply_of_exists h]
    classical
    change _ = (if h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1 then
      signClass (w.embedding (conjugationValue h.choose z : E)) else 0)
    split_ifs
    rw [ideleConjugationValue_principalIdeleCocycles₂, ideleInfiniteCoordinate_unitEmbedding,
      extensionEmbedding_algebraMap]
  · rw [archimedeanIdeleCocycleHom_apply_of_not_exists h]
    classical
    change _ = (if h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1 then
      signClass (w.embedding (conjugationValue h.choose z : E)) else 0)
    split_ifs
    rfl

end Invariant

section Primitive

variable {F E : Type u} [Field F] [Field E] [NumberField E] [Algebra F E]

/-- If the archimedean invariant at `w` of a 2-cocycle `f` of `J_E` vanishes, then the
restriction of `f` to the stabilizer `D_w`, followed by the `w`-coordinate, is the coboundary of
a cochain with values in `E_wˣ`. -/
theorem exists_d₁₂_eq_infiniteLocalProjection (w : InfinitePlace E)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E))
    (hf : archimedeanIdeleCocycleHom F w f = 0) :
    ∃ β : MulAction.stabilizer (E ≃ₐ[F] E) w → (infiniteLocalRepresentation F w).V,
      ∀ d d' : MulAction.stabilizer (E ≃ₐ[F] E) w,
        (groupCohomology.d₁₂ (infiniteLocalRepresentation F w)).hom β (d, d') =
          (infiniteLocalProjection F w).hom (f ((d : E ≃ₐ[F] E), (d' : E ≃ₐ[F] E))) := by
  have h1fst : ∀ d : MulAction.stabilizer (E ≃ₐ[F] E) w,
      (infiniteLocalProjection F w).hom (f (1, (d : E ≃ₐ[F] E))) =
        (infiniteLocalProjection F w).hom (f (1, 1)) := fun d => by
    rw [groupCohomology.cocycles₂_map_one_fst]
  have h1snd : ∀ d : MulAction.stabilizer (E ≃ₐ[F] E) w,
      (infiniteLocalProjection F w).hom (f ((d : E ≃ₐ[F] E), 1)) =
        (infiniteLocalRepresentation F w).ρ d ((infiniteLocalProjection F w).hom (f (1, 1))) :=
    fun d => by
      rw [groupCohomology.cocycles₂_map_one_snd]
      exact Rep.hom_comm_apply (infiniteLocalProjection F w) d (f (1, 1))
  by_cases h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1
  · classical
    rw [archimedeanIdeleCocycleHom_apply_of_exists h] at hf
    obtain ⟨hcS, hc1⟩ := h.choose_spec
    set c := h.choose with hcdef
    have hc := isConj_of_mem_stabilizer w hcS hc1
    have hcc := conjugation_mul_self w hc
    let c' : MulAction.stabilizer (E ≃ₐ[F] E) w := ⟨c, hcS⟩
    have hc'1 : c' ≠ 1 := fun h' => hc1 (congrArg Subtype.val h')
    have hc'c' : c' * c' = 1 := Subtype.ext hcc
    have hS : ∀ d : MulAction.stabilizer (E ≃ₐ[F] E) w, d = 1 ∨ d = c' := by
      intro d
      have hd : (d : E ≃ₐ[F] E) ∈ MulAction.stabilizer (E ≃ₐ[F] E)
          (InfinitePlace.mk w.embedding) := by
        rw [w.mk_embedding]
        exact d.2
      rw [InfinitePlace.mem_stabilizer_mk_iff] at hd
      rcases hd with hd | hd
      · exact Or.inl (Subtype.ext hd)
      · exact Or.inr (Subtype.ext (hd.ext hc))
    set y := ideleInfiniteCoordinate w (ideleConjugationValue c f) with hy
    have him : (InfinitePlace.Completion.extensionEmbedding w y).im = 0 :=
      extensionEmbedding_ideleConjugationValue_im w f hc
    have hne : InfinitePlace.Completion.extensionEmbedding w y ≠ 0 :=
      (map_ne_zero _).2 (Units.ne_zero _)
    have hre : 0 < (InfinitePlace.Completion.extensionEmbedding w y).re := by
      rcases lt_trichotomy (InfinitePlace.Completion.extensionEmbedding w y).re 0 with
        hlt | heq | hgt
      · simp only [signClass, hlt, ↓reduceIte] at hf
        exact absurd hf rationalClass_half_ne_zero
      · exact absurd (Complex.ext (by simpa using heq) (by simpa using him)) hne
      · exact hgt
    have hw : InfinitePlace.IsComplex w :=
      InfinitePlace.isComplex_iff.2 ((ComplexEmbedding.isConj_ne_one_iff hc).1 hc1)
    obtain ⟨s₀, hs₀⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw
      ((Real.sqrt (InfinitePlace.Completion.extensionEmbedding w y).re : ℝ) : ℂ)
    have hs₀ne : s₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hs₀
      have h0 := congrArg Complex.re hs₀
      rw [Complex.zero_re, Complex.ofReal_re] at h0
      exact (Real.sqrt_pos.2 hre).ne h0
    let s : (w.Completion)ˣ := Units.mk0 s₀ hs₀ne
    let s' : (infiniteLocalRepresentation F w).V := Additive.ofMul s
    have hsq : s * s = y := by
      apply Units.ext
      apply (InfinitePlace.Completion.extensionEmbedding w).injective
      rw [Units.val_mul, map_mul, Units.val_mk0, hs₀, ← Complex.ofReal_mul,
        Real.mul_self_sqrt hre.le]
      exact Complex.ext (by simp) (by simp [him])
    have hfix : (infiniteLocalRepresentation F w).ρ c' s' = s' := by
      change Additive.ofMul (ideleInfiniteCoordinate w
        (relativeIdeleAut F E c (IdeleGroup.ofCompletion (𝓞 E) E w s))) = Additive.ofMul s
      congr 1
      apply Units.ext
      apply (InfinitePlace.Completion.extensionEmbedding w).injective
      rw [extensionEmbedding_ideleInfiniteCoordinate_of_isConj hc,
        ideleInfiniteCoordinate_ofCompletion_self]
      change star (InfinitePlace.Completion.extensionEmbedding w s₀) =
        InfinitePlace.Completion.extensionEmbedding w s₀
      rw [hs₀]
      exact Complex.conj_ofReal _
    have hkey : s' + s' = (infiniteLocalProjection F w).hom (f (c, c)) +
        (infiniteLocalProjection F w).hom (f (1, 1)) := by
      change Additive.ofMul (s * s) = Additive.ofMul
        (ideleInfiniteCoordinate w (@Additive.toMul (IdeleGroup (𝓞 E) E) (f (c, c))) *
          ideleInfiniteCoordinate w (@Additive.toMul (IdeleGroup (𝓞 E) E) (f (1, 1))))
      rw [hsq, ← map_mul]
      rfl
    let a := (infiniteLocalProjection F w).hom (f (1, 1))
    let β : MulAction.stabilizer (E ≃ₐ[F] E) w → (infiniteLocalRepresentation F w).V :=
      fun d => if d = 1 then a else s'
    have hβ1 : β 1 = a := by simp [β]
    have hβc : β c' = s' := by simp [β, hc'1]
    refine ⟨β, fun d d' => ?_⟩
    rw [groupCohomology.d₁₂_hom_apply]
    rcases hS d with rfl | rfl <;> rcases hS d' with rfl | rfl
    · rw [mul_one, hβ1, map_one, Module.End.one_apply, sub_add_cancel]
      rfl
    · rw [one_mul, map_one, Module.End.one_apply, sub_self, zero_add, hβ1]
      exact (h1fst c').symm
    · rw [mul_one, sub_add_cancel, hβ1]
      exact (h1snd c').symm
    · rw [hc'c', hβ1, hβc, hfix, sub_add_eq_add_sub, hkey, add_sub_cancel_right]
  · have h1 : ∀ d : MulAction.stabilizer (E ≃ₐ[F] E) w, d = 1 := fun d =>
      by_contra fun hd => h ⟨d, d.2, fun h' => hd (Subtype.ext h')⟩
    refine ⟨fun _ => (infiniteLocalProjection F w).hom (f (1, 1)), fun d d' => ?_⟩
    rw [h1 d, h1 d', groupCohomology.d₁₂_hom_apply]
    simp

/-- If the archimedean invariant at `w` of a 2-cocycle `f` of `J_E` vanishes, then the semilocal
projection of `f` at `w` is the coboundary of a cochain with values in `Coind(E_wˣ)`. -/
theorem exists_d₁₂_eq_infiniteSemilocalProjection (w : InfinitePlace E)
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E))
    (hf : archimedeanIdeleCocycleHom F w f = 0) :
    ∃ β : (E ≃ₐ[F] E) → Rep.coind (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype
        (infiniteLocalRepresentation F w),
      ∀ g h, (groupCohomology.d₁₂ _).hom β (g, h) =
        (infiniteSemilocalProjection F w).hom (f (g, h)) := by
  obtain ⟨β₀, hβ₀⟩ := exists_d₁₂_eq_infiniteLocalProjection w f hf
  have hinj : Function.Injective (Shapiro.shapiroMapOf
      (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype (infiniteLocalRepresentation F w) 2) := by
    have := Shapiro.isIso_shapiroMapOf (Subgroup.subtype_injective _)
      (infiniteLocalRepresentation F w) 2
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  have h1 : groupCohomology.map (MonoidHom.id _) (infiniteSemilocalProjection F w) 2
      (groupCohomology.H2π _ f) = 0 := by
    apply hinj
    rw [map_zero, ← ConcreteCategory.comp_apply, map_infiniteSemilocalProjection_comp_shapiroMapOf,
      groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_eq_zero_iff]
    exact ⟨β₀, funext fun x => hβ₀ x.1 x.2⟩
  rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_eq_zero_iff] at h1
  obtain ⟨β, hβ⟩ := h1
  exact ⟨β, fun g h => congrFun hβ (g, h)⟩

/-- Let `β` be a primitive of the semilocal projection at `w` of a 2-cocycle `f`, and let `b` be
a cochain of `J_E` whose coordinates at the places of the orbit of `w` are those of the
semilocal sections of `β`. Then the coboundary of `b` and `f` have the same coordinates at the
places of the orbit of `w`. -/
theorem ideleInfiniteCoordinate_d₁₂_eq (w : InfinitePlace E)
    [Fintype ((E ≃ₐ[F] E) ⧸ (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype.range)]
    (f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E))
    (β : (E ≃ₐ[F] E) → Rep.coind (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype
        (infiniteLocalRepresentation F w))
    (hβ : ∀ g h, (groupCohomology.d₁₂ _).hom β (g, h) =
        (infiniteSemilocalProjection F w).hom (f (g, h)))
    (b : (E ≃ₐ[F] E) → (relativeIdeleRepresentation F E).V)
    (hb : ∀ k l : E ≃ₐ[F] E, ideleInfiniteCoordinate (infinitePlaceEquiv l.toRingEquiv w)
        (@Additive.toMul (IdeleGroup (𝓞 E) E) (b k)) =
      ideleInfiniteCoordinate (infinitePlaceEquiv l.toRingEquiv w)
        (@Additive.toMul (IdeleGroup (𝓞 E) E) ((infiniteSemilocalSection F w).hom (β k))))
    (g h l : E ≃ₐ[F] E) :
    ideleInfiniteCoordinate (infinitePlaceEquiv l.toRingEquiv w)
        (@Additive.toMul (IdeleGroup (𝓞 E) E) ((groupCohomology.d₁₂ _).hom b (g, h))) =
      ideleInfiniteCoordinate (infinitePlaceEquiv l.toRingEquiv w)
        (@Additive.toMul (IdeleGroup (𝓞 E) E) (f (g, h))) := by
  have hβ' := hβ g h
  rw [groupCohomology.d₁₂_hom_apply] at hβ'
  have hρ : infiniteCoordinateLinear F (infinitePlaceEquiv l.toRingEquiv w)
      ((relativeIdeleRepresentation F E).ρ g (b h)) =
      infiniteCoordinateLinear F (infinitePlaceEquiv l.toRingEquiv w)
        ((relativeIdeleRepresentation F E).ρ g ((infiniteSemilocalSection F w).hom (β h))) :=
    congrArg Additive.ofMul ((ideleInfiniteCoordinate_relativeIdeleAut_eq_iff g _ _ _).2
      (ideleInfiniteCoordinate_congr (infinitePlaceEquiv_mul l g w).symm (hb h (l * g))))
  have hb' : ∀ k, infiniteCoordinateLinear F (infinitePlaceEquiv l.toRingEquiv w) (b k) =
      infiniteCoordinateLinear F (infinitePlaceEquiv l.toRingEquiv w)
        ((infiniteSemilocalSection F w).hom (β k)) :=
    fun k => congrArg Additive.ofMul (hb k l)
  have key : (infiniteSemilocalSection F w).hom
      ((Rep.coind (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype
        (infiniteLocalRepresentation F w)).ρ g (β h) - β (g * h) + β g) =
      (relativeIdeleRepresentation F E).ρ g ((infiniteSemilocalSection F w).hom (β h)) -
        (infiniteSemilocalSection F w).hom (β (g * h)) +
          (infiniteSemilocalSection F w).hom (β g) := by
    rw [map_add, map_sub, Rep.hom_comm_apply]
  apply Additive.ofMul.injective
  change infiniteCoordinateLinear F (infinitePlaceEquiv l.toRingEquiv w)
      ((groupCohomology.d₁₂ _).hom b (g, h)) =
    infiniteCoordinateLinear F (infinitePlaceEquiv l.toRingEquiv w) (f (g, h))
  rw [groupCohomology.d₁₂_hom_apply, map_add, map_sub, hρ, hb', hb', ← map_sub, ← map_add,
    ← key, hβ']
  exact congrArg Additive.ofMul
    (ideleInfiniteCoordinate_infiniteSemilocalSection_infiniteSemilocalProjection w (f (g, h)) l)

end Primitive

section Criterion

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- **Vanishing of the archimedean invariants.** A class `c ∈ H²(Gal(E/F), J_E)` has
archimedean invariant `0` at every infinite place of `E` iff it is the class of a 2-cocycle all
of whose values have infinite adele part `1`. -/
theorem archimedeanIdeleInvariant_eq_zero_iff (c : relativeIdeleCohomology F E 2) :
    (∀ w, archimedeanIdeleInvariant F w c = 0) ↔
      ∃ f : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E),
        groupCohomology.H2π _ f = c ∧
          ∀ x, ((@Additive.toMul (IdeleGroup (𝓞 E) E) (f x) : IdeleGroup (𝓞 E) E) :
            AdeleRing (𝓞 E) E).1 = 1 := by
  constructor
  · intro hc
    classical
    obtain ⟨f, rfl⟩ := H2π_surjective c
    let hfint : ∀ w : InfinitePlace E,
        Fintype ((E ≃ₐ[F] E) ⧸ (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype.range) :=
      fun w => Fintype.ofFinite _
    have hβ := fun w : InfinitePlace E => exists_d₁₂_eq_infiniteSemilocalProjection w f
      ((archimedeanIdeleInvariant_H2π w f).symm.trans (hc w))
    choose β hβd using hβ
    let r : InfinitePlace E → InfinitePlace E := fun u =>
      (@Quotient.mk'' _ (MulAction.orbitRel (E ≃ₐ[F] E) (InfinitePlace E)) u).out
    have hr : ∀ u, ∃ l : E ≃ₐ[F] E, infinitePlaceEquiv l.toRingEquiv (r u) = u := by
      intro u
      obtain ⟨l, hl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1
        (Quotient.mk_out' (s₁ := MulAction.orbitRel (E ≃ₐ[F] E) (InfinitePlace E)) u))
      refine ⟨l, ?_⟩
      rw [infinitePlaceEquiv_eq_inv_smul]
      change l⁻¹ • (@Quotient.mk'' _ (MulAction.orbitRel (E ≃ₐ[F] E) (InfinitePlace E)) u).out = u
      rw [← hl, inv_smul_smul]
    have hrg : ∀ (l : E ≃ₐ[F] E) p, r (infinitePlaceEquiv l.toRingEquiv p) = r p := by
      intro l p
      refine congrArg Quotient.out (Quotient.sound' ?_)
      rw [infinitePlaceEquiv_eq_inv_smul]
      exact MulAction.mem_orbit p l⁻¹
    have hrr : ∀ u, r (r u) = r u := fun u =>
      congrArg Quotient.out (Quotient.out_eq' _)
    let b : (E ≃ₐ[F] E) → (relativeIdeleRepresentation F E).V := fun k =>
      Additive.ofMul (ideleOfInfiniteCoordinates fun u => ideleInfiniteCoordinate u
        (@Additive.toMul (IdeleGroup (𝓞 E) E)
          ((infiniteSemilocalSection F (r u)).hom (β (r u) k))))
    have hglue : ∀ x u, ideleInfiniteCoordinate u
        (@Additive.toMul (IdeleGroup (𝓞 E) E) ((groupCohomology.d₁₂ _).hom b x)) =
        ideleInfiniteCoordinate u (@Additive.toMul (IdeleGroup (𝓞 E) E) (f x)) := by
      rintro ⟨g, h⟩ u
      obtain ⟨l, hl⟩ := hr u
      refine ideleInfiniteCoordinate_congr hl.symm
        (ideleInfiniteCoordinate_d₁₂_eq (r u) f (β (r u)) (hβd (r u)) b ?_ g h l)
      intro k l'
      have key : ∀ p, p = r u →
          ideleInfiniteCoordinate (infinitePlaceEquiv l'.toRingEquiv (r u))
            (@Additive.toMul (IdeleGroup (𝓞 E) E) ((infiniteSemilocalSection F p).hom (β p k))) =
          ideleInfiniteCoordinate (infinitePlaceEquiv l'.toRingEquiv (r u))
            (@Additive.toMul (IdeleGroup (𝓞 E) E)
              ((infiniteSemilocalSection F (r u)).hom (β (r u) k))) := by
        rintro _ rfl
        rfl
      change ideleInfiniteCoordinate _ (ideleOfInfiniteCoordinates _) = _
      rw [ideleInfiniteCoordinate_ideleOfInfiniteCoordinates]
      exact key _ ((hrg l' (r u)).trans (hrr u))
    refine ⟨f - ⟨(groupCohomology.d₁₂ _).hom b, groupCohomology.d₁₂_apply_mem_cocycles₂ b⟩,
      ?_, fun x => ?_⟩
    · rw [map_sub, sub_eq_self, groupCohomology.H2π_eq_zero_iff]
      exact ⟨b, rfl⟩
    · rw [ideleInfinite_eq_one_iff]
      intro u
      change ideleInfiniteCoordinate u (@Additive.toMul (IdeleGroup (𝓞 E) E) (f x) /
        @Additive.toMul (IdeleGroup (𝓞 E) E) ((groupCohomology.d₁₂ _).hom b x)) = 1
      rw [map_div, hglue x u, div_self']
  · rintro ⟨f, rfl, hf⟩ w
    rw [archimedeanIdeleInvariant_H2π]
    by_cases h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1
    · rw [archimedeanIdeleCocycleHom_apply_of_exists h]
      have h1 : ideleInfiniteCoordinate w (ideleConjugationValue h.choose f) = 1 := by
        change ideleInfiniteCoordinate w
          (@Additive.toMul (IdeleGroup (𝓞 E) E) (f (h.choose, h.choose)) *
            @Additive.toMul (IdeleGroup (𝓞 E) E) (f (1, 1))) = 1
        rw [map_mul, (ideleInfinite_eq_one_iff _).1 (hf _) w,
          (ideleInfinite_eq_one_iff _).1 (hf _) w, mul_one]
      rw [h1, Units.val_one, map_one]
      simp [signClass]
    · exact archimedeanIdeleCocycleHom_apply_of_not_exists h f

end Criterion

end Langlands.ClassField.Global

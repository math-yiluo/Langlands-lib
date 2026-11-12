import Langlands.Sheaf.Renard.CompatibleTestActions
import Langlands.Topology.LocallyProfinite
import Mathlib.RepresentationTheory.Coinvariants

/-!
# The test module of coinvariants along an invariant map

Renard III.3.1, printed p.83 / PDF p.89 (9 July 2026).
The module carrier and quotient map are the original representation coinvariants.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.CoinvariantTestModule

open CategoryTheory Langlands.Algebra Langlands.HarmonicAnalysis
open PointwiseTestAlgebra CompatibleTestActions
open Langlands.Topology

universe uG uX uY uM

variable {G : Type uG} [Group G]
variable {X : Type uX} [TopologicalSpace X] [MulAction G X]
variable [ContinuousConstSMul G X]
variable {Y : Type uY} [TopologicalSpace Y]

attribute [local instance] CompatibleTestAction.complexModule

local instance smoothModule (M : CompatibleTestAction.{uG, uX, uM} G X) :
    Module (LocallyConstant X ℂ) M.module.obj :=
  PointwiseTestModule.module M.module.property

/-- A test on the target pulls back to a smooth multiplier, without a support claim. -/
def pullback (q : C(X, Y)) (f : Carrier Y) : LocallyConstant X ℂ :=
  f.val.comap q

@[simp]
theorem pullback_apply (q : C(X, Y)) (f : Carrier Y) (x : X) :
    pullback q f x = f (q x) := rfl

/-- Smooth multiplication is linear for the original canonical complex scalars. -/
def smoothLinear (M : CompatibleTestAction.{uG, uX, uM} G X)
    (f : LocallyConstant X ℂ) : M.module.obj →ₗ[ℂ] M.module.obj where
  toFun m := f • m
  map_add' := smul_add f
  map_smul' c m := by
    change f • (c • m) = c • (f • m)
    rw [← PointwiseTestModule.const_smul M.module.property c m,
      ← PointwiseTestModule.const_smul M.module.property c (f • m)]
    exact smul_comm f (LocallyConstant.const X c) m

/-- Pullback multiplication on the unchanged original module carrier. -/
abbrev multiplier (q : C(X, Y)) (M : CompatibleTestAction.{uG, uX, uM} G X)
    (f : Carrier Y) : M.module.obj →ₗ[ℂ] M.module.obj :=
  smoothLinear M (pullback q f)

/-- The target test action before taking coinvariants. -/
abbrev pullbackModule (q : C(X, Y)) (M : CompatibleTestAction.{uG, uX, uM} G X) :
    NonUnitalModule (Carrier Y) M.module.obj where
  smul f m := pullback q f • m
  smul_zero f := smul_zero (pullback q f)
  smul_add f m n := smul_add (pullback q f) m n
  mul_smul f h m := by
    change pullback q (f * h) • m = pullback q f • (pullback q h • m)
    have hh : pullback q (f * h) = pullback q f * pullback q h := by ext x; rfl
    rw [hh, mul_smul]
  add_smul f h m := by
    change pullback q (f + h) • m = pullback q f • m + pullback q h • m
    have hh : pullback q (f + h) = pullback q f + pullback q h := by ext x; rfl
    rw [hh, add_smul]
  zero_smul m := by
    change pullback q (0 : Carrier Y) • m = 0
    have hh : pullback q (0 : Carrier Y) = 0 := by ext x; rfl
    rw [hh, zero_smul]

/-- Invariant pulled-back multipliers commute with the original group action. -/
theorem action_multiplier (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (M : CompatibleTestAction.{uG, uX, uM} G X)
    (g : G) (f : Carrier Y) (m : M.module.obj) :
    M.action g (multiplier q M f m) = multiplier q M f (M.action g m) := by
  obtain ⟨e, he⟩ := M.module.property m
  have ht : testRepresentation g (pullback q f • (e : Carrier X)) =
      pullback q f • testRepresentation g (e : Carrier X) := by
    ext x
    change f (q (g⁻¹ • x)) * (e : Carrier X) (g⁻¹ • x) =
      f (q x) * (e : Carrier X) (g⁻¹ • x)
    rw [hq]
  have hge : testRepresentation g (e : Carrier X) • M.action g m = M.action g m :=
    (M.compatible g e m).symm.trans (congrArg (M.action g) he)
  change M.action g (pullback q f • m) = pullback q f • M.action g m
  rw [NondegenerateScalars.smul_eq (LocallyConstant X ℂ) isIdempotented
    M.module.property (pullback q f) m e he, M.compatible, ht]
  exact (PointwiseTestModule.smul_action M.module.property (pullback q f)
    (testRepresentation g e) (M.action g m)).symm.trans (congrArg (pullback q f • ·) hge)

/-- A compact set in a locally profinite space is contained in a compact open. -/
theorem exists_compactOpen_superset (hY : IsLocallyProfinite Y)
    (K : Set Y) (hK : IsCompact K) :
    ∃ V : Set Y, IsClopen V ∧ IsCompact V ∧ K ⊆ V := by
  classical
  let _ : T2Space Y := hY.t2Space
  have hl (x : K) : ∃ V : Set Y, x.val ∈ V ∧ IsOpen V ∧ IsCompact V :=
    by
      obtain ⟨V, hxV, hVo, hVc, _⟩ :=
        hY.2 x.val Set.univ (by simp)
      exact ⟨V, hxV, hVo, hVc⟩
  choose V hxV hVo hVc using hl
  have hKV : K ⊆ ⋃ x : K, V x :=
    fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover V hVo hKV
  have hc : IsCompact (⋃ x ∈ S, V x) := S.isCompact_biUnion (fun x _ => hVc x)
  refine ⟨⋃ x ∈ S, V x, ⟨hc.isClosed, isOpen_biUnion (fun x _ => hVo x)⟩, hc, hS⟩

/-- Pullback of target tests acts nondegenerately on the original carrier. -/
theorem pullback_nondegenerate (q : C(X, Y)) (hY : IsLocallyProfinite Y)
    (M : CompatibleTestAction.{uG, uX, uM} G X) :
    letI := pullbackModule q M
    IsNondegenerate (Carrier Y) M.module.obj := by
  let _ := pullbackModule q M
  intro m
  obtain ⟨U, hU, hUc, hm⟩ :=
    PointwiseTestModule.exists_characteristic_fixer M.module.property m
  obtain ⟨V, hV, hVc, hUV⟩ :=
    exists_compactOpen_superset hY (q '' U) (hUc.image q.continuous)
  refine ⟨characteristicIdempotent hV hVc, ?_⟩
  change pullback q (characteristic hV hVc) • m = m
  have hh : pullback q (characteristic hV hVc) • characteristic hU hUc =
      characteristic hU hUc := by
    ext x
    by_cases hx : x ∈ U
    · have hqx : q x ∈ V := hUV ⟨x, hx, rfl⟩
      simp [pullback, characteristic_apply, hx, hqx]
    · simp [pullback, characteristic_apply, hx]
  exact (PointwiseTestModule.smul_eq M.module.property _ m hU hUc hm).trans
    ((congrArg (· • m) hh).trans hm)

/-- Multiplication of target tests composes the original multipliers. -/
theorem multiplier_mul (q : C(X, Y)) (M : CompatibleTestAction.{uG, uX, uM} G X)
    (f h : Carrier Y) (m : M.module.obj) :
    multiplier q M (f * h) m = multiplier q M f (multiplier q M h m) := by
  let _ := pullbackModule q M
  exact mul_smul f h m

theorem multiplier_add (q : C(X, Y)) (M : CompatibleTestAction.{uG, uX, uM} G X)
    (f h : Carrier Y) (m : M.module.obj) :
    multiplier q M (f + h) m = multiplier q M f m + multiplier q M h m := by
  let _ := pullbackModule q M
  exact NonUnitalModule.add_smul f h m

theorem multiplier_zero (q : C(X, Y)) (M : CompatibleTestAction.{uG, uX, uM} G X)
    (m : M.module.obj) : multiplier q M (0 : Carrier Y) m = 0 := by
  let _ := pullbackModule q M
  exact NonUnitalModule.zero_smul (A := Carrier Y) m

/-- Target scalar multiplication retains the original complex structure. -/
theorem multiplier_smul (q : C(X, Y)) (M : CompatibleTestAction.{uG, uX, uM} G X)
    (c : ℂ) (f : Carrier Y) (m : M.module.obj) :
    multiplier q M (c • f) m = c • multiplier q M f m := by
  change pullback q (c • f) • m = c • (pullback q f • m)
  have hh : pullback q (c • f) = LocallyConstant.const X c * pullback q f := by
    ext x
    rfl
  rw [hh]
  exact (mul_smul (LocallyConstant.const X c) (pullback q f) m).trans
    (PointwiseTestModule.const_smul M.module.property c (pullback q f • m))

/-- The target-test action preserves the original module's complex scalar tower. -/
theorem pullback_scalarTower (q : C(X, Y))
    (M : CompatibleTestAction.{uG, uX, uM} G X) :
    letI := pullbackModule q M
    IsScalarTower ℂ (Carrier Y) M.module.obj := by
  let _ := pullbackModule q M
  exact ⟨multiplier_smul q M⟩

/-- Recovering complex scalars from target tests preserves the original scalars. -/
theorem pullback_canonicalComplex_eq (q : C(X, Y)) (hY : IsLocallyProfinite Y)
    (M : CompatibleTestAction.{uG, uX, uM} G X) :
    letI := pullbackModule q M
    NondegenerateScalars.module ℂ isIdempotented (pullback_nondegenerate q hY M) =
      M.complexModule := by
  let _ := pullbackModule q M
  let _ := pullback_scalarTower q M
  exact NondegenerateScalars.module_eq_of_compatible ℂ isIdempotented
    (pullback_nondegenerate q hY M)

/-- Each pulled-back multiplier preserves the actual coinvariant kernel. -/
theorem multiplier_preserves_ker (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (M : CompatibleTestAction.{uG, uX, uM} G X) (f : Carrier Y) :
    Representation.Coinvariants.ker M.action ≤
      (Representation.Coinvariants.ker M.action).comap (multiplier q M f) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, m⟩, rfl⟩
  change multiplier q M f (M.action g m - m) ∈ Representation.Coinvariants.ker M.action
  rw [map_sub, ← action_multiplier q hq M g f m]
  exact Representation.Coinvariants.sub_mem_ker g (multiplier q M f m)

/-- The actual multiplier descended to the existing complex coinvariant quotient. -/
def quotientMultiplier (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (M : CompatibleTestAction.{uG, uX, uM} G X) (f : Carrier Y) :
    Representation.Coinvariants M.action →ₗ[ℂ] Representation.Coinvariants M.action :=
  (Representation.Coinvariants.ker M.action).mapQ
    (Representation.Coinvariants.ker M.action) (multiplier q M f)
    (multiplier_preserves_ker q hq M f)

@[simp]
theorem quotientMultiplier_mk (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (M : CompatibleTestAction.{uG, uX, uM} G X) (f : Carrier Y) (m : M.module.obj) :
    quotientMultiplier q hq M f (Representation.Coinvariants.mk M.action m) =
      Representation.Coinvariants.mk M.action (multiplier q M f m) := rfl

/-- The nonunital test action on the literal existing coinvariant quotient. -/
abbrev coinvariantModule (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (M : CompatibleTestAction.{uG, uX, uM} G X) :
    NonUnitalModule (Carrier Y) (Representation.Coinvariants M.action) where
  smul f a := quotientMultiplier q hq M f a
  smul_zero f := map_zero (quotientMultiplier q hq M f)
  smul_add f := map_add (quotientMultiplier q hq M f)
  mul_smul f h a := by
    induction a using Representation.Coinvariants.induction_on with
    | h m =>
      change quotientMultiplier q hq M (f * h) (Representation.Coinvariants.mk M.action m) =
        quotientMultiplier q hq M f
          (quotientMultiplier q hq M h (Representation.Coinvariants.mk M.action m))
      simp only [quotientMultiplier_mk]
      exact congrArg (Representation.Coinvariants.mk M.action) (multiplier_mul q M f h m)
  add_smul f h a := by
    induction a using Representation.Coinvariants.induction_on with
    | h m =>
      change quotientMultiplier q hq M (f + h) (Representation.Coinvariants.mk M.action m) =
        quotientMultiplier q hq M f (Representation.Coinvariants.mk M.action m) +
          quotientMultiplier q hq M h (Representation.Coinvariants.mk M.action m)
      rw [quotientMultiplier_mk, quotientMultiplier_mk, quotientMultiplier_mk,
        multiplier_add, map_add]
  zero_smul a := by
    induction a using Representation.Coinvariants.induction_on with
    | h m =>
      change quotientMultiplier q hq M 0 (Representation.Coinvariants.mk M.action m) = 0
      rw [quotientMultiplier_mk, multiplier_zero, map_zero]

/-- A fixing target test before quotienting still fixes its quotient class. -/
theorem coinvariant_nondegenerate (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : IsLocallyProfinite Y) (M : CompatibleTestAction.{uG, uX, uM} G X) :
    letI := coinvariantModule q hq M
    IsNondegenerate (Carrier Y) (Representation.Coinvariants M.action) := by
  let _ := coinvariantModule q hq M
  intro a
  obtain ⟨m, rfl⟩ := Representation.Coinvariants.mk_surjective M.action a
  obtain ⟨e, he⟩ := pullback_nondegenerate q hY M m
  refine ⟨e, ?_⟩
  change quotientMultiplier q hq M e (Representation.Coinvariants.mk M.action m) =
    Representation.Coinvariants.mk M.action m
  rw [quotientMultiplier_mk]
  exact congrArg (Representation.Coinvariants.mk M.action) he

/-- The descended action is compatible with the original quotient's complex scalars. -/
theorem coinvariant_scalarTower (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (M : CompatibleTestAction.{uG, uX, uM} G X) :
    letI := coinvariantModule q hq M
    IsScalarTower ℂ (Carrier Y) (Representation.Coinvariants M.action) := by
  let _ := coinvariantModule q hq M
  refine ⟨fun c f a => ?_⟩
  induction a using Representation.Coinvariants.induction_on with
  | h m =>
    change quotientMultiplier q hq M (c • f) (Representation.Coinvariants.mk M.action m) =
      c • quotientMultiplier q hq M f (Representation.Coinvariants.mk M.action m)
    rw [quotientMultiplier_mk, quotientMultiplier_mk, multiplier_smul, map_smul]

/-- Canonical scalars recovered from the test action equal the actual quotient scalars. -/
theorem canonicalComplex_eq (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : IsLocallyProfinite Y) (M : CompatibleTestAction.{uG, uX, uM} G X) :
    letI := coinvariantModule q hq M
    NondegenerateScalars.module ℂ isIdempotented (coinvariant_nondegenerate q hq hY M) =
      (inferInstance : Module ℂ (Representation.Coinvariants M.action)) := by
  let _ := coinvariantModule q hq M
  let _ := coinvariant_scalarTower q hq M
  exact NondegenerateScalars.module_eq_of_compatible ℂ isIdempotented
    (coinvariant_nondegenerate q hq hY M)

/-- The original module, viewed as a nondegenerate module of target tests. -/
def sourceObject (q : C(X, Y)) (hY : IsLocallyProfinite Y)
    (M : CompatibleTestAction.{uG, uX, uM} G X) :
    NondegenerateModuleCat.{uY, uM} (Carrier Y) :=
  letI := pullbackModule q M
  ⟨NonUnitalModuleCat.of (Carrier Y) M.module.obj, pullback_nondegenerate q hY M⟩

/-- The literal coinvariant quotient as a published nondegenerate target-test module. -/
def object (q : C(X, Y)) (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : IsLocallyProfinite Y) (M : CompatibleTestAction.{uG, uX, uM} G X) :
    NondegenerateModuleCat.{uY, uM} (Carrier Y) :=
  letI := coinvariantModule q hq M
  ⟨NonUnitalModuleCat.of (Carrier Y) (Representation.Coinvariants M.action),
    coinvariant_nondegenerate q hq hY M⟩

/-- The original complex quotient map, now also a morphism of target-test modules. -/
def quotientMap (q : C(X, Y)) (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : IsLocallyProfinite Y) (M : CompatibleTestAction.{uG, uX, uM} G X) :
    sourceObject q hY M ⟶ object q hq hY M :=
  ObjectProperty.homMk
    { toAddMonoidHom := (Representation.Coinvariants.mk M.action).toAddMonoidHom
      map_smul' _ _ := rfl }

@[simp]
theorem quotientMap_apply (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : IsLocallyProfinite Y) (M : CompatibleTestAction.{uG, uX, uM} G X)
    (m : M.module.obj) :
    CompatibleTestAction.moduleMap (quotientMap q hq hY M) m =
      Representation.Coinvariants.mk M.action m := rfl

/-- The representative formula for the actual target-test action on coinvariants. -/
theorem smul_mk (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (M : CompatibleTestAction.{uG, uX, uM} G X) (f : Carrier Y) (m : M.module.obj) :
    letI := coinvariantModule q hq M
    f • Representation.Coinvariants.mk M.action m =
      Representation.Coinvariants.mk M.action (pullback q f • m) := rfl

theorem quotientMap_surjective (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : IsLocallyProfinite Y) (M : CompatibleTestAction.{uG, uX, uM} G X) :
    Function.Surjective (CompatibleTestAction.moduleMap (quotientMap q hq hY M)) :=
  Representation.Coinvariants.mk_surjective M.action

@[simp]
theorem quotientMap_action (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : IsLocallyProfinite Y) (M : CompatibleTestAction.{uG, uX, uM} G X)
    (g : G) (m : M.module.obj) :
    CompatibleTestAction.moduleMap (quotientMap q hq hY M) (M.action g m) =
      CompatibleTestAction.moduleMap (quotientMap q hq hY M) m :=
  Representation.Coinvariants.mk_self_apply M.action g m

variable {M N : CompatibleTestAction.{uG, uX, uM} G X}

/-- An original test-module morphism with its canonical complex linearity. -/
def originalIntertwiner (f : M ⟶ N) : Representation.IntertwiningMap M.action N.action where
  __ := NondegenerateScalars.toLinearMap ℂ isIdempotented M.module.property N.module.property
    (CompatibleTestAction.moduleMap f.moduleHom)
  isIntertwining' g := by
    ext m
    exact f.comm g m

@[simp]
theorem originalIntertwiner_apply (f : M ⟶ N) (m : M.module.obj) :
    originalIntertwiner f m = CompatibleTestAction.moduleMap f.moduleHom m := rfl

/-- Original morphisms remain linear for pulled-back target tests. -/
def sourceMap (q : C(X, Y)) (hY : IsLocallyProfinite Y) (f : M ⟶ N) :
    sourceObject q hY M ⟶ sourceObject q hY N :=
  ObjectProperty.homMk
    { toAddMonoidHom := (CompatibleTestAction.moduleMap f.moduleHom).toAddMonoidHom
      map_smul' a m :=
        (PointwiseTestModule.toLinearMap M.module.property N.module.property
          (CompatibleTestAction.moduleMap f.moduleHom)).map_smul (pullback q a) m }

/-- The unchanged original coinvariant map of a compatible-action morphism. -/
def inducedLinear (f : M ⟶ N) :
    Representation.Coinvariants M.action →ₗ[ℂ] Representation.Coinvariants N.action :=
  Representation.Coinvariants.map M.action N.action (originalIntertwiner f)

@[simp]
theorem inducedLinear_mk (f : M ⟶ N) (m : M.module.obj) :
    inducedLinear f (Representation.Coinvariants.mk M.action m) =
      Representation.Coinvariants.mk N.action
        (CompatibleTestAction.moduleMap f.moduleHom m) := rfl

/-- The original induced coinvariant map intertwines the descended test multipliers. -/
theorem inducedLinear_multiplier (q : C(X, Y))
    (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (f : M ⟶ N) (a : Carrier Y) (z : Representation.Coinvariants M.action) :
    inducedLinear f (quotientMultiplier q hq M a z) =
      quotientMultiplier q hq N a (inducedLinear f z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h m =>
    rw [quotientMultiplier_mk, inducedLinear_mk, inducedLinear_mk, quotientMultiplier_mk]
    exact congrArg (Representation.Coinvariants.mk N.action)
      ((PointwiseTestModule.toLinearMap M.module.property N.module.property
        (CompatibleTestAction.moduleMap f.moduleHom)).map_smul (pullback q a) m)

/-- The original coinvariant map as a morphism of nondegenerate target-test modules. -/
def map (q : C(X, Y)) (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : IsLocallyProfinite Y) (f : M ⟶ N) :
    object q hq hY M ⟶ object q hq hY N :=
  ObjectProperty.homMk
    { toAddMonoidHom := (inducedLinear f).toAddMonoidHom
      map_smul' := inducedLinear_multiplier q hq f }

@[simp]
theorem map_mk (q : C(X, Y)) (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : IsLocallyProfinite Y) (f : M ⟶ N) (m : M.module.obj) :
    CompatibleTestAction.moduleMap (map q hq hY f) (Representation.Coinvariants.mk M.action m) =
      Representation.Coinvariants.mk N.action
        (CompatibleTestAction.moduleMap f.moduleHom m) := rfl

/-- Restriction of tests along the fixed continuous map, retaining original carriers. -/
def sourceFunctor (q : C(X, Y)) (hY : IsLocallyProfinite Y) :
    CompatibleTestAction.{uG, uX, uM} G X ⥤ NondegenerateModuleCat.{uY, uM} (Carrier Y) where
  obj M := sourceObject q hY M
  map f := sourceMap q hY f
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    rfl

/-- Coinvariants along an invariant map, valued in the original nondegenerate category. -/
def functor (q : C(X, Y)) (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : IsLocallyProfinite Y) :
    CompatibleTestAction.{uG, uX, uM} G X ⥤ NondegenerateModuleCat.{uY, uM} (Carrier Y) where
  obj M := object q hq hY M
  map f := map q hq hY f
  map_id M := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro a
    induction a using Representation.Coinvariants.induction_on with
    | h m => rfl
  map_comp f h := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro a
    induction a using Representation.Coinvariants.induction_on with
    | h m => rfl

/-- The actual quotient maps form a natural transformation of target-test modules. -/
def quotient (q : C(X, Y)) (hq : ∀ (g : G) (x : X), q (g • x) = q x)
    (hY : IsLocallyProfinite Y) :
    sourceFunctor (G := G) q hY ⟶ functor (G := G) q hq hY where
  app M := quotientMap q hq hY M
  naturality {M N} f := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    rfl

end Langlands.Sheaf.Renard.CoinvariantTestModule

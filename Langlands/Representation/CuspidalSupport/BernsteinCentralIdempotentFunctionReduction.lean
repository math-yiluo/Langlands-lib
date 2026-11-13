import Langlands.Representation.CuspidalSupport.BernsteinCenterFunctionsBasics
import Langlands.Representation.CuspidalSupport.BernsteinCentralIdempotentStatements
import Langlands.Representation.Category.ExactFunctor

/-! # Renard VI.10.4, Remark 2, from the Theorem with Remark 1 and the VI.7.4 idempotents

The central idempotent of a Bernstein block acts on every `i_{P_a}^G(ρ_a ⊗ ω)` by the
characteristic function of the block's component; conversely, an element of the centre acting
by that characteristic function is the central idempotent, because (VI.10.4, Theorem with
Remark 1, published as `BernsteinCenterFunctionsStatement`) an element of the centre is
determined by its action on these inductions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Forward

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance instCentralIdempotentFunctionAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance instCentralIdempotentFunctionTopology :
    TopologicalSpace (rationalPoints G) := pointTopology
local instance instCentralIdempotentFunctionLeviClosedImmersion
    (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance instCentralIdempotentFunctionLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance instCentralIdempotentFunctionLeviFiniteType
    (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance instCentralIdempotentFunctionLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

open Classical in
/-- An element of the centre that is the identity on the block `s` and zero on every other
block acts on every object of the block `t` by `1` if `t = s` and by `0` otherwise. -/
theorem centralIdempotent_scalar_of_mem
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
    (z : CatCenter (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)))
    (h1 : ∀ V, bernsteinSaturatedBlockProperty i ν family s V → z.app V = 𝟙 V)
    (h0 : ∀ t, t ≠ s → ∀ V, bernsteinSaturatedBlockProperty i ν family t V → z.app V = 0)
    (t : BernsteinInertialClass.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hV : bernsteinSaturatedBlockProperty i ν family t V) (x : V) :
    SmoothRep.hom (z.app V) x = (if t = s then (1 : ℂ) else 0) • x := by
  split_ifs with h
  · subst h
    rw [h1 _ hV, one_smul]
    rfl
  · rw [h0 _ h _ hV, zero_smul]
    rfl

end Forward

/-- Derived reduction: Renard VI.10.4, Remark 2, follows from the Theorem's second sentence
with Remark 1 (the published `BernsteinCenterFunctionsStatement`) and the VI.7.4 central
idempotents at carriers in `Type (max uF uV)`. -/
def BernsteinCentralIdempotentFunctionReductionStatement : Prop :=
  BernsteinCenterFunctionsStatement.{uF, uV} →
    BernsteinCentralIdempotentStatement.{uF, max uF uV} →
      BernsteinCentralIdempotentFunctionStatement.{uF, uV}

/-- Proof of the reduction: the forward implication is `centralIdempotent_scalar_of_mem`
applied to the membership `twistInduction_mem_saturatedBlock`; for the converse, `z` and the
VI.7.4 idempotent `e s` act by the same scalars on every `i_{P_a}^G(ρ_a ⊗ ω)`, so they are equal
by the injectivity conjunct of `BernsteinCenterFunctionsStatement`. -/
theorem bernsteinCentralIdempotentFunction_reduction :
    BernsteinCentralIdempotentFunctionReductionStatement.{uF, uV} := by
  intro hS2 h74 F _ _ _ _ G _ _ T i ν
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ family s z
  constructor
  · rintro ⟨h1, h0⟩ a
    intro Xa twista inda ω x
    have hmem := twistInduction_mem_saturatedBlock i ν family a
    have hmemω := hmem ω
    have key := centralIdempotent_scalar_of_mem i ν family s z h1 h0
    have keyω := key _ _ hmemω
    exact keyω x
  · intro hz
    obtain ⟨e, -, he1, he0, -⟩ := h74 F G T i ν family
    have he1' : ∀ V, bernsteinSaturatedBlockProperty i ν family s V → (e s).app V = 𝟙 V :=
      fun V hV => he1 s V ((bernsteinBlockProperty_iff_saturated _ _).mpr hV)
    have he0' : ∀ t, t ≠ s → ∀ V, bernsteinSaturatedBlockProperty i ν family t V →
        (e s).app V = 0 :=
      fun t hts V hV =>
        he0 s t (Ne.symm hts) V ((bernsteinBlockProperty_iff_saturated _ _).mpr hV)
    have hinj := (hS2 F G T i ν family).2.1 z (e s)
    have hze : z = e s := by
      apply hinj
      intro a Xa twista inda ω
      apply SmoothRep.hom_ext'
      refine DFunLike.ext _ _ fun x => ?_
      have hmem := twistInduction_mem_saturatedBlock i ν family a
      have hmemω := hmem ω
      have key := centralIdempotent_scalar_of_mem i ν family s (e s) he1' he0'
      have keyω := key _ _ hmemω
      exact (hz a ω x).trans (keyω x).symm
    subst hze
    exact ⟨he1', he0'⟩

end Langlands.CuspidalSupport

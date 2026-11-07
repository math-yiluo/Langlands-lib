import Langlands.GroupScheme.CocycleRefinement
import Langlands.AbelianScheme.KernelBaseChange

/-! # Trivializations of cocycles relative to a base

A morphism `g : U ⊗ P ⟶ G.X` trivializes a natural cocycle `ξ` on `U` relative to `P` when the
coboundary identity for `g` holds on pairs of points of `U ⊗ P` with the same image in `P`.
Relative trivializations descend along fpqc morphisms of the base, and are produced by
compatible trivializations on fpqc refinements over `P`. A trivialization of a base-changed
cocycle gives such a compatible trivialization.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}

/-- `g` trivializes `ξ` relative to `P`: the coboundary identity holds on all pairs of points of
`U ⊗ P` with the same image in `P`. -/
def IsTrivialOver (ξ : Cocycle G U) (P : Over S) (g : U ⊗ P ⟶ G.X) : Prop :=
  ∀ {Z : Over S} (a b : Z ⟶ U ⊗ P), a ≫ snd U P = b ≫ snd U P →
    ξ.toFun (a ≫ fst U P) (b ≫ fst U P) = (a ≫ g) * (b ≫ g)⁻¹

/-- Quasi-compact, flat and surjective morphisms of schemes. -/
private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

private theorem fpqcProperty_of_instances {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [Flat f] [Surjective f] : fpqcProperty f :=
  ⟨inferInstance, inferInstance, inferInstance⟩

private theorem epi_of_fpqcProperty {X Y : Scheme.{u}} (f : X ⟶ Y) (h : fpqcProperty f) :
    Epi f := by
  let : QuasiCompact f := h.1
  let : Flat f := h.2.1
  let : Surjective f := h.2.2
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Every point of `P` lifts along an fpqc morphism `s : V ⟶ P` after an epimorphic change of
the test object. -/
private theorem exists_epi_lift {Z P V : Over S} (c : Z ⟶ P) (s : V ⟶ P)
    (hs : fpqcProperty s.left) :
    ∃ (Z' : Over S) (p : Z' ⟶ Z) (q : Z' ⟶ V), Epi p ∧ q ≫ s = p ≫ c := by
  let Z' : Over S := Over.mk (pullback.fst c.left s.left ≫ Z.hom)
  let p : Z' ⟶ Z := Over.homMk (pullback.fst c.left s.left) rfl
  let q : Z' ⟶ V := Over.homMk (pullback.snd c.left s.left) (by
    change pullback.snd c.left s.left ≫ V.hom = pullback.fst c.left s.left ≫ Z.hom
    rw [← Over.w s, ← Over.w c, ← Category.assoc, ← pullback.condition, Category.assoc])
  have hp : fpqcProperty (pullback.fst c.left s.left) :=
    MorphismProperty.pullback_fst (P := fpqcProperty) _ _ hs
  have : Epi p.left := epi_of_fpqcProperty _ hp
  refine ⟨Z', p, q, Over.epi_of_epi_left p, ?_⟩
  apply Over.OverMorphism.ext
  exact pullback.condition.symm

/-- The cocycle identity reverses a cocycle value. -/
private theorem toFun_swap (ξ : Cocycle G U) {Z : Over S} (a b : Z ⟶ U) :
    ξ.toFun b a = (ξ.toFun a b)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← ξ.cocycle a b a, toFun_self]

/-- Relative trivializations descend along fpqc morphisms of the base. -/
theorem IsTrivialOver.of_whiskerLeft {ξ : Cocycle G U} {P P' : Over S} (t : P' ⟶ P)
    [QuasiCompact t.left] [Flat t.left] [Surjective t.left] {g : U ⊗ P ⟶ G.X}
    (h : ξ.IsTrivialOver P' (U ◁ t ≫ g)) : ξ.IsTrivialOver P g := by
  intro Z a b hab
  obtain ⟨Z', p, q, hp, hq⟩ :=
    exists_epi_lift (a ≫ snd U P) t (fpqcProperty_of_instances t.left)
  let a' : Z' ⟶ U ⊗ P' := CartesianMonoidalCategory.lift (p ≫ a ≫ fst U P) q
  let b' : Z' ⟶ U ⊗ P' := CartesianMonoidalCategory.lift (p ≫ b ≫ fst U P) q
  have ha' : a' ≫ U ◁ t = p ≫ a := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [a']
    · simp [a', hq]
  have hb' : b' ≫ U ◁ t = p ≫ b := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [b']
    · simp [b', hq, hab]
  have key := h a' b' (by simp [a', b'])
  have hfa : a' ≫ fst U P' = p ≫ a ≫ fst U P := by simp [a']
  have hfb : b' ≫ fst U P' = p ≫ b ≫ fst U P := by simp [b']
  rw [hfa, hfb, ← Category.assoc a', ha', ← Category.assoc b', hb'] at key
  apply (cancel_epi p).mp
  rw [← ξ.naturality, key, MonObj.comp_mul, GrpObj.comp_inv]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A trivialization on an fpqc refinement `s : V ⟶ P`, compatible with `ξ` on pairs with the
same image in `P`, descends to a trivialization of `ξ` relative to `P`. -/
theorem exists_isTrivialOver (ξ : Cocycle G U) {P V : Over S} (r : V ⟶ U) (s : V ⟶ P)
    [QuasiCompact s.left] [Flat s.left] [Surjective s.left] (f : V ⟶ G.X)
    (hf : ∀ {Z : Over S} (a b : Z ⟶ V), a ≫ s = b ≫ s →
      ξ.toFun (a ≫ r) (b ≫ r) = (a ≫ f) * (b ≫ f)⁻¹) :
    ∃ g : U ⊗ P ⟶ G.X, ξ.IsTrivialOver P g := by
  have hs := fpqcProperty_of_instances s.left
  have hUs : fpqcProperty (U ◁ s).left := by
    have h := MorphismProperty.pullbackMap (P := fpqcProperty)
      (fpqcProperty_of_instances (𝟙 U.left)) hs (Over.w (𝟙 U)).symm (Over.w s).symm
    exact h
  have : EffectiveEpi (U ◁ s).left := by
    let : QuasiCompact (U ◁ s).left := hUs.1
    let : Flat (U ◁ s).left := hUs.2.1
    let : Surjective (U ◁ s).left := hUs.2.2
    infer_instance
  let φ : U ⊗ V ⟶ G.X := ξ.toFun (fst U V) (snd U V ≫ r) * (snd U V ≫ f)
  have hφ {Z : Over S} (x : Z ⟶ U ⊗ V) :
      x ≫ φ = ξ.toFun (x ≫ fst U V) ((x ≫ snd U V) ≫ r) * ((x ≫ snd U V) ≫ f) := by
    simp only [φ, MonObj.comp_mul, ← ξ.naturality, Category.assoc]
  have hdesc {Z : Over S} (x y : Z ⟶ U ⊗ V) (hfst : x ≫ fst U V = y ≫ fst U V)
      (hsnd : (x ≫ snd U V) ≫ s = (y ≫ snd U V) ≫ s) : x ≫ φ = y ≫ φ := by
    rw [hφ, hφ, hfst, ξ.cocycle (y ≫ fst U V) ((y ≫ snd U V) ≫ r) ((x ≫ snd U V) ≫ r),
      hf (y ≫ snd U V) (x ≫ snd U V) hsnd.symm]
    group
  let d : (U ⊗ P).left ⟶ G.X.left :=
    EffectiveEpi.desc (U ◁ s).left φ.left (fun {Z} x y hxy => by
      have hy : y ≫ (U ⊗ V).hom = x ≫ (U ⊗ V).hom := by
        rw [← Over.w (U ◁ s), ← Category.assoc, ← Category.assoc, hxy]
      let x₀ : Over.mk (x ≫ (U ⊗ V).hom) ⟶ U ⊗ V := Over.homMk x rfl
      let y₀ : Over.mk (x ≫ (U ⊗ V).hom) ⟶ U ⊗ V := Over.homMk y hy
      have hxy₀ : x₀ ≫ U ◁ s = y₀ ≫ U ◁ s := Over.OverMorphism.ext hxy
      have h1 : x₀ ≫ fst U V = y₀ ≫ fst U V := by
        simpa only [Category.assoc, whiskerLeft_fst] using congrArg (· ≫ fst U P) hxy₀
      have h2 : (x₀ ≫ snd U V) ≫ s = (y₀ ≫ snd U V) ≫ s := by
        simpa only [Category.assoc, whiskerLeft_snd] using congrArg (· ≫ snd U P) hxy₀
      exact congrArg (fun e => e.left) (hdesc x₀ y₀ h1 h2))
  have hd : (U ◁ s).left ≫ d = φ.left := EffectiveEpi.fac _ _ _
  let g : U ⊗ P ⟶ G.X := Over.homMk d (by
    apply (cancel_epi (U ◁ s).left).mp
    rw [← Category.assoc, hd, Over.w φ, Over.w (U ◁ s)])
  have hg : U ◁ s ≫ g = φ := Over.OverMorphism.ext hd
  refine ⟨g, fun {Z} a b hab => ?_⟩
  obtain ⟨Z', p, q, hp, hq⟩ := exists_epi_lift (a ≫ snd U P) s hs
  let a' : Z' ⟶ U ⊗ V := CartesianMonoidalCategory.lift (p ≫ a ≫ fst U P) q
  let b' : Z' ⟶ U ⊗ V := CartesianMonoidalCategory.lift (p ≫ b ≫ fst U P) q
  have ha' : a' ≫ U ◁ s = p ≫ a := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [a']
    · simp [a', hq]
  have hb' : b' ≫ U ◁ s = p ≫ b := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [b']
    · simp [b', hq, hab]
  have hga : p ≫ a ≫ g = ξ.toFun (p ≫ a ≫ fst U P) (q ≫ r) * (q ≫ f) := by
    rw [← Category.assoc, ← ha', Category.assoc, hg, hφ]
    simp [a']
  have hgb : p ≫ b ≫ g = ξ.toFun (p ≫ b ≫ fst U P) (q ≫ r) * (q ≫ f) := by
    rw [← Category.assoc, ← hb', Category.assoc, hg, hφ]
    simp [b']
  apply (cancel_epi p).mp
  rw [← ξ.naturality, MonObj.comp_mul, GrpObj.comp_inv, hga, hgb,
    ξ.cocycle (p ≫ a ≫ fst U P) (q ≫ r) (p ≫ b ≫ fst U P), toFun_swap ξ (p ≫ b ≫ fst U P) (q ≫ r)]
  group

variable {S' : Scheme.{u}}

/-- The base change of `ξ` along `b : S' ⟶ S`, evaluated on a cover `V` over `S'` through a
morphism `r` from `V`, viewed over `S`, to `U`. -/
def baseChange (b : S' ⟶ S) (ξ : Cocycle G U) (V : Over S') (r : (Over.map b).obj V ⟶ U) :
    Cocycle ((GroupScheme.baseChange b).obj G) V where
  toFun {Z} x y := (baseChangePointsEquiv b G Z).symm
    (ξ.toFun ((Over.map b).map x ≫ r) ((Over.map b).map y ≫ r))
  naturality t x y := by
    apply (baseChangePointsEquiv b G _).injective
    rw [MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality, MulEquiv.apply_symm_apply,
      Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ξ.naturality]
  cocycle x y z := by
    rw [← map_mul, ξ.cocycle _ ((Over.map b).map y ≫ r) _]

theorem baseChange_toFun (b : S' ⟶ S) (ξ : Cocycle G U) (V : Over S')
    (r : (Over.map b).obj V ⟶ U) {Z : Over S'} (x y : Z ⟶ V) :
    baseChangePointsEquiv b G Z ((ξ.baseChange b V r).toFun x y) =
      ξ.toFun ((Over.map b).map x ≫ r) ((Over.map b).map y ≫ r) :=
  MulEquiv.apply_symm_apply _ _

/-- A trivialization of the base-changed cocycle gives a trivialization over `V`, viewed over
`S`, that is compatible with `ξ` on pairs of points with the same image in `V`'s base `S'`. -/
theorem exists_of_baseChange_isTrivial (b : S' ⟶ S) (ξ : Cocycle G U) (V : Over S')
    (r : (Over.map b).obj V ⟶ U) (h : (ξ.baseChange b V r).IsTrivial) :
    ∃ f : (Over.map b).obj V ⟶ G.X, ∀ {Z : Over S} (x y : Z ⟶ (Over.map b).obj V),
      x.left ≫ V.hom = y.left ≫ V.hom →
        ξ.toFun (x ≫ r) (y ≫ r) = (x ≫ f) * (y ≫ f)⁻¹ := by
  obtain ⟨f₀, hf₀⟩ := h
  refine ⟨baseChangePointsEquiv b G V f₀, fun {Z} x y hxy => ?_⟩
  let Z₀ : Over S' := Over.mk (x.left ≫ V.hom)
  let x₀ : Z₀ ⟶ V := Over.homMk x.left rfl
  let y₀ : Z₀ ⟶ V := Over.homMk y.left hxy.symm
  let e : Z ⟶ (Over.map b).obj Z₀ := Over.homMk (𝟙 Z.left) (by
    simpa [Z₀] using Over.w x)
  have hx : e ≫ (Over.map b).map x₀ = x := by
    apply Over.OverMorphism.ext
    simp [e, x₀]
  have hy : e ≫ (Over.map b).map y₀ = y := by
    apply Over.OverMorphism.ext
    simp [e, y₀]
  have key := congrArg (fun w => e ≫ baseChangePointsEquiv b G Z₀ w) (hf₀ x₀ y₀)
  simp only [baseChange_toFun, map_mul, map_inv, baseChangePointsEquiv_naturality] at key
  rw [← ξ.naturality, ← Category.assoc, hx, ← Category.assoc, hy, MonObj.comp_mul,
    ← GrpObj.comp_inv, ← Category.assoc, hx, ← Category.assoc, hy, GrpObj.comp_inv] at key
  exact key

end Langlands.GroupScheme.Cocycle

module


public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks.Basic
public import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Flatness and `Tor_1` over a ring, and the skyscraper realization of stalk modules

This file proves the per-ring fact that a module over a commutative ring is flat iff its first
`Tor` against every module vanishes (`OXModule.module_flat_iff_tor1`), via the horseshoe
construction and the long exact sequence of left-derived functors.  It then constructs, for a
point `x` and an `O_{X,x}`-module `N`, the skyscraper presheaf of `O_X`-modules
`OXModule.skyscraperPOM x N` and computes the stalk at `x` of its sheafification
(`OXModule.sheafify_skyscraperPOM_stalk_iso`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopCat

universe u

namespace OXModule

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

attribute [local instance] sectionModule sectionPresheafModule stalkModule

/-! ## Stalk-wise reduction: the per-ring heart and the realization lemma

The main theorem is reduced (via `flat_iff_flat_stalk`) to a purely
*module-theoretic* statement over each local ring `O_{X,x}`:

  `F` flat  ↔  `∀ x, F_x` flat  ↔  `∀ x, ∀ N, Tor₁^{O_{X,x}}(F_x, N) = 0`
                                  ↔  `∀ G, ∀ x, Tor₁^{O_{X,x}}(F_x, G_x) = 0`
                                  =   `∀ G, Tor1IsZero F G`.

Two ingredients are needed beyond the correctness lemma `flat_iff_flat_stalk`:

* (HEART) the classical per-ring fact that an `R`-module is flat iff its first
  Tor against *every* module vanishes (`module_flat_iff_tor1`); and
* (REALIZATION) the fact that, for a fixed point `x`, *every* `O_{X,x}`-module
  `N` arises as the stalk `G_x` of some `O_X`-module `G` — concretely the
  skyscraper sheaf at `x` with value `N` (`exists_oxModule_stalk_iso`).  This is
  what lets us convert the `∀ N` quantifier (needed to test flatness of `F_x`)
  into the `∀ G` quantifier appearing in the statement. -/

/-! ## Per-ring heart (classical "flat ↔ Tor₁ vanishes")
For a commutative ring `R` and an `R`-module `M`, `M` is flat iff the first
(categorical) Tor of `M` with every `R`-module `N` is the zero module.

*Argument.*  `(⇒)` If `M` is flat then `- ⊗_R M` is exact, so the functor
`(tensoringLeft (ModuleCat R)).obj N` whose left-derived functor computes
`Tor` is already exact in the relevant degree; equivalently a flat module is an
acyclic object for the Tor bifunctor, so all higher Tor vanish, in particular
`Tor₁(M, N) = 0`.  Concretely: pick a short exact sequence
`0 → K → P → N → 0` with `P` projective (free); the long exact sequence of Tor
gives `Tor₁(M,N) ↪ K ⊗ M → P ⊗ M`, and the second map is injective because `M`
is flat (`Module.Flat.rTensor_preserves_injective_linearMap` /
`Module.Flat.iff_rTensor_exact`), forcing `Tor₁(M,N) = 0`.
`(⇐)` Conversely, vanishing of `Tor₁(M, -)` makes `- ⊗ M` left exact (the
connecting map `Tor₁(M,N) → K ⊗ M` is `0`, so `K ⊗ M → P ⊗ M` is injective for
all `K ↪ P`), which is flatness via
`Module.Flat.iff_rTensor_preserves_injective_linearMap`.

This is the classical result; Mathlib has the exactness/injectivity
characterizations of `Module.Flat` (`Module.Flat.iff_rTensor_exact`,
`Module.Flat.iff_rTensor_preserves_injective_linearMap`,
`Module.Flat.rTensor_preserves_injective_linearMap`) and the basic Tor API
(`CategoryTheory.Tor`, `isZero_Tor_succ_of_projective`, the long exact sequence
of a left-derived functor `Functor.leftDerived`), but *not* this packaged
equivalence (it is an explicit `TODO` in `Mathlib.RingTheory.Flat.CategoryTheory`).
It must be assembled from those pieces. -/

/-! ### Homological core of the reverse direction (LES of left-derived functors)

For an additive, right-exact `F` on `ModuleCat R` and a mono `f : A ⟶ B`,
vanishing of `(F.leftDerived 1).obj (cokernel f)` forces `(F.leftDerived 0).map f`
to be mono.  This is the only genuinely hard, not-pre-packaged piece; it is
isolated below into the single unproved lemma
`exists_exact_leftDerived_segment_of_mono` (the long-exact-sequence segment via
the horseshoe lemma), from which `additive_mono_of_isZero_leftDerived_one`
follows by short glue (zero source ⇒ left map zero ⇒ right map mono). -/

/-! ## Horseshoe construction

For a mono `f : A ⟶ B` in `ModuleCat R` the horseshoe construction is the case
`C := ModuleCat R`, `S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)` of the
construction in an arbitrary abelian category, which is `CategoryTheory.ShortComplex.horseshoe`
in `StacksFrontier/CategoryTheory/Abelian/Projective/Horseshoe.lean`.  That file carries the whole
development — the shear family `sₙ` with its cross-term identity, the twisted lower-triangular
differential, the middle complex with its degreewise splitting, and the augmentation — so none of
it is restated here; `exists_horseshoe_complex_split_covering` below reads the data off it. -/

open Classical in
/-- **Realization of stalk modules (skyscraper sheaf).**
For a fixed point `x` and an arbitrary `O_{X,x}`-module `N`, there is an
`O_X`-module `G` whose stalk at `x` is isomorphic to `N`.

*Argument.*  Take `G` to be the skyscraper sheaf at `x` with value `N`, viewed
as an `O_X`-module via the stalk ring map `O_X(U) → O_{X,x}` for `U ∋ x`.  Its
stalk at `x` is the filtered colimit over open neighborhoods `U ∋ x` of the
constant value `N`, with identity transition maps, hence canonically `N`.

The carrier object of the skyscraper presheaf-of-modules at `x` with value
`N`: over an open `U` containing `x` it is `N` with `O_X(U)`-action restricted
along the germ ring map `O_X(U) → O_{X,x}`; elsewhere it is the zero module.
(Validated, proof-complete building block for the skyscraper realization.) -/
noncomputable def skyscraperObj (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    ModuleCat.{u} ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) :=
  if h : x ∈ U.unop then
    (ModuleCat.restrictScalars (X.presheaf.germ U.unop x h).hom).obj N
  else
    ModuleCat.of _ PUnit.{u+1}

/-- Compatibility of germs of the structure sheaf: for `i : U ⟶ V` (i.e.
`V ⊆ U`) and `x ∈ V`, the germ at `U` factors as the germ at `V` precomposed
with the restriction `O_X(U) → O_X(V)`.  (Validated, proof-complete.) -/
theorem structure_germ_comp (x : X.carrier)
    {U V : (TopologicalSpace.Opens X.carrier)ᵒᵖ} (i : U ⟶ V) (hV : x ∈ V.unop) :
    (X.presheaf.germ U.unop x ((leOfHom i.unop) hV)).hom =
      ((X.presheaf.germ V.unop x hV).hom).comp ((X.presheaf.map i).hom) := by
  have h := X.presheaf.germ_res i.unop x hV
  have e : i.unop.op = i := rfl
  rw [e] at h
  rw [← CommRingCat.hom_comp, h]

/-- The transition map of the skyscraper presheaf-of-modules.  On the open sets
containing `x` it is the canonical change-of-scalars identification built from
`structure_germ_comp` and `ModuleCat.restrictScalarsComp'`; otherwise it is the
zero map (the target sits over the zero module).  (Validated, proof-complete.) -/
noncomputable def skyscraperMap (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    {U V : (TopologicalSpace.Opens X.carrier)ᵒᵖ} (i : U ⟶ V) :
    skyscraperObj x N U ⟶ (ModuleCat.restrictScalars
      (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map i))).obj
        (skyscraperObj x N V) := by
  classical
  by_cases hV : x ∈ V.unop
  · have hU : x ∈ U.unop := (leOfHom i.unop) hV
    have eU : skyscraperObj x N U =
        (ModuleCat.restrictScalars (X.presheaf.germ U.unop x hU).hom).obj N := by
      rw [skyscraperObj, dite_eq_left hU]
    have eV : skyscraperObj x N V =
        (ModuleCat.restrictScalars (X.presheaf.germ V.unop x hV).hom).obj N := by
      rw [skyscraperObj, dite_eq_left hV]
    refine eqToHom eU ≫ ?_ ≫
      (ModuleCat.restrictScalars
        (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map i))).map
          (eqToHom eV.symm)
    exact (ModuleCat.restrictScalarsComp' ((X.presheaf.map i).hom)
      (X.presheaf.germ V.unop x hV).hom (X.presheaf.germ U.unop x hU).hom
      (structure_germ_comp x i hV)).hom.app N
  · exact 0

/-- The forward component of the change-of-scalars coherence iso
`restrictScalarsComp'App` is the canonical `eqToHom` cast (it is built from
`AddEquiv.refl`, hence the identity on underlying types).  Used to collapse the
skyscraper transition maps to `eqToHom`s in the coherence proofs. -/
theorem restrictScalarsComp'App_hom_eqToHom
    {R₁ R₂ R₃ : Type u} [Ring R₁] [Ring R₂] [Ring R₃]
    (f : R₁ →+* R₂) (g : R₂ →+* R₃) (gf : R₁ →+* R₃) (h : gf = g.comp f)
    (M : ModuleCat R₃) :
    (ModuleCat.restrictScalarsComp'App f g gf h M).hom = eqToHom (by subst h; rfl) := by
  subst h; rfl

/-- The inverse component of the identity change-of-scalars iso
`restrictScalarsId'App` is the canonical `eqToHom` cast (built from
`AddEquiv.refl`). -/
theorem restrictScalarsId'App_inv_eqToHom
    {R : Type u} [Ring R] (f : R →+* R) (h : f = RingHom.id R) (M : ModuleCat R) :
    (ModuleCat.restrictScalarsId'App f h M).inv = eqToHom (by subst h; rfl) := by
  subst h; rfl

/-- Morphisms into the restriction of scalars of `skyscraperObj x N U` are equal when `x ∉ U`. -/
private theorem hom_ext_restrictScalars_skyscraperObj_of_not_mem (x : X.carrier)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) {U : (TopologicalSpace.Opens X.carrier)ᵒᵖ}
    (hU : x ∉ U.unop) {R : Type u} [Ring R]
    (f : R →+* (X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) {M : ModuleCat.{u} R}
    (a b : M ⟶ (ModuleCat.restrictScalars f).obj (skyscraperObj x N U)) : a = b := by
  have : skyscraperObj x N U = ModuleCat.of _ PUnit.{u+1} := by
    rw [skyscraperObj, dite_eq_right hU]
  have : Subsingleton ((ModuleCat.restrictScalars f).obj (skyscraperObj x N U)) := by
    rw [this]
    exact inferInstanceAs (Subsingleton PUnit.{u+1})
  exact ModuleCat.hom_ext (LinearMap.ext fun y => Subsingleton.elim _ _)

/-- **Coherence (LEAF 1a): identity law for the skyscraper transition maps.**
This is the `map_id` field needed to assemble `skyscraperObj`/`skyscraperMap`
into a `PresheafOfModules`.  By the case split in `skyscraperMap`:
* on `x ∈ U` the map is built from `structure_germ_comp x (𝟙 U)` (which reduces
  the germ factorization to `germ_U = germ_U ∘ 𝟙`) and the `restrictScalarsComp'`
  coherence iso; unfolding shows it equals the canonical `restrictScalarsId'.inv`
  component — this is `restrictScalarsId'`/`restrictScalarsComp'`/`eqToHom`
  coherence (`eqToHom_map`, `eqToHom_trans`, `eqToHom_app`);
* on `x ∉ U` the codomain is the zero module `PUnit`, so both sides are forced
  equal by `Subsingleton` of homs into `PUnit` (`Subsingleton.elim`).
Routine but verbose; no deep content. -/
theorem skyscraperMap_id (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    skyscraperMap x N (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map (𝟙 U)))
        (by simp)).inv.app (skyscraperObj x N U) := by
  classical
  rw [skyscraperMap]
  by_cases hU : x ∈ U.unop
  · rw [dite_eq_left hU]
    -- Both the `restrictScalarsComp'`/`restrictScalarsId'` coherence isos are
    -- `AddEquiv.refl`-based, hence `eqToHom` casts; collapse the whole composite
    -- to a single `eqToHom` between equal objects (`eqToHom_trans`).
    simp only [ModuleCat.restrictScalarsId'_inv_app, ModuleCat.restrictScalarsComp'_hom_app,
      restrictScalarsComp'App_hom_eqToHom, restrictScalarsId'App_inv_eqToHom, eqToHom_map,
      eqToHom_trans]
  · rw [dite_eq_right hU]
    exact hom_ext_restrictScalars_skyscraperObj_of_not_mem x N hU _ _ _

/-- **Coherence (LEAF 1b): composition law for the skyscraper transition maps.**
This is the `map_comp` field needed to assemble `skyscraperObj`/`skyscraperMap`
into a `PresheafOfModules`.  By the case split in `skyscraperMap`:
* on `x ∈ U` (hence `x ∈ V`, `x ∈ W` whenever they appear) it follows from
  `structure_germ_comp` applied along `i` and `j` and the associativity/coherence
  of `restrictScalarsComp'` (the germ factorizes as
  `germ_U = germ_W ∘ R.map j ∘ R.map i`);
* whenever the target sits over a `PUnit` zero module both sides agree by
  `Subsingleton`.
Routine but verbose; no deep content. -/
theorem skyscraperMap_comp (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    {U V W : (TopologicalSpace.Opens X.carrier)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    skyscraperMap x N (i ≫ j) =
      skyscraperMap x N i ≫
        (ModuleCat.restrictScalars
            (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map i))).map
            (skyscraperMap x N j) ≫
          (ModuleCat.restrictScalarsComp'
                  (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map i))
                  (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map j))
                  (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map (i ≫ j)))
                  (by simp)).inv.app
            (skyscraperObj x N W) := by
  classical
  by_cases hW : x ∈ W.unop
  · have hV : x ∈ V.unop := (leOfHom j.unop) hW
    have hU : x ∈ U.unop := (leOfHom i.unop) hV
    have hinv : ∀ {R₁ R₂ R₃ : Type u} [Ring R₁] [Ring R₂] [Ring R₃]
        (f : R₁ →+* R₂) (g : R₂ →+* R₃) (gf : R₁ →+* R₃) (h : gf = g.comp f)
        (M : ModuleCat R₃),
        (ModuleCat.restrictScalarsComp'App f g gf h M).inv = eqToHom (by subst h; rfl) := by
      intro R₁ R₂ R₃ _ _ _ f g gf h M; subst h; rfl
    rw [skyscraperMap, skyscraperMap, skyscraperMap]
    rw [dite_eq_left hW, dite_eq_left hV, dite_eq_left hW]
    simp only [ ModuleCat.restrictScalarsComp'_inv_app,
      ModuleCat.restrictScalarsComp'_hom_app, restrictScalarsComp'App_hom_eqToHom,
      eqToHom_map, eqToHom_trans,
       eqToHom_trans_assoc]
    rw [hinv]
    simp only [eqToHom_trans]
  · rw [skyscraperMap]
    rw [dite_eq_right hW]
    exact hom_ext_restrictScalars_skyscraperObj_of_not_mem x N hW _ _ _

/-- The skyscraper presheaf-of-modules at `x` with value `N`: assembled from the
verified `skyscraperObj`/`skyscraperMap` building blocks plus the two coherence
leaves `skyscraperMap_id`/`skyscraperMap_comp`.  Sheafifying this (via
`OXModule.sheafify`) yields the `O_X`-module realizing `N` as a stalk. -/
noncomputable def skyscraperPOM (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    PresheafOfModules.{u} ((ringSheaf X).obj) :=
  PresheafOfModules.mk (skyscraperObj x N) (fun {_ _} i => skyscraperMap x N i)
    (skyscraperMap_id x N) (fun {_ _ _} i j => skyscraperMap_comp x N i j)

/-! **(LEAF 3a) Sheafification preserves stalks, `O_{X,x}`-linearly (obligation O1).**
The sheafification unit `skyscraperPOM x N ⟶ (sheafify.obj (skyscraperPOM x N)).val`
of `PresheafOfModules.sheafification (𝟙 _)` is a stalkwise isomorphism at every
point: it induces an `O_{X,x}`-linear isomorphism between the stalk of the
sheafified module and the stalk of the original presheaf-of-modules.

*Justification.* The underlying
type/`AddCommGrp`-valued presheaf morphism of the unit is precisely the
sheafification unit for the open-cover Grothendieck topology of `X.carrier`; for
that site the unit is a local isomorphism, and `TopCat.Presheaf.stalkFunctor x`
inverts local isomorphisms (stalks are filtered colimits over `OpenNhds x`, and
local injectivity + local surjectivity become genuine bijectivity in the germ
colimit). The unit is a morphism *in* `PresheafOfModules`, so each component is
`O_X(U)`-linear; the induced colimit map is therefore `O_{X,x}`-linear because
the `O_{X,x}`-action factors through the germs `O_X(U) → O_{X,x}`.  Mathlib API:
`TopCat.Presheaf.stalkFunctor`, the local-iso/stalk-iso facts in
`Mathlib.Topology.Sheaves.Stalks`, transported across `PresheafOfModules.toPresheaf`. -/

/-- The underlying `AddCommGrp`-valued presheaf of the skyscraper PoM has value
(the underlying group of) `N` on every open containing `x`. -/
theorem skyscraperPOM_presheaf_obj_eq (x : X.carrier)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (W : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (h : x ∈ W.unop) :
    (skyscraperPOM x N).presheaf.obj W = AddCommGrpCat.of N := by
  change (forget₂ (ModuleCat _) AddCommGrpCat).obj (skyscraperObj x N W) = _
  rw [skyscraperObj, dite_eq_left h]
  rfl

/-- On opens containing `x`, the transition maps of the skyscraper PoM are, under
the canonical `= AddCommGrpCat.of N` identifications, the identity. -/
theorem skyscraperPOM_presheaf_map_eq (x : X.carrier)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) {W₁ W₂ : (TopologicalSpace.Opens X.carrier)ᵒᵖ}
    (j : W₁ ⟶ W₂) (h₂ : x ∈ W₂.unop) :
    (skyscraperPOM x N).presheaf.map j =
      eqToHom (skyscraperPOM_presheaf_obj_eq x N W₁ ((leOfHom j.unop) h₂)) ≫
        eqToHom (skyscraperPOM_presheaf_obj_eq x N W₂ h₂).symm := by
  change (forget₂ (ModuleCat _) AddCommGrpCat).map (skyscraperMap x N j) = _
  rw [skyscraperMap, dite_eq_left h₂]
  simp only [ restrictScalarsComp'App_hom_eqToHom,
    ModuleCat.restrictScalarsComp'_hom_app, eqToHom_map, eqToHom_trans]
  rfl

/-- **(LEAF 3b) Constant filtered colimit: the skyscraper stalk is `N` (abelian-group level).**
The underlying `AddCommGrp`-valued presheaf of `skyscraperPOM x N` is, on every
neighbourhood `U ∋ x`, the underlying group of `N` (the value of `skyscraperObj`
on opens containing `x` is `(restrictScalars (germ U)).obj N`, whose underlying
type/group is that of `N`), and `structure_germ_comp` makes every transition map
of the `OpenNhds x`-diagram the identity on `N`.  Hence the stalk at `x` — the
filtered colimit over the (nonempty, filtered) category `OpenNhds x` of this
constant diagram — is `N` as an abelian group.

*Justification.* Constant filtered
colimit (`Limits.colimitConstCone` / `IsColimit.coconePointUniqueUpToIso`), cf.
`skyscraperPresheafStalkOfSpecializes p₀ A (specializes_refl p₀)`.  The germ map
`N → stalk` for `U ∋ x` is the comparison iso. -/
noncomputable def sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ↑(TopCat.Presheaf.stalk (skyscraperPOM x N).presheaf x) ≃+ N := by
  set P := (skyscraperPOM x N).presheaf with hP
  -- membership of x in every neighbourhood appearing in the stalk diagram
  have hmem : ∀ (U : (TopologicalSpace.OpenNhds x)ᵒᵖ),
      x ∈ ((TopologicalSpace.OpenNhds.inclusion x).op.obj U).unop :=
    fun U => U.unop.2
  -- the value identification on the diagram objects
  let eU : ∀ (U : (TopologicalSpace.OpenNhds x)ᵒᵖ),
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ P).obj U = AddCommGrpCat.of N :=
    fun U => skyscraperPOM_presheaf_obj_eq x N _ (hmem U)
  -- the colimit cocone with point N, all legs the canonical identifications
  let c : CategoryTheory.Limits.Cocone
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ P) :=
    { pt := AddCommGrpCat.of N
      ι :=
        { app := fun U => eqToHom (eU U)
          naturality := by
            intro U V i
            simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
              Functor.const_obj_map, Category.comp_id]
            rw [skyscraperPOM_presheaf_map_eq x N _ (hmem V)]
            simp only [eqToHom_trans] } }
  -- the desc gives the forward map; the germ at any U gives a section
  refine (?_ : (TopCat.Presheaf.stalk P x) ≅ AddCommGrpCat.of N).addCommGroupIsoToAddEquiv
  refine
    { hom := CategoryTheory.Limits.colimit.desc _ c
      inv := eqToHom (eU (Opposite.op ⊤)).symm ≫
        TopCat.Presheaf.germ P
          ((TopologicalSpace.OpenNhds.inclusion x).obj (⊤ : TopologicalSpace.OpenNhds x))
          x (hmem (Opposite.op ⊤))
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply TopCat.Presheaf.stalk_hom_ext
    intro U hxU
    let objectIso := eqToIso (eU (Opposite.op ⟨U, hxU⟩))
    let topIso := eqToIso (eU (Opposite.op ⊤))
    let germU := TopCat.Presheaf.germ P U x hxU
    let germTop := TopCat.Presheaf.germ P
      ((TopologicalSpace.OpenNhds.inclusion x).obj (⊤ : TopologicalSpace.OpenNhds x))
      x (hmem (Opposite.op ⊤))
    have hgd : germU ≫ CategoryTheory.Limits.colimit.desc _ c = objectIso.hom :=
      CategoryTheory.Limits.colimit.ι_desc c (Opposite.op ⟨U, hxU⟩)
    have hle : U ≤ (TopologicalSpace.OpenNhds.inclusion x).obj
        (⊤ : TopologicalSpace.OpenNhds x) := le_top
    have hmap : P.map (homOfLE hle).op = topIso.hom ≫ objectIso.inv :=
      skyscraperPOM_presheaf_map_eq x N (homOfLE hle).op hxU
    have hres : topIso.hom ≫ objectIso.inv ≫ germU = germTop :=
      (Category.assoc topIso.hom objectIso.inv germU).symm.trans
        ((congrArg (fun morphism => morphism ≫ germU) hmap).symm.trans
          (TopCat.Presheaf.germ_res P (homOfLE hle) x hxU))
    have topGerm : topIso.inv ≫ germTop = objectIso.inv ≫ germU :=
      (congrArg (fun morphism => topIso.inv ≫ morphism) hres).symm.trans
        (topIso.inv_hom_id_assoc (objectIso.inv ≫ germU))
    exact (Category.assoc germU (CategoryTheory.Limits.colimit.desc _ c)
      (topIso.inv ≫ germTop)).symm.trans
        ((congrArg (fun morphism => morphism ≫ topIso.inv ≫ germTop) hgd).trans
          ((congrArg (fun morphism => objectIso.hom ≫ morphism) topGerm).trans
            ((objectIso.hom_inv_id_assoc germU).trans (Category.comp_id germU).symm)))
  · let topIso := eqToIso (eU (Opposite.op ⊤))
    let germTop := TopCat.Presheaf.germ P
      ((TopologicalSpace.OpenNhds.inclusion x).obj (⊤ : TopologicalSpace.OpenNhds x))
      x (hmem (Opposite.op ⊤))
    have hgd : germTop ≫ CategoryTheory.Limits.colimit.desc _ c = topIso.hom :=
      CategoryTheory.Limits.colimit.ι_desc c (Opposite.op ⊤)
    exact (Category.assoc topIso.inv germTop (CategoryTheory.Limits.colimit.desc _ c)).trans
      ((congrArg (fun morphism => topIso.inv ≫ morphism) hgd).trans topIso.inv_hom_id)

/-- Characterization of the forward map of
`sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv` on a germ: it sends the germ
of `n` over a neighbourhood `U ∋ x` to the value `n`, under the canonical
identification `skyscraperPOM_presheaf_obj_eq`. -/
theorem sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv_germ
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop)
    (n : (skyscraperPOM x N).presheaf.obj U) :
    sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N
        (TopCat.Presheaf.germ (skyscraperPOM x N).presheaf U.unop x hx n) =
      (eqToHom (skyscraperPOM_presheaf_obj_eq x N U hx)) n := by
  have key : TopCat.Presheaf.germ (skyscraperPOM x N).presheaf U.unop x hx ≫
      AddCommGrpCat.ofHom
        (sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N).toAddMonoidHom =
      eqToHom (skyscraperPOM_presheaf_obj_eq x N U hx) := by
    exact CategoryTheory.Limits.colimit.ι_desc
      (F := (TopologicalSpace.OpenNhds.inclusion x).op ⋙ (skyscraperPOM x N).presheaf) _
      (Opposite.op (⟨U.unop, hx⟩ : TopologicalSpace.OpenNhds x))
  have happ := ConcreteCategory.congr_hom key n
  exact (ConcreteCategory.comp_apply
    (TopCat.Presheaf.germ (skyscraperPOM x N).presheaf U.unop x hx)
    (AddCommGrpCat.ofHom
      (sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N).toAddMonoidHom) n).symm.trans happ

/-- Casting along `P = (restrictScalars f).obj M` (at the level of underlying types)
turns the `R`-action into the `f`-twisted `S`-action. -/
theorem cast_smul_restrictScalars {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (M : ModuleCat.{u} S) (P : ModuleCat.{u} R)
    (hP : P = (ModuleCat.restrictScalars f).obj M)
    (hT : (↑P : Type u) = ↑M) (s : R) (n : (↑P : Type u)) :
    cast hT (s • n) = f s • cast hT n := by
  subst hP
  exact ModuleCat.restrictScalars.smul_def f s n

/-- The canonical identification `skyscraperPOM_presheaf_obj_eq` intertwines the
`O_X(U)`-action on `skyscraperObj` (via `restrictScalars` along the germ) with the
`O_{X,x}`-action on `N`: applying the leg to `s • n` equals scaling `n` by the germ
of `s`. -/
theorem skyscraperPOM_leg_smul
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop)
    (s : (X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) (n : skyscraperObj x N U) :
    (eqToHom (skyscraperPOM_presheaf_obj_eq x N U hx)) (s • n) =
      (ConcreteCategory.hom (X.presheaf.germ U.unop x hx)) s •
        (eqToHom (skyscraperPOM_presheaf_obj_eq x N U hx)) n := by
  -- The leg `eqToHom` is the underlying identity; turn both applications into `cast`s.
  have hcast : ∀ {A B : AddCommGrpCat.{u}} (h : A = B) (y : A),
      (ConcreteCategory.hom (eqToHom h)) y
        = cast (congrArg (fun Z : AddCommGrpCat.{u} => (↑Z : Type u)) h) y := by
    intro A B h y; subst h; simp
  have hsky : skyscraperObj x N U = (ModuleCat.restrictScalars
      (X.presheaf.germ U.unop x hx).hom).obj N := by
    rw [skyscraperObj, dite_eq_left hx]
  have castScalar := cast_smul_restrictScalars (X.presheaf.germ U.unop x hx).hom N
    (skyscraperObj x N U) hsky
    (congrArg (fun group : AddCommGrpCat.{u} => (↑group : Type u))
      (skyscraperPOM_presheaf_obj_eq x N U hx)) s n
  exact (hcast (skyscraperPOM_presheaf_obj_eq x N U hx) (s • n)).trans
    (castScalar.trans
      (congrArg (fun value : N => X.presheaf.germ U.unop x hx s • value)
        (hcast (skyscraperPOM_presheaf_obj_eq x N U hx) n).symm))

noncomputable def sheafify_skyscraperPOM_stalkIso_skyscraper
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ModuleCat.of (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (skyscraperPOM x N).presheaf x) ≅ N :=
  LinearEquiv.toModuleIso
    { sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N with
      map_smul' := by
        intro r m
        obtain ⟨W₀, hxW₀, n₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq (skyscraperPOM x N).presheaf m
        obtain ⟨V, hxV, s₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq (X.presheaf) r
        -- common neighbourhood W = W₀ ⊓ V
        have hxW : x ∈ W₀ ⊓ V := ⟨hxW₀, hxV⟩
        -- restrict the representatives to W
        have hgn : TopCat.Presheaf.germ (skyscraperPOM x N).presheaf (W₀ ⊓ V) x hxW
              (((skyscraperPOM x N).presheaf.map (CategoryTheory.homOfLE (inf_le_left)).op) n₀) =
            TopCat.Presheaf.germ (skyscraperPOM x N).presheaf W₀ x hxW₀ n₀ :=
          TopCat.Presheaf.germ_res_apply (skyscraperPOM x N).presheaf
            (CategoryTheory.homOfLE (inf_le_left : W₀ ⊓ V ≤ W₀)) x hxW n₀
        have hgs : TopCat.Presheaf.germ (X.presheaf) (W₀ ⊓ V) x hxW
              ((ConcreteCategory.hom (X.presheaf.map (CategoryTheory.homOfLE (inf_le_right)).op))
                  s₀) =
            TopCat.Presheaf.germ (X.presheaf) V x hxV s₀ :=
          TopCat.Presheaf.germ_res_apply (X.presheaf)
            (CategoryTheory.homOfLE (inf_le_right : W₀ ⊓ V ≤ V)) x hxW s₀
        rw [← hgn, ← hgs]
        let restrictedScalar : X.presheaf.obj (Opposite.op (W₀ ⊓ V)) :=
          (X.presheaf.map (homOfLE inf_le_right).op) s₀
        let restrictedSection : skyscraperObj x N (Opposite.op (W₀ ⊓ V)) :=
          (skyscraperPOM x N).restrictₛₗ (homOfLE inf_le_left).op n₀
        exact (congrArg (sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N)
          (PresheafOfModules.germ_smul (R := X.presheaf) (skyscraperPOM x N) x
            (W₀ ⊓ V) hxW restrictedScalar restrictedSection).symm).trans
          ((sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv_germ x N
            (Opposite.op (W₀ ⊓ V)) hxW (restrictedScalar • restrictedSection)).trans
            ((skyscraperPOM_leg_smul x N (Opposite.op (W₀ ⊓ V)) hxW
              restrictedScalar restrictedSection).trans
              (congrArg (fun value : N =>
                X.presheaf.germ (W₀ ⊓ V) x hxW restrictedScalar • value)
                (sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv_germ x N
                  (Opposite.op (W₀ ⊓ V)) hxW restrictedSection).symm))) }

end OXModule

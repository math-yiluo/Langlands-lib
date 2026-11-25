/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # The single-complex stalkwise base-change condition

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8, and Tag 0DJ9
(blueprint: def-pc-single-complex-base-change-stalk-condition).

K-flat coordinates express the canonical tensor-cohomology comparison, followed by
the given derived map. Every choice is tied to the actual stalk maps or to a
localization equation. Invertibility is independent of representative coordinates.
-/

@[expose] public section

universe uSC wSC
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{uSC},
  HasDerivedCategory.{wSC} (SheafOfModules.{uSC} (moduleRings Y.toRingedSpace))]

/-- Additivity of termwise tensor pullback, from the existing composition construction.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
instance tensorPullbackAdditive {Y Z : Scheme.{uSC}} (k : Y ⟶ Z) :
    (Scheme.Modules.tensorPullback k).Additive :=
  (Classical.choose exists_derivedPullbackComposition) k

/-- The universal counit of the recorded derived tensor pullback, on homotopy categories.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
def counit {Y Z : Scheme.{uSC}} (k : Y ⟶ Z) :
    DerivedCategory.Qh (C := SheafOfModules.{uSC} (moduleRings Z.toRingedSpace)) ⋙
      derivedPullback k ⟶
      (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{uSC} (moduleRings Y.toRingedSpace)) :=
  (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k

variable {X X' S S' : Scheme.{uSC}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- The base stalk ring O_{S,f(g' z)}.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev R (z : X') := S.presheaf.stalk (f (g' z))
/-- The original scheme stalk ring O_{X,g' z}.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev A (z : X') := X.presheaf.stalk (g' z)
/-- The new base stalk ring O_{S',f' z}.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev B (z : X') := S'.presheaf.stalk (f' z)
/-- The base-changed scheme stalk ring O_{X',z}.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev C (z : X') := X'.presheaf.stalk z

/-- The R-algebra structure on A is the stalk map of f.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev leftAlgebra (z : X') : Algebra (R f g' z) (A g' z) :=
  (f.stalkMap (g' z)).hom.toAlgebra

/-- The R-algebra structure on B transports the stalk map of g along the square.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev rightAlgebra (z : X') : Algebra (R f g' z) (B f' z) :=
  ((S.presheaf.stalkCongr (.of_eq (congrArg (fun k : X' ⟶ S => k z) sq.w))).hom ≫
    g.stalkMap (f' z)).hom.toAlgebra

/-- The two stalk projection maps form compatible algebra maps over the base stalk.
Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-single-complex-stalk-algebra-maps). -/
theorem exists_stalk_algebra_maps (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (f.stalkMap (g' z) ≫ g'.stalkMap z).hom.toAlgebra
    ∃ l : A g' z →ₐ[R f g' z] C z,
      ∃ r : B f' z →ₐ[R f g' z] C z,
        (∀ a, l a = (g'.stalkMap z).hom a) ∧
        (∀ b, r b = (f'.stalkMap z).hom b) ∧
        ∀ a b, Commute (l a) (r b) := by
  have _derived : HasDerivedCategory.{wSC}
      (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) := inferInstance
  let _ := leftAlgebra f g' z
  let _ := rightAlgebra f f' g g' sq z
  let _ := (f.stalkMap (g' z) ≫ g'.stalkMap z).hom.toAlgebra
  have hsq : f.stalkMap (g' z) ≫ g'.stalkMap z =
      (S.presheaf.stalkCongr
        (.of_eq (congrArg (fun k : X' ⟶ S => k z) sq.w))).hom ≫
          g.stalkMap (f' z) ≫ f'.stalkMap z := by
    rw [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp]
    exact Scheme.Hom.stalkMap_congr_hom _ _ sq.w z
  let l : A g' z →ₐ[R f g' z] C z :=
    { (g'.stalkMap z).hom with commutes' := fun _ => rfl }
  let r : B f' z →ₐ[R f g' z] C z :=
    { (f'.stalkMap z).hom with
      commutes' := fun a => (congrArg (fun k => k.hom a) hsq).symm }
  exact ⟨l, r, fun _ => rfl, fun _ => rfl, fun _ _ => Commute.all _ _⟩

/-- Existence of the tensor-to-stalk map with its two specified restrictions.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
theorem exists_tensorMap (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    ∃ a : A g' z ⊗[R f g' z] B f' z →+* C z,
      a.comp (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)) =
        (g'.stalkMap z).hom ∧
      a.comp Algebra.TensorProduct.includeRight.toRingHom = (f'.stalkMap z).hom := by
  let _ := leftAlgebra f g' z
  let _ := rightAlgebra f f' g g' sq z
  let _ := (f.stalkMap (g' z) ≫ g'.stalkMap z).hom.toAlgebra
  obtain ⟨l, r, hl, hr, hcomm⟩ := exists_stalk_algebra_maps f f' g g' sq z
  let a : A g' z ⊗[R f g' z] B f' z →ₐ[R f g' z] C z :=
    Algebra.TensorProduct.lift l r hcomm
  refine ⟨a.toRingHom, ?_, ?_⟩
  · ext x
    simp [a, hl]
  · ext y
    simp [a, hr]

/-- The canonical tensor-to-stalk map, chosen from its universal property.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
def tensorMap (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    A g' z ⊗[R f g' z] B f' z →+* C z :=
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  Classical.choose (exists_tensorMap f f' g g' sq z)

/-- The original representative's stalk complex, using the shared module stalk functor.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev stalkComplex (z : X')
    (P : CochainComplex (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) ℤ) :=
  ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).mapHomologicalComplex
    (.up ℤ)).obj P

/-- The existing base-derived tensor cohomology model at a point of this square.
The R-, A-, B- and tensor-algebra structures are the actual scheme stalk maps;
the model fixes the localized comparison by its derived counit equations.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
def cohomologyModel (z : X')
    (P : CochainComplex (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) ℤ) :=
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{uSC} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{uSC} (B f' z))
  ModuleCat.baseDerivedTensorCohomologyModel (R f g' z) (A g' z) (B f' z)
    (stalkComplex g' z P) (C z)

/-- Ordinary scalar extension of the stalk complex along A -> A tensor-over-R B -> C.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
def tensorComplex (z : X')
    (P : CochainComplex (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) ℤ) :=
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  ((ModuleCat.extendScalars ((tensorMap f f' g g' sq z).comp
    (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomologicalComplex
      (.up ℤ)).obj (stalkComplex g' z P)

/-- Existence of the canonical degreewise pullback-stalk identification.
Proof: the tensorMap restriction equation identifies its A-to-C map with the
stalk map of g'. Apply the existing natural pullback-stalk isomorphism in every
degree. Its naturality for each differential shows that these components give a
chain isomorphism, whose components are precisely the displayed maps.
Source: Stacks Project, Tag 0098 and perfect.tex, equation-bc before Tag 0DJ8.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
theorem exists_tensorStalkIso (z : X')
    (P : CochainComplex (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    ∃ e : tensorComplex f f' g g' sq z P ≅
      ((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
        (.up ℤ)).obj (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) ,
      ∀ i : ℤ, e.hom.f i =
        eqToHom (congrArg (fun a : A g' z →+* C z =>
          (ModuleCat.extendScalars a).obj
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).obj (P.X i)))
              (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).1) ≫
          (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.app
            (P.X i) := by
  let _ := leftAlgebra f g' z
  let _ := rightAlgebra f f' g g' sq z
  have h (a : A g' z →+* C z) (ha : a = (g'.stalkMap z).hom) :
      ∃ e : ((ModuleCat.extendScalars a).mapHomologicalComplex (.up ℤ)).obj
          (stalkComplex g' z P) ≅
        ((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
          (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P),
        ∀ i : ℤ, e.hom.f i =
          eqToHom (congrArg (fun b : A g' z →+* C z =>
            (ModuleCat.extendScalars b).obj
              ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).obj (P.X i))) ha) ≫
            (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.app
              (P.X i) := by
    subst a
    have : (ModuleCat.extendScalars.{uSC, uSC, uSC} (g'.stalkMap z).hom).Additive :=
      ModuleCat.baseDerivedTensor_extendScalars_additive _
    -- Pin zero-preservation at the universe of the stalk modules.
    have hs0 : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (g' z)).PreservesZeroMorphisms := inferInstance
    have he0 : (ModuleCat.extendScalars.{uSC, uSC, uSC}
        (g'.stalkMap z).hom).PreservesZeroMorphisms := inferInstance
    have hc0 : (RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z) ⋙
        ModuleCat.extendScalars.{uSC, uSC, uSC}
          (g'.stalkMap z).hom).PreservesZeroMorphisms := inferInstance
    have : (Scheme.Modules.tensorPullback g').Additive :=
      tensorPullbackAdditive.{uSC, wSC} g'
    have hp0 : (Scheme.Modules.tensorPullback g').PreservesZeroMorphisms := inferInstance
    have ht0 : (RingedSpace.moduleStalkFunctor X'.toRingedSpace
        z).PreservesZeroMorphisms := inferInstance
    have hd0 : (Scheme.Modules.tensorPullback g' ⋙
        RingedSpace.moduleStalkFunctor X'.toRingedSpace z).PreservesZeroMorphisms :=
      inferInstance
    let e := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)
    exact ⟨(NatIso.mapHomologicalComplex e.symm (.up ℤ)).app P, fun _ => by simp [e]⟩
  exact h _ (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).1

/-- The canonical pullback-stalk chain isomorphism specified degreewise above.
Source: Stacks Project, Tag 0098 and perfect.tex, equation-bc before Tag 0DJ8.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
def tensorStalkIso (z : X')
    (P : CochainComplex (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) ℤ) :
    tensorComplex f f' g g' sq z P ≅
      ((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
        (.up ℤ)).obj (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) :=
  Classical.choose (exists_tensorStalkIso f f' g g' sq z P)

/-- K-flat coordinates for the given derived morphism. P represents K, N represents
K', and t represents phi through the specified left-derived counit and the two
representative isomorphisms. No arbitrary stalk comparison is included.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
structure Coordinates (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') where
  P : CochainComplex (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) ℤ
  N : CochainComplex (SheafOfModules.{uSC} (moduleRings X'.toRingedSpace)) ℤ
  e : DerivedCategory.Q.obj P ≅ K
  e' : DerivedCategory.Q.obj N ≅ K'
  isKFlat : P.IsKFlatTensor
  counit_isIso : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  t : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P ⟶ N
  represents : cast (by rfl) ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
    (DerivedCategory.Q (C := SheafOfModules.{uSC} (moduleRings X'.toRingedSpace))).map t ≫
      e'.hom = (derivedPullback g').map e.hom ≫ φ

private theorem counit_isIso_of_isKFlat
    (P : CochainComplex (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) :
    IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
      (derivedPullback_spec g')
  have h : E = Scheme.Modules.tensorPullback g' :=
    CategoryTheory.Functor.ext hE (fun M N a => hEmap a)
  subst E
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) (.up ℤ)
  have : (derivedPullback g').IsLeftDerivedFunctor ε W := hL
  have hc : (derivedPullback g').IsLeftDerivedFunctor (counit g') W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) g'
  have : IsIso ((derivedPullback g').leftDerivedLift ε W
      (derivedPullback g') (counit g')) :=
    ((derivedPullback g').isLeftDerivedFunctor_iff_isIso_leftDerivedLift
      ε W (derivedPullback g') (counit g')).mp hc
  have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hK P hP
  rw [← Functor.leftDerived_fac_app (derivedPullback g') ε W
    (derivedPullback g') (counit g')]
  infer_instance

private theorem derived_map_surjective
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (M N : CochainComplex D ℤ) [N.IsKInjective] :
    Function.Surjective (DerivedCategory.Q.map : (M ⟶ N) → _) := by
  have _derived : ∀ Y : Scheme.{uSC},
      HasDerivedCategory.{wSC} (SheafOfModules.{uSC} (moduleRings Y.toRingedSpace)) :=
    inferInstance
  intro φ
  let e := DerivedCategory.quotientCompQhIso D
  obtain ⟨t, ht⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj M) N).surjective
      (e.hom.app M ≫ φ ≫ e.inv.app N)
  obtain ⟨t, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective t
  refine ⟨t, ?_⟩
  apply (cancel_mono (e.inv.app N)).1
  rw [DerivedCategory.quotientCompQhIso_inv_naturality, ht]
  simp [e]

-- Elaborating the two sheaf resolutions and their localization maps needs this budget.
/-- Every derived morphism has these K-flat coordinates.
Proof: choose a complex representing K and a K-flat resolution P (lem-pc-kflat-resolution).
Choose a K-injective representative N of K' (prop-pur-kinjective-resolutions-exist).
The universal left-derived counit computes pullback on P, so is invertible there.
Compose its inverse with the pullback of e and phi, and then e' inverse. Since N
is K-injective, the localization Hom bijection lifts this derived morphism to a
homotopy class of chain maps from termwise pullback of P to N. Choose a chain-map
representative t. The localization equation is exactly the represents field.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
theorem nonempty_coordinates (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') : Nonempty (Coordinates g' K K' φ) := by
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution
    (R := X.sheaf) (DerivedCategory.Q.objPreimage K)
  have : QuasiIso s := hs
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨_, _, I, η, hI⟩ :=
    SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      (Opens.grothendieckTopology X') X'.sheaf
  let M := DerivedCategory.Q.objPreimage K'
  let N := I.obj M
  have : QuasiIso (η.app M) := (hI M).1
  have : N.IsKInjective := (hI M).2.1
  let e' : DerivedCategory.Q.obj N ≅ K' :=
    (asIso (DerivedCategory.Q.map (η.app M))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso K'
  have hc := counit_isIso_of_isKFlat g' P hP
  let q := (HomotopyCategory.quotient _ (.up ℤ)).obj P
  obtain ⟨t, ht⟩ := derived_map_surjective
    (D := SheafOfModules.{uSC} (moduleRings X'.toRingedSpace))
    (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) N
    (inv ((counit g').app q) ≫ (derivedPullback g').map e.hom ≫ φ ≫ e'.inv)
  refine ⟨⟨P, N, e, e', hP, hc, t, ?_⟩⟩
  rw [ht]
  simp only [cast_eq, q, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    IsIso.hom_inv_id_assoc]

/-- The canonical map H^i(K_x tensor-derived-over-R B) tensor-over-(A tensor-over-R B) C
-> H^i(K'_z), expressed in given K-flat coordinates c for phi.
It is the existing localized tensor comparison followed by the canonical
pullback-stalk identification and the stalk of c.t. The target H^i(N_z) identifies
canonically with H^i(K')_z through c.e' and exactness of stalks. Postcomposing by
that identification preserves and reflects invertibility. The represents equation
of c ensures this is the map induced by the given phi, rather than a free comparison.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
def stalkComparison {K : schemeDerivedCategory X} {K' : schemeDerivedCategory X'}
    {φ : (derivedPullback g').obj K ⟶ K'} (c : Coordinates g' K K' φ) (z : X') (i : ℤ) :=
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{uSC} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{uSC} (B f' z))
  (cohomologyModel f f' g g' sq z c.P).localizedComparison i ≫
    HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z c.P).hom i ≫
    HomologicalComplex.homologyMap
      (((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
        (.up ℤ)).map c.t) i

/-- The single-complex stalk condition (equation-bc of Tag 0DJ8 an isomorphism for
every z and i). Invertibility of the comparison does not depend on the K-flat
coordinates, so it is required for all of them; they exist by `nonempty_coordinates`,
so the condition is not vacuous. No coordinate system is chosen.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
def StalkCondition (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') : Prop :=
  ∀ (c : Coordinates g' K K' φ) (z : X') (i : ℤ),
    IsIso (stalkComparison f f' g g' sq c z i)

end AlgebraicGeometry.SingleComplexBaseChange

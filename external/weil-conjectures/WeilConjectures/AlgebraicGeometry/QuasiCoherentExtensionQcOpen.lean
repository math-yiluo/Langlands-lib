/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Extension of a quasi-coherent module across a quasi-compact open

Source: Stacks Project, Properties, Lemma 01PE (lemma-extend-trivial), part (3)
and its proof (properties.tex, lines 2787--2843).
(blueprint: lem-weil-pbc-quasi-coherent-extension-qc-open)

Restriction to an open is expressed on the localized site with `SheafOfModules.over`,
on the `moduleRings` carrier, as in the sibling extension lemmas.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Transport quasi-coherence from the localized site to the open subscheme. -/
private theorem overEquiv_quasiCoherent (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) [M.IsQuasicoherent] :
    ((overEquiv U).functor.obj M).IsQuasicoherent := by
  have : ∀ W, (Over.post (X := W) U.overEquivalence.symm.functor).IsContinuous
      ((Opens.grothendieckTopology ↥U).over W)
      (((Opens.grothendieckTopology X).over U).over _) := fun W ↦
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.symm.functor _ _).overPost W)
  apply SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    (U.overEquivalence.symm.functor) _
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf)

/-- The pullback is the kernel of the difference map on the binary biproduct. -/
private theorem quasiCoherent_pullback {X : Scheme.{u}} {M N P : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [P.IsQuasicoherent]
    (f : M ⟶ P) (g : N ⟶ P) : (Limits.pullback f g).IsQuasicoherent := by
  let : Limits.HasFiniteBiproducts X.Modules :=
    Limits.HasFiniteBiproducts.of_hasFiniteProducts
  have := isQuasicoherent_biprod M N
  have h := isQuasicoherent_kernel (Limits.biprod.desc f (-g))
  let e : Limits.pullback f g ≅ Limits.kernel (Limits.biprod.desc f (-g)) :=
    (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g).conePointUniqueUpToIso
      (Limits.limit.isLimit _)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm h

/-- A quasi-coherent module and a map on a quasi-compact open extend across the open.
Source: Stacks Project, Properties, Lemma 01PE (lemma-extend-trivial), part (3)
and its proof (properties.tex, lines 2787--2843).
(blueprint: lem-weil-pbc-quasi-coherent-extension-qc-open)

Proof:
1. The open immersion is quasi-compact by hypothesis and quasi-separated because it is
   an open immersion (hence a monomorphism and separated), using
   lem-weil-pbc-open-immersion-monomorphism and def-weil-quasi-separated-morphism.
2. Restriction preserves quasi-coherence
   (lem-weil-pbc-module-restriction-open-immersion-colimits). Push forward the given
   module and the restriction of `F`; these are quasi-coherent by pqf-lem-pushforward-qcoh.
   Their direct sum is quasi-coherent (lem-weil-pbc-quasi-coherent-module-direct-sum).
   Form the map `d : F ⊞ j_*G ⟶ j_*(F|_U)` given sectionwise by restriction minus
   the pushed-forward map.
3. Let `H = Ker d` and let `ψ` be the first projection. Quasi-coherence of kernels
   gives quasi-coherence of `H` (lem-weil-pbc-quasi-coherent-module-kernel).
4. Over `U`, projection to the second component gives an isomorphism
   `α : H|_U ≅ G`, with inverse `g ↦ (φ(g), g)`, and the defining equation gives
   `ψ|_U = α.hom ≫ φ`; restriction is as in
   lem-weil-pbc-module-restriction-open-immersion-colimits.
-/
theorem exists_quasiCoherent_extension_of_quasiCompact_open
    (X : Scheme.{u}) (U : X.Opens) (hU : QuasiCompact U.ι)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [F.IsQuasicoherent]
    (G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) [G.IsQuasicoherent]
    (φ : G ⟶ F.over U) :
    ∃ (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)), H.IsQuasicoherent ∧
      ∃ (ψ : H ⟶ F) (α : H.over U ≅ G),
        (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).map ψ = α.hom ≫ φ := by
  let : QuasiCompact U.ι := hU
  let E := overEquiv U
  let L := restrictFunctor U.ι
  have : Limits.PreservesLimitsOfSize.{u, u} L := preservesLimitsOfSize_restrictFunctor U.ι
  have hsmall : Limits.PreservesLimitsOfSize.{0, 0} L :=
    Limits.preservesSmallestLimits_of_preservesLimits L
  let R := pushforward U.ι
  let A := restrictAdjunction U.ι
  let G' := E.functor.obj G
  have : G'.IsQuasicoherent := overEquiv_quasiCoherent X U G
  let φ' : G' ⟶ L.obj F := E.functor.map φ ≫ (overFunctorEquiv U).hom.app F
  let a : F ⟶ R.obj (L.obj F) := A.unit.app F
  let b : R.obj G' ⟶ R.obj (L.obj F) := R.map φ'
  have : (R.obj G').IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated U.ι G'
  have : (R.obj (L.obj F)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated U.ι (L.obj F)
  let H := Limits.pullback a b
  have hH : H.IsQuasicoherent := quasiCoherent_pullback a b
  have ha : L.map a ≫ A.counit.app (L.obj F) = 𝟙 _ :=
    A.left_triangle_components F
  have : IsIso (L.map a) := by
    have he : L.map a = inv (A.counit.app (L.obj F)) := by
      apply (cancel_mono (A.counit.app (L.obj F))).1
      simpa using ha
    rw [he]
    infer_instance
  have hshape : Limits.PreservesLimitsOfShape Limits.WalkingCospan L :=
    hsmall.preservesLimitsOfShape
  have : Limits.PreservesLimit (Limits.cospan a b) L := hshape.preservesLimit
  let e : L.obj H ≅ G' :=
    Limits.PreservesPullback.iso L a b ≪≫
      asIso (Limits.pullback.snd (L.map a) (L.map b)) ≪≫
      asIso (A.counit.app G')
  have he : e.hom = L.map (Limits.pullback.snd a b) ≫ A.counit.app G' := by
    simp [e]
  have hfac : L.map (Limits.pullback.fst a b) = e.hom ≫ φ' := by
    rw [he, Category.assoc, ← A.counit_naturality φ']
    change L.map (Limits.pullback.fst a b) =
      L.map (Limits.pullback.snd a b) ≫ L.map b ≫ A.counit.app (L.obj F)
    rw [← L.map_comp_assoc, ← Limits.pullback.condition, L.map_comp, Category.assoc, ha,
      Category.comp_id]
  let α : H.over U ≅ G := E.functor.preimageIso ((overFunctorEquiv U).app H ≪≫ e)
  refine ⟨H, hH, Limits.pullback.fst a b, α, ?_⟩
  apply E.functor.map_injective
  rw [Functor.map_comp]
  have hα : E.functor.map α.hom = (overFunctorEquiv U).hom.app H ≫ e.hom := by
    exact E.functor.map_preimage _
  rw [hα, Category.assoc]
  apply (cancel_mono ((overFunctorEquiv U).hom.app F)).1
  rw [Category.assoc, Category.assoc, ← hfac]
  exact (overFunctorEquiv U).hom.naturality (Limits.pullback.fst a b)

end AlgebraicGeometry.Scheme.Modules

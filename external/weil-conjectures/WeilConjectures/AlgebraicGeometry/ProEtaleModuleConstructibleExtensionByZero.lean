/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# Extension by zero of constructible module objects

Source: the open–closed stratification argument for constructible sheaves.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private instance lowerShriek_unit_iso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).unit := by
  have : IsIso (openImmersionLowerShriekAdjunction Ab.{u + 1} j).unit :=
    (openImmersionAdjunctionTriple Ab.{u + 1} j).isIso_unit_iff_isIso_counit.mpr
      (isIso_openImmersionRestrictionLowerStarAdjunction_counit Ab.{u + 1} j)
  let e := (openImmersionLowerShriekAdjunction Ab.{u + 1} j).fullyFaithfulLOfIsIsoUnit
  let := e.full
  let := e.faithful
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private lemma restriction_pushforward_isZero {U W X : Scheme.{u}}
    (g : W ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hgj : Set.range g.base ∩ Set.range j.base = ∅)
    (F : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) :
    IsZero ((openImmersionRestriction Ab.{u + 1} j).obj ((g)_*[Ab.{u + 1}].obj F)) := by
  refine Sheaf.isZero_of_isZero_obj _ ?_
  rintro ⟨T⟩
  let W' := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj
    ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj T)
  have : IsEmpty W'.left := by
    refine ⟨fun z ↦ ?_⟩
    have hz : (pullback.fst (T.hom ≫ j) g ≫ T.hom ≫ j).base z ∈
        Set.range g.base ∩ Set.range j.base := by
      refine ⟨?_, ⟨T.hom.base (pullback.fst (T.hom ≫ j) g z), rfl⟩⟩
      rw [pullback.condition]
      exact ⟨_, rfl⟩
    rw [hgj] at hz
    exact hz
  exact (isZero_zero _).of_iso
    ((Scheme.ProEt.isTerminalSectionsOfIsEmpty F W').uniqueUpToIso
      HasZeroObject.zeroIsTerminal)

private lemma pullback_lowerShriek_isZero {U W X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : W ⟶ X)
    (hjg : Set.range j.base ∩ Set.range g.base = ∅)
    (F : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :
    IsZero ((g)^*[Ab.{u + 1}].obj ((j)_!open[Ab.{u + 1}].obj F)) := by
  have hz : IsInitial ((g)^*[Ab.{u + 1}].obj ((j)_!open[Ab.{u + 1}].obj F)) := by
    refine IsInitial.ofUnique (h := fun H ↦ ?_)
    haveI : Unique (F ⟶ (openImmersionRestriction Ab.{u + 1} j).obj
        ((g)_*[Ab.{u + 1}].obj H)) := by
      have h := restriction_pushforward_isZero g j (by rwa [Set.inter_comm]) H
      exact ⟨⟨h.isTerminal.from F⟩, fun a ↦ h.isTerminal.hom_ext _ _⟩
    exact Equiv.unique
      (((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ H).trans
        ((openImmersionLowerShriekAdjunction Ab.{u + 1} j).homEquiv F _))
  exact (isZero_zero _).of_iso (hz.uniqueUpToIso HasZeroObject.zeroIsInitial)

private lemma finitePresentation_of_isZero {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod _ R) (hM : IsZero M) : Mod.IsFinitelyPresented R M := by
  exact ⟨0, 0, 𝟙 _, ⟨hM.iso (isZero_cokernel_of_epi (𝟙 (Mod.finiteFree R 0)))⟩⟩

private lemma localFinitePresentation_of_isZero {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod _ R) (hM : IsZero M) : IsLocallyFinitelyPresented R M := by
  refine ⟨Precoverage.ZeroHypercover.singleton (𝟙 X)
    (Precoverage.mem_coverings_of_isIso (J := Scheme.proetalePrecoverage) (𝟙 X)), fun i ↦ ?_⟩
  exact finitePresentation_of_isZero _ _
    (((𝟙 X)^*[Ab.{u + 1}].mapMod R).map_isZero hM)

private lemma constructible_of_restrictions {U Z X : Scheme.{u}}
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] (M : Mod _ R)
    (hU : IsConstructibleModuleObject ((j)^*[Ab.{u + 1}].obj R)
      (((j)^*[Ab.{u + 1}].mapMod R).obj M))
    (hZ : IsConstructibleModuleObject ((i)^*[Ab.{u + 1}].obj R)
      (((i)^*[Ab.{u + 1}].mapMod R).obj M)) : IsConstructibleModuleObject R M := by
  obtain ⟨SU, hSU⟩ := hU
  obtain ⟨SZ, hSZ⟩ := hZ
  refine ⟨Scheme.Stratification.openClosed j i hij SU SZ, fun k ↦ ?_⟩
  change IsLocallyFinitelyPresented _
    (((ProEtale.upperStar Ab.{u + 1}
      (Sum.rec (motive := fun s ↦ Sum.elim SU.domain SZ.domain s ⟶ X)
        (fun l ↦ SU.immersion l ≫ j) (fun l ↦ SZ.immersion l ≫ i)
        (finSumFinEquiv.symm k))).mapMod R).obj M)
  generalize finSumFinEquiv.symm k = s
  rcases s with l | l
  · let e := Functor.mapModCompIso (j)^*[Ab.{u + 1}] (SU.immersion l)^*[Ab.{u + 1}]
      (upperStarComp Ab.{u + 1} (SU.immersion l) j).inv R
    apply localFinitePresentation_of_comap
      (Functor.compAlgHom (j)^*[Ab.{u + 1}] (SU.immersion l)^*[Ab.{u + 1}]
        (upperStarComp Ab.{u + 1} (SU.immersion l) j).inv R)
    exact localFinitePresentation_of_iso (e.app M) (hSU l)
  · let e := Functor.mapModCompIso (i)^*[Ab.{u + 1}] (SZ.immersion l)^*[Ab.{u + 1}]
      (upperStarComp Ab.{u + 1} (SZ.immersion l) i).inv R
    apply localFinitePresentation_of_comap
      (Functor.compAlgHom (i)^*[Ab.{u + 1}] (SZ.immersion l)^*[Ab.{u + 1}]
        (upperStarComp Ab.{u + 1} (SZ.immersion l) i).inv R)
    exact localFinitePresentation_of_iso (e.app M) (hSZ l)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma isIso_linear_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      ((j)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))) :
    IsIso ((linearOpenImmersionLowerShriekAdjunction Λ j).unit.app M) := by
  have : IsIso ((Mod.forget _).map
      ((linearOpenImmersionLowerShriekAdjunction Λ j).unit.app M)) := by
    change IsIso (((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).homEquiv
      M.X _ (𝟙 _)))
    rw [Adjunction.homEquiv_id]
    infer_instance
  exact isIso_of_reflects_iso _ (Mod.forget _)

/-- Extension by zero along a quasi-compact open immersion preserves constructible module
objects.

Source: `ConstructibleSheaf/OpenClosed.lean`, the open–closed stratification construction,
and the pro-étale open-immersion adjunction triple.
Restrict to the open subscheme and its closed complement. The unit of the linearized
extension-by-zero adjunction is an isomorphism, because its underlying map is the unit of
extension by zero for abelian sheaves. Thus the open restriction is the original module
with scalars transported along the coefficient isomorphism. On the closed complement the
underlying sheaf is zero: the two adjunctions identify maps out of its inverse image with
maps into the restriction of a pushforward from the complement, whose sections are sections
over empty fibre products. Faithfulness of the module forgetful functor reflects this
vanishing. The zero module has a rank-zero finite presentation. Concatenate the open
stratification with the trivial stratification on the complement, transporting the
presentations through pullback composition. Quasi-compactness makes the resulting strata
constructible in the ambient scheme. Empty schemes and rank zero are included.
(auxiliary; not a blueprint node) -/
theorem isConstructibleModuleObject_openImmersionLowerShriek
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ U) M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) ((j)_!open⟦Λ⟧.obj M) := by
  apply constructible_of_restrictions j j.closedComplement j.range_closedComplement
  · have := isIso_linear_unit Λ j ((Mod.comap (condensedPullbackHom Λ j)).obj M)
    exact constructible_of_iso
      (asIso ((linearOpenImmersionLowerShriekAdjunction Λ j).unit.app
        ((Mod.comap (condensedPullbackHom Λ j)).obj M)))
      (constructible_comap (condensedPullbackHom Λ j) hM)
  · apply isConstructibleModuleObject_of_isZero
    have hz := pullback_lowerShriek_isZero j j.closedComplement
      (by rw [j.range_closedComplement]; exact Set.inter_compl_self _) M.X
    apply (IsZero.iff_id_eq_zero _).2
    exact Mod.hom_ext _ _ (hz.eq_of_src _ _)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

section

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

private lemma constructible_of_isZero {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod _ R) (hM : IsZero M) : IsConstructibleModuleObject R M := by
  refine ⟨Scheme.Stratification.trivial X, fun i ↦ ?_⟩
  exact localFinitePresentation_of_isZero _ _
    (((𝟙 X)^*[Ab.{u + 1}].mapMod R).map_isZero hM)

end

end AlgebraicGeometry.ProEtale

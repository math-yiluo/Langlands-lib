/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.LocallyConstantFiniteValuesFiniteType
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.AlgebraicGeometry.FiniteTypeEtaleModuleStalk
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Finite values of locally constant etale module sheaves

Source: Stacks Project, Tags 03RU, 03RW(3), and 093N(1); the equivalences are
agent-formulated from these definitions
(blueprint: lem-weil-pbc-finite-locally-constant-module-values).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private instance : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @Etale))

private noncomputable def constantValuePullbackIso
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : Y.Etale) (M : ModuleCat.{u + 1} Λ)
    (e : F.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj M) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
  (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) U F).symm ≪≫
    (Etale.overSheafEquiv U (ModuleCat.{u + 1} Λ)).functor.mapIso e ≪≫
    ((Etale.overEquiv U).constantSheafSheafCongrIso
      (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) CategoryTheory.Over.mkIdTerminal).app M

private noncomputable def constantValueStalkIso
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : Y.Etale) (M : ModuleCat.{u + 1} Λ)
    (e : F.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj M)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    ((pointSmallEtale (s ≫ U.hom)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F ≅ M := by
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.hom s).app F).symm ≪≫
    (pointSmallEtale s).sheafFiber.mapIso (constantValuePullbackIso F U M e) ≪≫
    (pointSmallEtale s).sheafFiberConstantSheafIso M

private theorem finiteSheaf_of_finiteType
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsFiniteTypeEtaleModuleSheaf F) : IsFiniteSheaf F := by
  classical
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨𝒰, h𝒰⟩ := hF
  constructor
  intro Ω _ _ s
  obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (s default)
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) s x hx
  obtain ⟨n, π, hπ⟩ := h𝒰 i
  let U := 𝒰.etalePrecoverageToEtale i
  let E := (Etale.overSheafEquiv U (ModuleCat.{u + 1} Λ)).functor
  let P := (constantSheaf (Y.smallEtaleTopology.over U)
    (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ (Fin n → Λ))
  let e : E.obj P ≅ (constantSheaf U.left.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ (Fin n → Λ)) :=
    ((Etale.overEquiv U).constantSheafSheafCongrIso
      (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) CategoryTheory.Over.mkIdTerminal).app _
  let q := ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).map (E.map π)
  let eP := ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).mapIso e ≪≫
    (pointSmallEtale t).sheafFiberConstantSheafIso (ModuleCat.of Λ (Fin n → Λ))
  have : Finite (((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj (E.obj P)) :=
    Finite.of_equiv (Fin n → Λ) eP.toLinearEquiv.toEquiv.symm
  have : E.PreservesEpimorphisms := inferInstance
  have : CategoryTheory.Limits.HasProducts.{u} (ModuleCat.{u + 1} Λ) := by
    have : CategoryTheory.Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
    intro J
    infer_instance
  have : ((pointSmallEtale t).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).IsLeftAdjoint := inferInstance
  have : ((pointSmallEtale t).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).PreservesEpimorphisms := inferInstance
  have hq : Epi q := by infer_instance
  have : Finite
      (((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj (E.obj (F.over U))) :=
    Finite.of_surjective q ((ModuleCat.epi_iff_surjective q).mp hq)
  have hgen := (ModuleCat.isFinitelyGenerated_iff
    (((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj (E.obj (F.over U)))).2
      (Module.Finite.of_finite (R := Λ))
  have eF := ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).mapIso
    (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) U F) ≪≫
    (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (𝒰.f i) t).app F
  simpa only [ht] using hgen.of_iso eF

/-- Over a finite commutative ring, the existence of a trivialization with finite module
values, finite local constancy, and local constancy together with finite type are equivalent.
Every geometric stalk through a member of any such trivialization is isomorphic, as a
module, to that member's constant value.

Proof:
1. Transport a constant-value trivialization from the localized site to the small etale
   site of the cover member, using `overSheafEquivFunctorObjOverIso` and
   `constantSheafSheafCongrIso`. Compose `upperStarCompSheafFiberIso` with its stalk and
   `sheafFiberConstantSheafIso` to identify the original stalk with the constant value.
   These are isomorphisms in ModuleCat, so no separate scalar-linearity argument is needed.
2. Finite type implies finite stalks at separably closed points: lift a point through its
   generating cover and apply the stalk functor to the generating epimorphism. The site
   equivalence preserves epimorphisms, and the stalk functor does so because it is left
   adjoint to the skyscraper functor. The source stalk is the finite free module, so its
   quotient is finite and hence finitely generated. Transport back by the pullback-stalk
   isomorphism.
3. Finite constant values are finitely generated; apply
   `locallyConstant_finiteValues_isFiniteType` to obtain finite type. The given datum
   supplies local constancy, and step 2 supplies the finite-sheaf predicate.
4. Conversely, remove empty members of a locally constant cover. This remains a cover:
   every point is covered by a member containing a point. On each remaining member,
   choose a point and the separable closure of its residue field. Step 1 identifies its
   constant value with a finitely generated stalk. Over the finite coefficient ring,
   that constant value is a finite set.
5. Combine these implications to obtain both equivalences. The moreover assertion is
   step 1 for the specified member and geometric point; it requires no finiteness.

The existing finite-sheaf predicate uses finitely generated stalks at separably closed
points; over a finite ring this is equivalent to finite stalks. Testing at algebraically
closed points is equivalent by invariance under algebraic closure of the geometric field.
Source: Stacks Project, Tags 03RU, 03RW(3), 093N(1), and the stalk calculations of 03PN
(blueprint: lem-weil-pbc-finite-locally-constant-module-values). -/
theorem finite_locally_constant_module_values_iff
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let finiteValues : Prop := ∃ d : LocallyConstantDatum F, ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty (F.over (d.cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M)
    (finiteValues ↔ IsFiniteLocallyConstantSheaf F) ∧
      (finiteValues ↔ IsLocallyConstantSheaf F ∧ IsFiniteTypeEtaleModuleSheaf F) ∧
      ∀ (d : LocallyConstantDatum F) (M : d.cover.I₀ → ModuleCat.{u + 1} Λ),
        (∀ i : d.cover.I₀, Finite (M i) ∧
          Nonempty (F.over (d.cover.etalePrecoverageToEtale i) ≅
            (constantSheaf (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
              (ModuleCat.{u + 1} Λ)).obj (M i))) →
        ∀ (i : d.cover.I₀) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (s : Spec (.of Ω) ⟶ d.cover.X i),
          Nonempty (((pointSmallEtale (s ≫ d.cover.f i)).sheafFiber
            (A := ModuleCat.{u + 1} Λ)).obj F ≅ M i) := by
  classical
  dsimp only
  let finiteValues : Prop := ∃ d : LocallyConstantDatum F, ∀ i : d.cover.I₀,
    ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
      Nonempty (F.over (d.cover.etalePrecoverageToEtale i) ≅
        (constantSheaf (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} Λ)).obj M)
  have toFiniteType : finiteValues → IsFiniteTypeEtaleModuleSheaf F := by
    rintro ⟨d, hd⟩
    choose M hM e using hd
    have hfinite (i : d.cover.I₀) : Module.Finite Λ (M i) := by
      have := hM i
      exact Module.Finite.of_finite
    exact (locallyConstant_finiteValues_isFiniteType F d.cover M hfinite
      (fun i ↦ (e i).some)).1
  have toFiniteLocallyConstant : finiteValues → IsFiniteLocallyConstantSheaf F := by
    rintro h
    have htype := toFiniteType h
    obtain ⟨d, -⟩ := h
    exact { toIsLocallyConstantSheaf := ⟨⟨d⟩⟩
            toIsFiniteSheaf := finiteSheaf_of_finiteType F htype }
  have fromFiniteLocallyConstant : IsFiniteLocallyConstantSheaf F → finiteValues := by
    intro hF
    have := hF
    obtain ⟨d₀⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
    let 𝒰 : Cover.{u} etalePrecoverage Y :=
      { I₀ := { i : d₀.cover.I₀ // Nonempty (d₀.cover.X i) }
        X i := d₀.cover.X i.1
        f i := d₀.cover.f i.1
        mem₀ := by
          refine (presieve₀_mem_precoverage_iff _).mpr
            ⟨fun y ↦ ?_, fun i ↦ d₀.cover.map_prop i.1⟩
          obtain ⟨i, x, hx⟩ := d₀.cover.exists_eq y
          exact ⟨⟨i, ⟨x⟩⟩, x, hx⟩ }
    let d : LocallyConstantDatum F := ⟨𝒰, fun i ↦ d₀.isConstant i.1⟩
    refine ⟨d, fun i ↦ ?_⟩
    have := d.isConstant i
    obtain ⟨M, ⟨e⟩⟩ := (F.over (d.cover.etalePrecoverageToEtale i)).mem_essImage_of_isConstant
    let U := d.cover.etalePrecoverageToEtale i
    have : Nonempty U.left := i.2
    let x : U.left := Classical.arbitrary _
    let Ω := SeparableClosure (U.left.residueField x)
    let s : Spec (.of Ω) ⟶ U.left := (SpecToEquivOfField Ω _).2
      ⟨x, CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)⟩
    have hgen := (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (F := F) Ω (s ≫ U.hom)).of_iso (constantValueStalkIso F U M e.symm s)
    have : Module.Finite Λ M := (ModuleCat.isFinitelyGenerated_iff M).1 hgen
    exact ⟨M, Module.finite_of_finite Λ, ⟨e.symm⟩⟩
  refine ⟨⟨toFiniteLocallyConstant, fromFiniteLocallyConstant⟩, ⟨?_, ?_⟩, ?_⟩
  · intro h
    have := toFiniteLocallyConstant h
    exact ⟨inferInstance, toFiniteType h⟩
  · rintro ⟨hlocal, htype⟩
    exact fromFiniteLocallyConstant
      { toIsLocallyConstantSheaf := hlocal
        toIsFiniteSheaf := finiteSheaf_of_finiteType F htype }
  · intro d M hM i Ω _ _ s
    exact ⟨constantValueStalkIso F (d.cover.etalePrecoverageToEtale i)
      (M i) (hM i).2.some s⟩

end AlgebraicGeometry.Scheme

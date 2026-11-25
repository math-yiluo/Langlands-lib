/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedAmbientDirectSums
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Ambient coproducts and quasi-coherent cohomology

Source: Stacks Project, Lemma 08DT and Section 01LA, item (3).
The proofs use the termwise ambient coproduct and its cohomology comparison, together
with the source library's proved closure of quasi-coherent modules under arbitrary sums.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

local instance instHasColimitsOfShape_derivedQCohDirectSumsAux (X : Scheme.{u}) (I : Type u) :
    HasColimitsOfShape (Discrete I)
      (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  have : HasColimitsOfShape (Discrete I) C := inferInstance
  refine ⟨fun F ↦ ?_⟩
  have (n : ℤ) : HasColimit (F ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    HasColimitsOfShape.has_colimit _
  exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩

/-- The ambient derived category of sheaves of modules has coproducts
(blueprint: lem-pc-derived-ambient-has-coproducts). The proof chooses representatives
for each derived object, forms the termwise coproduct complex, and applies
`derivedAmbientDirectSums`; the resulting coproduct cocone is transported along the
chosen representative isomorphisms.
Source: Stacks Project, Lemma 08DT. Proof: choose representatives for each derived
object, form the termwise coproduct complex, and apply `derivedAmbientDirectSums` to
obtain the coproduct cocone and its universal property; choice of representatives
assembles these cocones for every small discrete diagram. -/
theorem derivedAmbientHasCoproducts (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    HasCoproducts.{u} (schemeDerivedCategory X) := by
  classical
  let Q := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let K {I : Type u} (E : I → schemeDerivedCategory X) := fun i ↦ Q.objPreimage (E i)
  let e {I : Type u} (E : I → schemeDerivedCategory X) :=
    fun i ↦ Q.objObjPreimageIso (E i)
  let c {I : Type u} (E : I → schemeDerivedCategory X) : Cofan E :=
    Cofan.mk (Q.obj (∐ K E)) (fun i ↦ (e E i).inv ≫ Q.map (Sigma.ι (K E) i))
  exact hasCoproducts_of_colimit_cofans (fun E ↦ c E)
    (fun E ↦ (derivedAmbientDirectSums X _ E (K E) (e E)).1.some)

/-- Quasi-coherent cohomology is closed under ambient derived coproducts
(blueprint: lem-pc-derived-qcoh-closed-coproducts). The proof identifies cohomology of
the ambient coproduct with direct sums, writes each direct sum as a filtered colimit of
finite sums, and applies finite-sum and filtered-colimit quasi-coherence closure.
Source: Stacks Project, Lemma 08DT. Proof: `derivedAmbientDirectSums` identifies each
cohomology sheaf of the ambient coproduct with the direct sum of the input cohomology
sheaves. Express that direct sum as the filtered colimit of finite partial sums;
`isQuasicoherent_biprod` proves the finite case and
`quasiCoherentModuleColimitAffineSections` proves closure under the filtered colimit. -/
theorem schemeDerivedQCohClosedUnderCoproducts (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (I : Type u) :
    (schemeDerivedQCohProperty X).IsClosedUnderColimitsOfShape (Discrete I) := by
  classical
  constructor
  rintro Y ⟨p⟩ q
  let Q := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let E := fun i : I ↦ p.diag.obj ⟨i⟩
  let K := fun i ↦ Q.objPreimage (E i)
  let e := fun i ↦ Q.objObjPreimageIso (E i)
  let c : Cofan E :=
    Cofan.mk (Q.obj (∐ K)) (fun i ↦ (e i).inv ≫ Q.map (Sigma.ι K i))
  obtain ⟨⟨hc⟩, hH⟩ := derivedAmbientDirectSums X I E K e
  let c' := (Cocone.precompose (Discrete.natIsoFunctor (F := p.diag)).inv).obj
    p.cocone
  have hc' : IsColimit c' :=
    (IsColimit.precomposeInvEquiv Discrete.natIsoFunctor p.cocone).symm p.isColimit
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) q
  have hM : ∀ i : I, (H.obj (E i)).IsQuasicoherent :=
    fun i ↦ p.prop_diag_obj ⟨i⟩ q
  -- The proved arbitrary-sum theorem bypasses the finite-sum/filtered-colimit plan.
  have hsum : (∐ (fun i : I ↦ H.obj (E i))).IsQuasicoherent :=
    @Scheme.Modules.isQuasicoherent_sigma X I (fun i ↦ H.obj (E i)) hM
  have hcomparison : IsIso (Sigma.desc (fun i ↦ H.map (c.inj i))) := hH q
  let comparison := asIso (Sigma.desc (fun i ↦ H.map (c.inj i)))
  let iso := comparison ≪≫ H.mapIso (hc.coconePointUniqueUpToIso hc')
  exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    iso hsum

end AlgebraicGeometry

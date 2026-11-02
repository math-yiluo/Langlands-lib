import Langlands.Sheaf.Renard.SheafGermUnitIsoStatements

/-!
# The canonical germ unit identifies a sheaf with its germ sheaf

Descent of identity is the inverse on original sections. Its actual lifted
and direct sheaf morphisms give the specified canonical natural isomorphisms.
-/

open CategoryTheory Opposite

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- The original germs of descent of identity recover the given germ family. -/
theorem sectionGerms_rawGermDesc_id (G : BasisSheaf.{u,v} B) (U : BasisOpen B)
    (s : GermSections G.obj.obj U.obj) :
    sectionGerms G.obj.obj U (rawGermDesc (G := G) (𝟙 G.obj.obj) U s) = s := by
  apply GermSections.ext
  intro x
  change rawGerm G.obj.obj U x.val x.property
    (rawGermDesc (G := G) (𝟙 G.obj.obj) U s) = s.val x
  rw [rawGermDesc_germ]
  exact ConcreteCategory.congr_hom (rawStalkMap_id G.obj.obj x.val) (s.val x)

/-- On every basis open the actual original-section map is bijective. -/
theorem sheafSectionGermsBijective (G : BasisSheaf.{u,v} B) :
    SheafSectionGermsBijectiveStatement G := by
  intro U
  refine ⟨?_, ?_⟩
  · intro s t h
    have hi := congrArg (rawGermDesc (G := G) (𝟙 G.obj.obj) U) h
    simpa only [rawGermDesc_sectionGerms, NatTrans.id_app, AddCommGrpCat.id_apply] using hi
  · intro s
    exact ⟨rawGermDesc (G := G) (𝟙 G.obj.obj) U s,
      sectionGerms_rawGermDesc_id G U s⟩

/-- The lifted component has precisely the canonical unit and descent of identity. -/
noncomputable def sheafGermLiftUnitIso (G : BasisSheaf.{u,v} B) :
    (sheafLiftJoint.{u,v} B).obj G ≅ (germSheafFunctor.{u,v} B).obj G.obj where
  hom := ObjectProperty.homMk ((germSheafLiftUnit.{u,v} B).app G.obj)
  inv := liftedGermDesc.{u,v} (𝟙 G.obj)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    change (germSheafLiftUnit.{u,v} B).app G.obj ≫
      (sheafForget B).map (liftedGermDesc (𝟙 G.obj)) = 𝟙 _
    rw [liftedGermDesc_factorization]
    exact CategoryTheory.Functor.map_id _ _
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro s
    exact sectionGerms_rawGermDesc_id G U.unop s

/-- Invertibility concerns the published unit itself in the presheaf category. -/
theorem sheafGermLiftUnitIsIso (G : BasisSheaf.{u,v} B) :
    SheafGermLiftUnitIsIsoStatement G := by
  change IsIso ((sheafForget.{u,max u v} B).map (sheafGermLiftUnitIso G).hom)
  infer_instance

/-- Actual canonical natural identification for every original value universe. -/
noncomputable def sheafGermLiftUnitNatIso (B : OpenBasis X) :
    sheafLiftJoint.{u,v} B ≅ sheafForget.{u,v} B ⋙ germSheafFunctor.{u,v} B :=
  NatIso.ofComponents sheafGermLiftUnitIso
    (fun φ => ObjectProperty.hom_ext _ ((germSheafLiftUnit B).naturality φ.hom))

/-- The natural isomorphism's forward component is the literal lifted canonical unit. -/
@[simp]
theorem sheafGermLiftUnitNatIso_hom_app (G : BasisSheaf.{u,v} B) :
    (sheafForget.{u,max u v} B).map ((sheafGermLiftUnitNatIso.{u,v} B).hom.app G) =
      (germSheafLiftUnit.{u,v} B).app G.obj := rfl

/-- Its inverse component is the literal lifted descent of identity. -/
@[simp]
theorem sheafGermLiftUnitNatIso_inv_app (G : BasisSheaf.{u,v} B) :
    (sheafGermLiftUnitNatIso.{u,v} B).inv.app G = liftedGermDesc.{u,v} (𝟙 G.obj) := rfl

/-- The direct component at the joint universe has the specified original-valued inverse. -/
noncomputable def sheafGermUnitIso (G : BasisSheaf.{u,max u v} B) :
    G ≅ (germSheafFunctor.{u,max u v} B).obj G.obj where
  hom := ObjectProperty.homMk ((germSheafUnit.{u,v} B).app G.obj)
  inv := germDesc.{u,v} (𝟙 G.obj)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact germDesc_factorization (𝟙 G.obj)
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro s
    exact sectionGerms_rawGermDesc_id G U.unop s

/-- The actual direct canonical presheaf unit is invertible. -/
theorem sheafGermUnitIsIso (G : BasisSheaf.{u,max u v} B) :
    SheafGermUnitIsIsoStatement.{u,v} G := by
  change IsIso ((sheafForget.{u,max u v} B).map (sheafGermUnitIso.{u,v} G).hom)
  infer_instance

/-- The identity-source canonical natural identification at the joint value universe. -/
noncomputable def sheafGermUnitNatIso (B : OpenBasis X) :
    𝟭 (BasisSheaf.{u,max u v} B) ≅
      sheafForget.{u,max u v} B ⋙ germSheafFunctor.{u,max u v} B :=
  NatIso.ofComponents sheafGermUnitIso
    (fun φ => ObjectProperty.hom_ext _ ((germSheafUnit.{u,v} B).naturality φ.hom))

/-- The direct natural isomorphism has the exact published unit as underlying hom. -/
@[simp]
theorem sheafGermUnitNatIso_hom_app (G : BasisSheaf.{u,max u v} B) :
    (sheafForget.{u,max u v} B).map ((sheafGermUnitNatIso.{u,v} B).hom.app G) =
      (germSheafUnit.{u,v} B).app G.obj := rfl

/-- Its inverse component is exactly direct descent of identity. -/
@[simp]
theorem sheafGermUnitNatIso_inv_app (G : BasisSheaf.{u,max u v} B) :
    (sheafGermUnitNatIso.{u,v} B).inv.app G = germDesc.{u,v} (𝟙 G.obj) := rfl

/-- The full unchanged five-part statement, with independent space and value universes. -/
theorem renardSheafGermUnitIso : RenardSheafGermUnitIsoStatement.{u,v} := by
  intro X _ B
  refine ⟨sheafSectionGermsBijective, sheafGermLiftUnitIsIso, ?_,
    sheafGermUnitIsIso, ?_⟩
  · exact ⟨sheafGermLiftUnitNatIso B, fun _ => ⟨rfl, rfl⟩⟩
  · exact ⟨sheafGermUnitNatIso B, fun _ => ⟨rfl, rfl⟩⟩

end Langlands.Sheaf.Renard

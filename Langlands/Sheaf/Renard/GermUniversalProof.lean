import Langlands.Sheaf.Renard.GermUniversalStatements

/-!
# The actual germ sheafification universal property

Local original-section representatives determine maps into any actual target
sheaf. This gives direct and lifted uniqueness, the specified natural Hom
equivalences, and the actual direct adjunction.
-/

open CategoryTheory Opposite

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- Target sheaf separation promotes equality on original germ families to equality
of morphisms, without any separation premise on the original presheaf. -/
theorem germSheaf_hom_ext {F : Presheaf.{u,v} B}
    {G : BasisSheaf.{u,max u v} B}
    (χ ξ : (germSheafFunctor.{u,v} B).obj F ⟶ G)
    (h : ∀ (U : BasisOpen B) (t : Sections F.obj U),
      χ.hom.hom.app (op U) (sectionGerms F.obj U t) =
        ξ.hom.hom.app (op U) (sectionGerms F.obj U t)) : χ = ξ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro s
  apply rawSheafGermEquality G.obj.obj G.property U.unop
  intro x hx
  obtain ⟨V, hxV, hVU, t, ht⟩ := s.property ⟨x, hx⟩
  have hs : germRestriction F.obj hVU s = sectionGerms F.obj V t := by
    apply GermSections.ext
    intro y
    exact (ht y.val y.property).symm
  have hχ : restriction G.obj.obj hVU (χ.hom.hom.app U s) =
      χ.hom.hom.app (op V) (germRestriction F.obj hVU s) :=
    (ConcreteCategory.congr_hom (χ.hom.hom.naturality (basisHom hVU).op) s).symm
  have hξ : restriction G.obj.obj hVU (ξ.hom.hom.app U s) =
      ξ.hom.hom.app (op V) (germRestriction F.obj hVU s) :=
    (ConcreteCategory.congr_hom (ξ.hom.hom.naturality (basisHom hVU).op) s).symm
  calc
    rawGerm G.obj.obj U.unop x hx (χ.hom.hom.app U s) =
        rawGerm G.obj.obj V x hxV
          (restriction G.obj.obj hVU (χ.hom.hom.app U s)) :=
      (rawGerm_restriction G.obj.obj hVU x hxV _).symm
    _ = rawGerm G.obj.obj V x hxV
          (restriction G.obj.obj hVU (ξ.hom.hom.app U s)) := by
      rw [hχ, hξ, hs, h V t]
    _ = rawGerm G.obj.obj U.unop x hx (ξ.hom.hom.app U s) :=
      rawGerm_restriction G.obj.obj hVU x hxV _

/-- Direct unit precomposition is injective for the actual germ sheaf. -/
theorem germDesc_unique {F : Presheaf.{u,max u v} B}
    {G : BasisSheaf.{u,max u v} B} (ψ : F ⟶ G.obj)
    (χ : (germSheafFunctor.{u,max u v} B).obj F ⟶ G)
    (hχ : (germSheafUnit.{u,v} B).app F ≫ (sheafForget B).map χ = ψ) :
    χ = germDesc.{u,v} ψ := by
  apply germSheaf_hom_ext
  intro U t
  exact congrArg (fun f => f.hom.app (op U) t)
    (hχ.trans (germDesc_factorization.{u,v} ψ).symm)

/-- Lifted unit precomposition likewise determines every map into the actual lifted target. -/
theorem liftedGermDesc_unique {F : Presheaf.{u,v} B} {G : BasisSheaf.{u,v} B}
    (ψ : F ⟶ G.obj)
    (χ : (germSheafFunctor.{u,v} B).obj F ⟶ (sheafLiftJoint.{u,v} B).obj G)
    (hχ : (germSheafLiftUnit.{u,v} B).app F ≫ (sheafForget B).map χ =
      (presheafLiftJoint.{u,v} B).map ψ) : χ = liftedGermDesc.{u,v} ψ := by
  apply germSheaf_hom_ext
  intro U t
  exact congrArg (fun f => f.hom.app (op U) (ULift.up t))
    (hχ.trans (liftedGermDesc_factorization ψ).symm)

/-- The specified direct Hom equivalence, with both inverse laws proved. -/
noncomputable def germHomEquiv (B : OpenBasis X)
    (F : Presheaf.{u,max u v} B) (G : BasisSheaf.{u,max u v} B) :
    ((germSheafFunctor.{u,max u v} B).obj F ⟶ G) ≃ (F ⟶ G.obj) where
  toFun χ := (germSheafUnit.{u,v} B).app F ≫ (sheafForget B).map χ
  invFun := germDesc.{u,v}
  left_inv χ := (germDesc_unique _ χ rfl).symm
  right_inv ψ := germDesc_factorization ψ

/-- The arbitrary-value Hom equivalence lowers only a map between actual lifts. -/
noncomputable def liftedGermHomEquiv (B : OpenBasis X)
    (F : Presheaf.{u,v} B) (G : BasisSheaf.{u,v} B) :
    ((germSheafFunctor.{u,v} B).obj F ⟶ (sheafLiftJoint.{u,v} B).obj G) ≃
      (F ⟶ G.obj) where
  toFun χ := presheafLower.{u,v,u}
    ((germSheafLiftUnit.{u,v} B).app F ≫ (sheafForget B).map χ)
  invFun := liftedGermDesc
  left_inv χ := (liftedGermDesc_unique _ χ
    (presheafLift_map_presheafLower _).symm).symm
  right_inv ψ := by
    change presheafLower.{u,v,u}
      ((germSheafLiftUnit.{u,v} B).app F ≫ (sheafForget B).map (liftedGermDesc ψ)) = ψ
    exact (congrArg (presheafLower.{u,v,u} (F := F) (G := G.obj))
      (liftedGermDesc_factorization ψ)).trans (presheafLower_presheafLift_map ψ)

/-- Direct forward naturality in the source, obtained from actual inverse naturality. -/
theorem germHomEquiv_precomp {E F : Presheaf.{u,max u v} B}
    {G : BasisSheaf.{u,max u v} B} (φ : E ⟶ F)
    (χ : (germSheafFunctor.{u,max u v} B).obj F ⟶ G) :
    germHomEquiv.{u,v} B E G ((germSheafFunctor B).map φ ≫ χ) =
      φ ≫ germHomEquiv.{u,v} B F G χ := by
  apply (germHomEquiv.{u,v} B E G).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = germDesc.{u,v} (φ ≫ germHomEquiv.{u,v} B F G χ)
  rw [germDesc_precomp]
  exact congrArg (fun f => (germSheafFunctor B).map φ ≫ f)
    ((germHomEquiv.{u,v} B F G).symm_apply_apply χ).symm

/-- Direct forward naturality in the actual target sheaf. -/
theorem germHomEquiv_postcomp {F : Presheaf.{u,max u v} B}
    {G H : BasisSheaf.{u,max u v} B}
    (χ : (germSheafFunctor.{u,max u v} B).obj F ⟶ G) (θ : G ⟶ H) :
    germHomEquiv.{u,v} B F H (χ ≫ θ) =
      germHomEquiv.{u,v} B F G χ ≫ (sheafForget B).map θ := by
  apply (germHomEquiv.{u,v} B F H).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = germDesc.{u,v} (germHomEquiv.{u,v} B F G χ ≫ θ.hom)
  rw [germDesc_postcomp]
  exact congrArg (fun f => f ≫ θ)
    ((germHomEquiv.{u,v} B F G).symm_apply_apply χ).symm

/-- Lifted forward source naturality follows from the published precomposition law. -/
theorem liftedGermHomEquiv_precomp {E F : Presheaf.{u,v} B}
    {G : BasisSheaf.{u,v} B} (φ : E ⟶ F)
    (χ : (germSheafFunctor.{u,v} B).obj F ⟶ (sheafLiftJoint.{u,v} B).obj G) :
    liftedGermHomEquiv B E G ((germSheafFunctor B).map φ ≫ χ) =
      φ ≫ liftedGermHomEquiv B F G χ := by
  apply (liftedGermHomEquiv B E G).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = liftedGermDesc (φ ≫ liftedGermHomEquiv B F G χ)
  rw [liftedGermDesc_precomp]
  exact congrArg (fun f => (germSheafFunctor B).map φ ≫ f)
    ((liftedGermHomEquiv B F G).symm_apply_apply χ).symm

/-- Lifted target naturality uses the actual sheaf lift on the target arrow. -/
theorem liftedGermHomEquiv_postcomp {F : Presheaf.{u,v} B}
    {G H : BasisSheaf.{u,v} B}
    (χ : (germSheafFunctor.{u,v} B).obj F ⟶ (sheafLiftJoint.{u,v} B).obj G)
    (θ : G ⟶ H) :
    liftedGermHomEquiv B F H (χ ≫ (sheafLiftJoint B).map θ) =
      liftedGermHomEquiv B F G χ ≫ (sheafForget B).map θ := by
  apply (liftedGermHomEquiv B F H).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = liftedGermDesc (liftedGermHomEquiv B F G χ ≫ θ.hom)
  rw [liftedGermDesc_postcomp]
  exact congrArg (fun f => f ≫ (sheafLiftJoint B).map θ)
    ((liftedGermHomEquiv B F G).symm_apply_apply χ).symm

/-- The actual direct adjunction, built from the proved natural Hom equivalence.
Mathlib's constructor proves both triangle identities from the two inverse laws. -/
noncomputable def germAdjunction (B : OpenBasis X) :
    germSheafFunctor.{u,max u v} B ⊣ sheafForget.{u,max u v} B :=
  Adjunction.mkOfHomEquiv
    { homEquiv := germHomEquiv.{u,v} B
      homEquiv_naturality_left_symm := fun φ ψ => germDesc_precomp φ ψ
      homEquiv_naturality_right := fun χ θ => germHomEquiv_postcomp χ θ }

/-- The entire unit of the constructed adjunction is the published canonical unit. -/
theorem germAdjunction_unit (B : OpenBasis X) :
    (germAdjunction.{u,v} B).unit = germSheafUnit.{u,v} B := by
  apply NatTrans.ext
  funext F
  change (germSheafUnit.{u,v} B).app F ≫ (sheafForget B).map (𝟙 _) = _
  simp

/-- Its Hom equivalence is precisely the proved literal direct family. -/
theorem germAdjunction_homEquiv (B : OpenBasis X) :
    (germAdjunction.{u,v} B).homEquiv = germHomEquiv.{u,v} B :=
  Adjunction.mkOfHomEquiv_homEquiv _

/-- The counit is literal descent of the identity of the forgotten target. -/
theorem germAdjunction_counit (B : OpenBasis X) (G : BasisSheaf.{u,max u v} B) :
    (germAdjunction.{u,v} B).counit.app G = germDesc.{u,v} (𝟙 G.obj) := rfl

/-- The closed seven-part universal property for arbitrary supplied topology and basis. -/
theorem germUniversal : GermUniversalStatement.{u,v} := by
  intro X _ B
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F G ψ
    refine ⟨germDesc_factorization ψ, fun χ => ⟨fun h => germDesc_unique ψ χ h, ?_⟩⟩
    rintro rfl
    exact germDesc_factorization ψ
  · intro F G ψ
    refine ⟨liftedGermDesc_factorization ψ,
      fun χ => ⟨fun h => liftedGermDesc_unique ψ χ h, ?_⟩⟩
    rintro rfl
    exact liftedGermDesc_factorization ψ
  · exact ⟨fun _ _ _ φ ψ => germDesc_precomp φ ψ,
      fun _ _ _ ψ θ => germDesc_postcomp ψ θ⟩
  · exact ⟨fun _ _ _ φ ψ => liftedGermDesc_precomp φ ψ,
      fun _ _ _ ψ θ => liftedGermDesc_postcomp ψ θ⟩
  · exact ⟨germHomEquiv B, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ φ χ => germHomEquiv_precomp φ χ,
      fun _ _ _ χ θ => germHomEquiv_postcomp χ θ⟩
  · exact ⟨liftedGermHomEquiv B, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ φ χ => liftedGermHomEquiv_precomp φ χ,
      fun _ _ _ χ θ => liftedGermHomEquiv_postcomp χ θ⟩
  · refine ⟨germAdjunction B, germAdjunction_unit B, ?_, ?_, germAdjunction_counit B⟩
    · intro F G χ
      rw [germAdjunction_homEquiv]
      rfl
    · intro F G ψ
      rw [germAdjunction_homEquiv]
      rfl

end Langlands.Sheaf.Renard

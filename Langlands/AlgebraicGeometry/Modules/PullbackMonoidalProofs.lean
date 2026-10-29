import Langlands.AlgebraicGeometry.Modules.PullbackMonoidalStatements
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace Langlands.Scheme.Modules

private lemma isMonoidal_of_oplax
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (τ : F ⟶ G)
    (hunit : τ.app (𝟙_ C) ≫ CategoryTheory.Functor.OplaxMonoidal.η G =
      CategoryTheory.Functor.OplaxMonoidal.η F)
    (htensor : ∀ M N : C,
      τ.app (M ⊗ N) ≫ CategoryTheory.Functor.OplaxMonoidal.δ G M N =
        CategoryTheory.Functor.OplaxMonoidal.δ F M N ≫ (τ.app M ⊗ₘ τ.app N)) :
    NatTrans.IsMonoidal τ where
  unit := by
    apply (cancel_mono (CategoryTheory.Functor.OplaxMonoidal.η G)).1
    rw [Category.assoc, hunit, CategoryTheory.Functor.Monoidal.ε_η,
      CategoryTheory.Functor.Monoidal.ε_η]
  tensor M N := by
    apply (cancel_mono (CategoryTheory.Functor.OplaxMonoidal.δ G M N)).1
    simp only [Category.assoc, CategoryTheory.Functor.Monoidal.μ_δ, Category.comp_id]
    rw [htensor, ← Category.assoc, CategoryTheory.Functor.Monoidal.μ_δ, Category.id_comp]

/-- The fixed identity pullback comparison respects the localized oplax tensor map. -/
lemma localizedPullbackTensorIdentity (X : Scheme.{u}) (M N : X.Modules) :
    localizedPullbackTensorComparisonApp (𝟙 X) M N ≫
      ((Scheme.Modules.pullbackId X).hom.app M ⊗ₘ (Scheme.Modules.pullbackId X).hom.app N) =
        (Scheme.Modules.pullbackId X).hom.app (M ⊗ N) := by
  apply (cancel_mono (localizedTensorIso X M N).hom).1
  have hn := localizedTensorIso_hom_naturality (X := X)
    (M := (Scheme.Modules.pullback (𝟙 X)).obj M) (M' := M)
    (N := (Scheme.Modules.pullback (𝟙 X)).obj N) (N' := N)
    ((Scheme.Modules.pullbackId X).hom.app M) ((Scheme.Modules.pullbackId X).hom.app N)
  simp only [localizedPullbackTensorComparisonApp_eq, Category.assoc]
  rw [hn, Iso.inv_hom_id_assoc, pullbackTensorIdentity]
  exact (Scheme.Modules.pullbackId X).hom.naturality (localizedTensorIso X M N).hom

/-- The fixed composite pullback comparison respects the localized oplax tensor maps. -/
lemma localizedPullbackTensorComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : Z.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app (M ⊗ N) ≫
      localizedPullbackTensorComparisonApp (f ≫ g) M N =
        (Scheme.Modules.pullback f).map (localizedPullbackTensorComparisonApp g M N) ≫
          localizedPullbackTensorComparisonApp f ((Scheme.Modules.pullback g).obj M)
            ((Scheme.Modules.pullback g).obj N) ≫
              ((Scheme.Modules.pullbackComp f g).hom.app M ⊗ₘ
                (Scheme.Modules.pullbackComp f g).hom.app N) := by
  apply (cancel_mono (localizedTensorIso X ((Scheme.Modules.pullback (f ≫ g)).obj M)
    ((Scheme.Modules.pullback (f ≫ g)).obj N)).hom).1
  have hn := localizedTensorIso_hom_naturality (X := X)
    (M := (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))
    (M' := (Scheme.Modules.pullback (f ≫ g)).obj M)
    (N := (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N))
    (N' := (Scheme.Modules.pullback (f ≫ g)).obj N)
    ((Scheme.Modules.pullbackComp f g).hom.app M) ((Scheme.Modules.pullbackComp f g).hom.app N)
  simp only [localizedPullbackTensorComparisonApp_eq, CategoryTheory.Functor.map_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hn]
  simp only [Iso.inv_hom_id_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc (Scheme.Modules.pullback f)
      (localizedTensorIso Y ((Scheme.Modules.pullback g).obj M)
        ((Scheme.Modules.pullback g).obj N)).inv
      (localizedTensorIso Y ((Scheme.Modules.pullback g).obj M)
        ((Scheme.Modules.pullback g).obj N)).hom, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← (Scheme.Modules.pullbackComp f g).hom.naturality_assoc
    (localizedTensorIso Z M N).hom]
  change (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map
    (localizedTensorIso Z M N).hom) ≫ _ = _
  rw [pullbackTensorComposition X Y Z f g M N]

/-- The existing identity comparison is monoidal for canonical scheme-module pullback. -/
lemma pullbackIdentityMonoidal : PullbackIdentityMonoidalStatement.{u} := by
  intro X
  apply isMonoidal_of_oplax
  · change (Scheme.Modules.pullbackId X).hom.app (structureSheaf X) ≫ 𝟙 _ =
      (pullbackUnitIso (𝟙 X)).hom
    simpa only [Category.comp_id, structureSheaf] using (pullbackUnitIdentity X).symm
  · intro M N
    change (Scheme.Modules.pullbackId X).hom.app (M ⊗ N) ≫ 𝟙 _ =
      localizedPullbackTensorComparisonApp (𝟙 X) M N ≫
        ((Scheme.Modules.pullbackId X).hom.app M ⊗ₘ (Scheme.Modules.pullbackId X).hom.app N)
    simpa only [Category.comp_id] using (localizedPullbackTensorIdentity X M N).symm

/-- The existing composition comparison is monoidal for canonical scheme-module pullback. -/
lemma pullbackCompositionMonoidal : PullbackCompositionMonoidalStatement.{u} := by
  intro X Y Z f g
  apply isMonoidal_of_oplax
  · change (Scheme.Modules.pullbackComp f g).hom.app (structureSheaf Z) ≫
      (pullbackUnitIso (f ≫ g)).hom =
        (Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom
    exact pullbackUnitComposition X Y Z f g
  · intro M N
    exact localizedPullbackTensorComposition f g M N

/-- Monoidality of the two existing pullback comparison natural isomorphisms. -/
theorem pullbackComparisonsMonoidal : PullbackComparisonsMonoidalStatement.{u} :=
  ⟨pullbackIdentityMonoidal, pullbackCompositionMonoidal⟩

instance pullbackId_isMonoidal (X : Scheme.{u}) :
    NatTrans.IsMonoidal (Scheme.Modules.pullbackId X).hom :=
  pullbackIdentityMonoidal X

instance pullbackComp_isMonoidal {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (Scheme.Modules.pullbackComp f g).hom :=
  pullbackCompositionMonoidal X Y Z f g

end Langlands.Scheme.Modules

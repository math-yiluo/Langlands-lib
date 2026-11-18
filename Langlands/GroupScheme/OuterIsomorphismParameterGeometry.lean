import Langlands.GroupScheme.OuterIsomorphismLocalGeometry
import Langlands.GroupScheme.OuterIsomorphismConstantSection
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget

/-! # Outer parameter geometry from local normalized families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OuterIsomorphismScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
  (O : OuterIsomorphismScheme I a)
  [Flat A.X.hom] [LocallyOfFinitePresentation A.X.hom]

/-- A target-local property of the outer parameter is detected on local
normalized families over an étale cover of the base. -/
theorem parameter_property_of_etaleCover
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u})]
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hlocal : ∀ i, ∃ (M : Over S) (π : M ⟶ Over.mk (𝒰.f i))
      (s : M ⟶ I.parameter), P π.left ∧
        ∀ (T : Over S), Function.Bijective
          (fun z : (T ⟶ A.X) × (T ⟶ M) =>
            prod.lift (lift z.1 (z.2 ≫ s) ≫ I.actionHom a) (z.2 ≫ π))) :
    P O.parameter.hom := by
  let 𝒱 := Scheme.Cover.changeProp 𝒰
    (Q := @Flat ⊓ @LocallyOfFinitePresentation)
    (fun i => by
      have := 𝒰.map_prop i
      exact ⟨inferInstance, inferInstance⟩)
  let : P.IsLocalAtTarget (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage P
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd 𝒱.mem₀
  intro U b _ hb
  obtain ⟨i⟩ := hb
  obtain ⟨M, π, s, hP, h⟩ := hlocal i
  obtain ⟨e⟩ := O.exists_localParameterIso π s h
  change (Over.pullback (𝒰.f i)).obj O.parameter ≅ Over.mk π.left at e
  change P ((Over.pullback (𝒰.f i)).obj O.parameter).hom
  rw [← Over.w e.hom, P.cancel_left_of_respectsIso]
  exact hP

/-- Local constant normalized families make the actual outer parameter
separated and étale, with the specified scheme-level local constancy. -/
theorem geometry_of_localConstants
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hlocal : ∀ i, ∃ (D : Type u)
      (s : (Over.map (𝒰.f i)).obj
        (GroupIsomorphismScheme.constantParameter (𝒰.X i) D) ⟶ I.parameter),
      ∀ (T : Over S), Function.Bijective
        (fun z : (T ⟶ A.X) ×
            (T ⟶ (Over.map (𝒰.f i)).obj
              (GroupIsomorphismScheme.constantParameter (𝒰.X i) D)) =>
          prod.lift (lift z.1 (z.2 ≫ s) ≫ I.actionHom a)
            (z.2 ≫ (Over.homMk
              (GroupIsomorphismScheme.constantParameter (𝒰.X i) D).hom rfl :
                (Over.map (𝒰.f i)).obj
                  (GroupIsomorphismScheme.constantParameter (𝒰.X i) D) ⟶
                    Over.mk (𝒰.f i))))) :
    Etale O.parameter.hom ∧ IsSeparated O.parameter.hom ∧
      ∀ i, ∃ D : Type u, Nonempty ((Over.pullback (𝒰.f i)).obj O.parameter ≅
        GroupIsomorphismScheme.constantParameter (𝒰.X i) D) := by
  have hP (P : MorphismProperty Scheme.{u})
      (hconstant : ∀ (U : Scheme.{u}) (D : Type u),
        P (GroupIsomorphismScheme.constantParameter U D).hom) :
      ∀ i, ∃ (M : Over S) (π : M ⟶ Over.mk (𝒰.f i)) (s : M ⟶ I.parameter),
        P π.left ∧ ∀ (T : Over S), Function.Bijective
          (fun z : (T ⟶ A.X) × (T ⟶ M) =>
            prod.lift (lift z.1 (z.2 ≫ s) ≫ I.actionHom a) (z.2 ≫ π)) := by
    intro i
    obtain ⟨D, s, h⟩ := hlocal i
    exact ⟨_, Over.homMk _ rfl, s, hconstant _ D, h⟩
  refine ⟨O.parameter_property_of_etaleCover (@Etale.{u}) 𝒰
    (hP _ (fun _ _ => inferInstance)),
    O.parameter_property_of_etaleCover (@IsSeparated.{u}) 𝒰
      (hP _ (fun _ _ => inferInstance)), ?_⟩
  intro i
  obtain ⟨D, s, h⟩ := hlocal i
  exact ⟨D, O.exists_localParameterIso (Over.homMk _ rfl) s h⟩

/-- Choose the constant label type and actual local comparison isomorphism
on every member of the supplied normalized-chart cover. -/
def constantLocalParameterIso
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hlocal : ∀ i, ∃ (D : Type u)
      (s : (Over.map (𝒰.f i)).obj
        (GroupIsomorphismScheme.constantParameter (𝒰.X i) D) ⟶ I.parameter),
      ∀ (T : Over S), Function.Bijective
        (fun z : (T ⟶ A.X) ×
            (T ⟶ (Over.map (𝒰.f i)).obj
              (GroupIsomorphismScheme.constantParameter (𝒰.X i) D)) =>
          prod.lift (lift z.1 (z.2 ≫ s) ≫ I.actionHom a)
            (z.2 ≫ (Over.homMk
              (GroupIsomorphismScheme.constantParameter (𝒰.X i) D).hom rfl :
                (Over.map (𝒰.f i)).obj
                  (GroupIsomorphismScheme.constantParameter (𝒰.X i) D) ⟶
                    Over.mk (𝒰.f i))))) :
    (i : 𝒰.I₀) → Σ D : Type u,
      (Over.pullback (𝒰.f i)).obj O.parameter ≅
        GroupIsomorphismScheme.constantParameter (𝒰.X i) D := by
  intro i
  let h := (O.geometry_of_localConstants 𝒰 hlocal).2.2 i
  exact ⟨h.choose, Classical.choice h.choose_spec⟩

end Langlands.GroupScheme.OuterIsomorphismScheme

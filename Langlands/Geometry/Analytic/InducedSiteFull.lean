import Langlands.Geometry.Analytic.InducedSiteFold

/-! # Induction on equivariant quasi-étale sites is full -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Action

variable {G : Type z} [Group G] (H : Subgroup G) (hP : OpenPartitionCoproductStatement.{u, v, z})

/-- A `G`-morphism `A_{G/H} → B_{G/H}` over the induction of a base `Y` preserves the coset of
every point. -/
theorem pointCoset_space_apply_of_comp_eq
    {A B Y : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H}
    (pA : A ⟶ Y) (pB : B ⟶ Y) (ψ : (inductionFunctor H).obj A ⟶ (inductionFunctor H).obj B)
    (hψ : ψ ≫ (inductionFunctor H).map pB = (inductionFunctor H).map pA)
    (p : localizedSpaceFunctor.obj (copies H A).pt) :
    pointCoset H B (localizedSpaceFunctor.map ψ.hom p) = pointCoset H A p := by
  rw [← pointCoset_inductionFunctor_map H pB, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Action.comp_hom, hψ, pointCoset_inductionFunctor_map]

include hP in
/-- **Fullness of induction over a base.** Every `G`-morphism `ψ : A_{G/H} → B_{G/H}` over the
induction of a base `Y` of `H`-objects is the induction of a morphism `A → B` over `Y`. -/
theorem exists_inductionFunctor_map_eq
    {A B Y : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H}
    (pA : A ⟶ Y) (pB : B ⟶ Y) (ψ : (inductionFunctor H).obj A ⟶ (inductionFunctor H).obj B)
    (hψ : ψ ≫ (inductionFunctor H).map pB = (inductionFunctor H).map pA) :
    ∃ f : A ⟶ B, f ≫ pB = pA ∧ (inductionFunctor H).map f = ψ := by
  obtain ⟨t, ht⟩ : ∃ t, t = unitHom H A ≫ ψ.hom := ⟨_, rfl⟩
  -- The composite `t` lands in the copy of `B` indexed by the coset `H`.
  have htc : t ≫ foldHom H B ≫ copy H B (baseCoset H) = t :=
    foldHom_copy_of_pointCoset H B hP t (baseCoset H) fun x => by
      rw [ht, Functor.map_comp, ConcreteCategory.comp_apply,
        pointCoset_space_apply_of_comp_eq H pA pB ψ hψ, pointCoset_unitHom]
  obtain ⟨fh, hfh⟩ : ∃ fh, fh = t ≫ foldHom H B ≫ B.ρ (baseRep H) := ⟨_, rfl⟩
  have hfu : fh ≫ unitHom H B = t := by
    rw [hfh, unitHom, Category.assoc, Category.assoc, ρ_comp_assoc, inv_mul_cancel, Action.ρ_one,
      Category.id_comp, htc]
  have hcomm : ∀ h : H, A.ρ h ≫ fh = fh ≫ B.ρ h := fun h => by
    rw [← cancel_mono (unitHom H B), Category.assoc, Category.assoc, hfu, unitHom_comm,
      ← Category.assoc fh, hfu, ht, ← Category.assoc (A.ρ h), unitHom_comm, Category.assoc,
      Category.assoc]
    exact congrArg (unitHom H A ≫ ·) (ψ.comm (h : G))
  let f : A ⟶ B := ⟨fh, hcomm⟩
  have hind : (inductionFunctor H).map f = ψ := by
    apply (homEquiv H).injective
    rw [inductionFunctor_map, homEquiv_apply, unit_comp_lift, homEquiv_apply]
    exact Action.Hom.ext (hfu.trans ht)
  refine ⟨f, inductionFunctor_map_injective H ?_, hind⟩
  rw [Functor.map_comp, hind, hψ]

end Action

variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  (hP : OpenPartitionCoproductStatement.{u, v, z})
  (hH : IsOpen (H : Set G)) (hC : ContinuityStatement.{u, v, z})
  (hQ : MorphismPropertyStatement.{u, v, z}) (X : GSpace.{u, max z v, max z v} K H)

include hP in
/-- Induction `Qét(X(H)) ⥤ Qét(X_{G/H}(G))` is full, given the statement that an analytic space
partitioned into open subsets is the disjoint union of the corresponding open domains. -/
theorem full_quasiEtaleSiteInduction : (quasiEtaleSiteInduction hH hC hQ X).Full where
  map_surjective {U V} φ := by
    obtain ⟨f, hf, hind⟩ := exists_inductionFunctor_map_eq H hP U.hom.hom V.hom.hom φ.left.hom
      (congrArg (fun k => k.hom) (MorphismProperty.Over.w φ))
    exact ⟨MorphismProperty.Over.homMk (ObjectProperty.homMk f) (ObjectProperty.hom_ext _ hf)
      trivial, MorphismProperty.Over.Hom.ext (ObjectProperty.hom_ext _ hind)⟩

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

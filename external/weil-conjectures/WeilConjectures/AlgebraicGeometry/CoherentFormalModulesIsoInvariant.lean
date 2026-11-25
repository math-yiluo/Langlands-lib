/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem finiteType_of_iso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ U, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F G : SheafOfModules.{u} R} (e : F ≅ G) (hF : F.IsFiniteType) :
    G.IsFiniteType := by
  obtain ⟨q, hq⟩ := hF.exists_localGeneratorsData
  have : q.IsFiniteType := hq
  let q' : G.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (e.hom.over (q.X i)) }
  refine ⟨⟨q', ?_⟩⟩
  constructor
  intro i
  have := hq.isFiniteType i
  dsimp [q']
  infer_instance

/-- Coherence of a formal module is invariant under isomorphism of inverse systems.
Source: Stacks Project, Lemma 087X, transport of the three defining conditions
(blueprint: lem-weil-pbc-coherent-formal-iso-invariant).

Proof: transport coherence and zero-product conditions along each component isomorphism;
transport the quotient-transition isomorphisms by the naturality squares of the given
natural isomorphism. -/
theorem coherentFormalModules_of_iso
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    {F G : ℕᵒᵖ ⥤ X.Modules} (e : F ≅ G)
    (hF : IsCoherentFormalModule I F) :
    IsCoherentFormalModule I G := by
  set_option backward.isDefEq.respectTransparency false in
    refine ⟨?_, ?_, ?_⟩
    · intro n
      let d := e.app (op n)
      refine ⟨finiteType_of_iso.{u} d (hF.1 n).1, ?_⟩
      intro U r f
      exact finiteType_of_iso.{u} (kernelCompMono f (d.inv.over U)) ((hF.1 n).2 U r _)
    · intro n
      let d := e.app (op n)
      obtain ⟨k, hk⟩ := formalModuleQuotient_factor I d.inv (Nat.le_refl (n + 1))
      have hi : Scheme.idealModuleProductι
          (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (G.obj (op n)) = 0 := by
        apply (cancel_mono d.inv).1
        have hz : Scheme.idealModuleProductι
            (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (F.obj (op n)) = 0 :=
          (hF.2.1 n).eq_zero_of_src _
        rw [hk, hz, comp_zero, zero_comp]
      let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
      have : Mono (Scheme.idealModuleProductι
          (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (G.obj (op n))) := by
        dsimp [Scheme.idealModuleProductι]
        infer_instance
      exact IsZero.of_mono_eq_zero _ hi
    · intro n
      obtain ⟨a, ha⟩ := hF.2.2 n
      let d := e.app (op (n + 1))
      let q : formalModuleQuotient I (n + 1) (G.obj (op (n + 1))) ≅
          formalModuleQuotient I (n + 1) (F.obj (op (n + 1))) :=
        { hom := formalModuleQuotientMap I d.inv (Nat.le_refl (n + 1))
          inv := formalModuleQuotientMap I d.hom (Nat.le_refl (n + 1))
          hom_inv_id := by
            rw [← formalModuleQuotientMap_comp, d.inv_hom_id]
            exact formalModuleQuotientMap_id I _ _
          inv_hom_id := by
            rw [← formalModuleQuotientMap_comp, d.hom_inv_id]
            exact formalModuleQuotientMap_id I _ _ }
      refine ⟨q ≪≫ a ≪≫ e.app (op n), ?_⟩
      change formalModuleQuotientπ I (n + 1) (G.obj (op (n + 1))) ≫
        formalModuleQuotientMap I d.inv (Nat.le_refl (n + 1)) ≫
        a.hom ≫ e.hom.app (op n) = _
      have hq : formalModuleQuotientπ I (n + 1) (G.obj (op (n + 1))) ≫
          formalModuleQuotientMap I d.inv (Nat.le_refl (n + 1)) =
          d.inv ≫ formalModuleQuotientπ I (n + 1) (F.obj (op (n + 1))) := by
        exact cokernel.π_desc _ _ _
      rw [← Category.assoc, ← Category.assoc, hq]
      simp only [Category.assoc]
      rw [← Category.assoc _ a.hom, ha, e.hom.naturality]
      simp [d]

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-!
# The `𝔾ₘ`-torsor of trivialisations of a module

For a quasi-coherent `𝒪_X`-module `L`, the étale sheaf `V ↦ Iso(V^* 𝒪_X, V^* L)`
(`AlgebraicGeometry.Scheme.Modules.etaleIso`) carries an action of `𝔾ₘ` by multiplication.
For `L` invertible it is a `𝔾ₘ`-torsor `Isom(𝒪, L)` on the small étale site.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.etaleIsoTorsor`: the `𝔾ₘ`-torsor `Isom(𝒪, L)`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (L : modulesPseudofunctor.obj (.mk (op X)))

/-- A free generator of `L` over `U` trivialises the pullback of `L` along a morphism landing
in `U`. -/
lemma nonempty_pullback_unit_iso_of_isFreeGenerator {Y : Scheme.{u}} (h : Y ⟶ X)
    {M : X.Modules} {U : X.Opens} {s : Γ(M, U)} (hs : IsFreeGenerator s) (hU : h ⁻¹ᵁ U = ⊤) :
    Nonempty ((pullback h).obj (Modules.unit X) ≅ (pullback h).obj M) := by
  let e := ((pullback h).obj M).presheaf.map (homOfLE hU.ge).op
    (((pullbackPushforwardAdjunction h).unit.app M).app U s)
  have he : IsFreeGenerator e := (hs.pullback_unit_app h).map hU.ge
  have := isIso_homOfGlobalSection he
  exact ⟨pullbackObjUnitIso h ≪≫ asIso (homOfGlobalSection _ e)⟩

set_option maxHeartbeats 1000000 in
-- the defeq checks through the small étale and pro-étale sites are slow
/-- The `𝔾ₘ`-torsor `Isom(𝒪, L)` on the small étale site. -/
noncomputable def etaleIsoTorsor [SheafOfModules.IsInvertible.{u, u, u} (L : X.Modules)] :
    Sheaf.Torsor X.gmSheaf where
  sheaf :=
    haveI := Modules.IsInvertible.of_sheafOfModules (L : X.Modules)
    haveI : (L : X.Modules).IsQuasicoherent := IsInvertible.isQuasicoherent (L : X.Modules)
    ⟨(etaleIso (unitObj X) L).toFunctor ⋙ uliftFunctor.{u + 1},
    (isSheaf_iff_isSheaf_of_type _ _).2 ((Presieve.isSheaf_comp_uliftFunctor_iff _).2
      ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_etaleIso _ _)))⟩
  vadd V a t := ⟨⟨smulMor _ ((Additive.toMul a.down : Γ(V.unop.left, ⊤)ˣ) : Γ(V.unop.left, ⊤))
      ≫ t.down.1, by
    have : IsIso t.down.1 := t.down.2
    exact IsIso.comp_isIso' (isIso_smulHom_units (_ : Scheme.Modules _) (Additive.toMul a.down))
      this⟩⟩
  zero_vadd V t := by
    apply ULift.ext
    apply Subtype.ext
    change smulMor _ (((1 : Γ(V.unop.left, ⊤)ˣ)) : Γ(V.unop.left, ⊤)) ≫ t.down.1 = t.down.1
    erw [Units.val_one, smulMor_one]
    exact Category.id_comp _
  add_vadd V a b t := by
    apply ULift.ext
    apply Subtype.ext
    change smulMor _ ((Additive.toMul (a + b).down : Γ(V.unop.left, ⊤)ˣ) : Γ(V.unop.left, ⊤))
      ≫ t.down.1 = smulMor _ ((Additive.toMul a.down : Γ(V.unop.left, ⊤)ˣ) : Γ(V.unop.left, ⊤))
      ≫ smulMor _ ((Additive.toMul b.down : Γ(V.unop.left, ⊤)ˣ) : Γ(V.unop.left, ⊤)) ≫ t.down.1
    erw [toMul_add, Units.val_mul, mul_comm, smulMor_mul]
    exact Category.assoc _ _ _
  map_vadd f a t := by
    apply ULift.ext
    apply Subtype.ext
    exact presheafHom_map_smulMor_comp (unitObj X) L ((toProEt X ⋙ ProEt.forget X).map f.unop) _
      t.down.1
  bijective_vadd V t := by
    have : (Modules.unit X).IsInvertible := isInvertible_tensorUnit
    have hA : ((pullback ((toProEt X ⋙ ProEt.forget X).obj V.unop).hom).obj
        (Modules.unit X)).IsInvertible := inferInstance
    refine ⟨fun a b h ↦ ?_, fun s ↦ ?_⟩
    · have h' := congrArg (fun x ↦ x.down.1) h
      have := @smulMor_comp_injective _ _ _ hA t.down.1 t.down.2 _ _ h'
      exact ULift.ext (Additive.toMul.injective (Units.ext this))
    · obtain ⟨a, ha⟩ := @exists_smulMor_comp_eq _ _ _ hA t.down.1 s.down.1 t.down.2 s.down.2
      exact ⟨ULift.up (Additive.ofMul a), ULift.ext (Subtype.ext ha)⟩
  nonemptySieve_mem V := by
    have (w : V.left) := exists_isFreeGenerator (L : X.Modules) (W := ⊤) (x := V.hom w) trivial
    choose U hwU hUle s hs using this
    let W (w : V.left) : V.left.Opens := V.hom ⁻¹ᵁ (U w).1
    let Z (w : V.left) : X.Etale := Etale.mk ((W w).ι ≫ V.hom)
    let ι (w : V.left) : Z w ⟶ V := MorphismProperty.Over.homMk (W w).ι rfl
    refine X.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff ι).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨w⟩
      have hU : ((W w).ι ≫ V.hom) ⁻¹ᵁ (U w).1 = ⊤ := by
        ext y
        simp [W]
      obtain ⟨e⟩ := nonempty_pullback_unit_iso_of_isFreeGenerator _ (hs w) hU
      exact ⟨⟨⟨e.hom, ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩⟩⟩
    · refine Set.eq_univ_of_forall fun w ↦ Set.mem_iUnion.2 ⟨w, ⟨⟨w, hwU w⟩, ?_⟩⟩
      exact Scheme.Opens.ι_apply _ _

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction

/-! # Singleton projection retracts the local alternating augmentation

Source: Stacks Project, Tag 02FU, the degree-zero insertion operator.
(blueprint: lem-pc-s3-alternating-cech-sheaf-singleton-retraction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry

open TopologicalSpace in
private theorem cechCapFunctor_isContinuous {X : Scheme.{u}} (W : X.Opens) :
    (cechCapFunctor W).IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology X) := by
  let j : TopCat.of W ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hj : Topology.IsOpenEmbedding j := W.isOpenEmbedding
  let K : X.Opens ⥤ X.Opens := Opens.map j ⋙ hj.isOpenMap.functor
  have : hj.isOpenMap.functor.IsContinuous (Opens.grothendieckTopology W)
      (Opens.grothendieckTopology X) := hj.functor_isContinuous
  have : K.IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology X) := inferInstance
  have he (V : X.Opens) : (cechCapFunctor W).obj V = K.obj V := by
    ext x
    change (x ∈ V ∧ x ∈ W) ↔ x ∈ Subtype.val '' {y : W | y.val ∈ V}
    aesop
  let e : cechCapFunctor W ≅ K :=
    NatIso.ofComponents (fun V ↦ eqToIso (he V)) (by intros; apply Subsingleton.elim)
  exact Functor.isContinuous_of_iso e.symm (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology X)

/-- The local augmentation has a left inverse in degree zero.
Source: Stacks Project, Tag 02FU, degree-zero insertion; Tag 01FM for increasing tuples.
(blueprint: lem-pc-s3-alternating-cech-sheaf-singleton-retraction).

Proof: Project the degree-zero product of intersection presheaves to the singleton
whose unique index is i. On a test open V contained in U i, its intersection with
U i is V, so the singleton restriction is identified with the identity of G(V).
These identifications are linear and natural under restrictions. Sheafify the
projection and restrict it to U i. Sheafification of G.val is identified with G
by the sheafification counit, inverse to its unit on sheaves. Thus projection
following augmentation is the identity. Extend to integer degrees: degree zero
is unchanged, up to the canonical extendXIso and its functorial image. Transport
the preceding retraction across these isomorphisms. For r=0 there is no i; for an
empty U i all the modules in question are zero and the assertion still holds. -/
theorem alternatingCechSheafAugmentation_restrict_degreeZero_retraction
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let A := ((CochainComplex.single₀ X.Modules).obj G).extend
      ComplexShape.embeddingUpNat
    let C := (alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat
    let a := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
        ComplexShape.embeddingUpNat)
    ∃ π : F.obj (C.X 0) ⟶ F.obj (A.X 0), a.f 0 ≫ π = 𝟙 _ := by
  classical
  let W := U i
  let F := Scheme.Modules.restrictFunctor W.ι
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have : (cechCapFunctor W).IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology X) := cechCapFunctor_isContinuous W
  let H : X.Modules := ⟨cechCapModule G W,
    Functor.op_comp_isSheaf (cechCapFunctor W) _ _ ⟨G.val.presheaf, G.isSheaf⟩⟩
  let b : G ⟶ H := (SheafOfModules.fullyFaithfulForget _).preimage
    (cechCapModuleUnit G W)
  have hb : IsIso (F.map b) := by
    apply (isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)).mp
    apply (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)).mp
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    change IsIso (G.val.presheaf.map
      (homOfLE (inf_le_left : (W.ι ''ᵁ V.unop) ⊓ W ≤ W.ι ''ᵁ V.unop)).op)
    have h : (W.ι ''ᵁ V.unop) ⊓ W = W.ι ''ᵁ V.unop :=
      inf_eq_left.mpr (W.ι_image_le V.unop)
    have he : homOfLE (inf_le_left : (W.ι ''ᵁ V.unop) ⊓ W ≤ W.ι ''ᵁ V.unop) =
        (eqToIso h).hom := Subsingleton.elim _ _
    rw [he]
    infer_instance
  let η : G ⟶ L.obj G.val := (SheafOfModules.fullyFaithfulForget _).preimage
    (adj.unit.app G.val)
  have hη : η ≫ adj.counit.app G = 𝟙 G := by
    apply (SheafOfModules.forget _).map_injective
    change adj.unit.app G.val ≫ (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map (adj.counit.app G) = 𝟙 _
    exact adj.right_triangle_components G
  let t : Fin 1 ↪o Fin r :=
    { toFun := fun _ ↦ i
      inj' := fun a b _ ↦ Subsingleton.elim a b
      map_rel_iff' := by intro a b; simp [Subsingleton.elim a b] }
  have ht : alternatingCechIntersection U t = W := by
    simp [alternatingCechIntersection, t, W]
  let p : alternatingCechSheafPresheafTerms U G 0 ⟶ H.val :=
    Pi.π _ t ≫ eqToHom (congrArg (cechCapModule G) ht)
  have hp : alternatingCechSheafPresheafZero U G ≫ p = b.val := by
    dsimp [p, alternatingCechSheafPresheafZero]
    rw [Pi.lift_comp_π_assoc]
    change cechCapModuleUnit G (alternatingCechIntersection U t) ≫
      eqToHom (congrArg (cechCapModule G) ht) = cechCapModuleUnit G W
    clear p
    generalize alternatingCechIntersection U t = Z at ht ⊢
    subst Z
    simp
  have hfactor : (alternatingCechSheafAugmentation U G).f 0 ≫
      L.map p ≫ adj.counit.app H = b := by
    change (η ≫ L.map (alternatingCechSheafPresheafZero U G)) ≫
      L.map p ≫ adj.counit.app H = b
    rw [Category.assoc, ← L.map_comp_assoc, hp]
    have hn := adj.counit.naturality b
    change L.map b.val ≫ adj.counit.app H = adj.counit.app G ≫ b at hn
    rw [hn, ← Category.assoc, hη, Category.id_comp]
  let ρ : F.obj ((alternatingCechSheafComplex U G).X 0) ⟶ F.obj G :=
    F.map (L.map p ≫ adj.counit.app H) ≫ inv (F.map b)
  have hρ : F.map ((alternatingCechSheafAugmentation U G).f 0) ≫ ρ = 𝟙 _ := by
    dsimp only [ρ]
    rw [← F.map_comp_assoc, hfactor, IsIso.hom_inv_id]
  let eS := ((CochainComplex.single₀ X.Modules).obj G).extendXIso
    ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl
  let eC := (alternatingCechSheafComplex U G).extendXIso
    ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl
  refine ⟨F.map eC.hom ≫ ρ ≫ F.map eS.inv, ?_⟩
  change F.map ((HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
    ComplexShape.embeddingUpNat).f 0) ≫ _ = _
  rw [HomologicalComplex.extendMap_f (alternatingCechSheafAugmentation U G)
    ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) rfl]
  change F.map (eS.hom ≫ (alternatingCechSheafAugmentation U G).f 0 ≫ eC.inv) ≫
    (F.map eC.hom ≫ ρ ≫ F.map eS.inv) = 𝟙 _
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc eC.inv, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [← Category.assoc (F.map ((alternatingCechSheafAugmentation U G).f 0)), hρ]
  simp [← F.map_comp]

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleIsoTorsor

/-!
# Invertible modules and étale `𝔾ₘ`-torsors

The torsor `Isom(𝒪, L)` determines the invertible module `L`: an isomorphism of torsors
`Isom(𝒪, L) ≅ Isom(𝒪, L')` comes from an isomorphism `L ≅ L'`, obtained by gluing the local
isomorphisms `t⁻¹ ≫ e(t)` along the étale sheaf of homomorphisms.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_of_etaleIsoTorsor_iso`.
-/

@[expose] public section

universe u w

open CategoryTheory Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

section

variable {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat} {S : C}

lemma CategoryTheory.Pseudofunctor.presheafHom_map_inv {M N : F.obj (.mk (op S))}
    {T T' : Over S} (g : T' ⟶ T) (φ : (F.presheafHom M N).obj (op T)) [IsIso φ] :
    (F.presheafHom N M).map g.op (inv φ) = inv ((F.presheafHom M N).map g.op φ) := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← Pseudofunctor.presheafHom_map_comp, IsIso.hom_inv_id, Pseudofunctor.presheafHom_map_id]

variable {D : Type*} [Category D] (G : D ⥤ Over S)
  {O M N : F.obj (.mk (op S))}

/-- Compare a local trivialisation with its image under a morphism of isomorphism presheaves. -/
private noncomputable def presheafIsoDifference
    (e : (F.presheafIso G O M).toFunctor ⋙ uliftFunctor.{w} ⟶
      (F.presheafIso G O N).toFunctor ⋙ uliftFunctor.{w})
    (U : Dᵒᵖ) (x : ((F.presheafIso G O M).toFunctor ⋙ uliftFunctor.{w}).obj U) :
    ((G.op ⋙ F.presheafHom M N) ⋙ uliftFunctor.{w}).obj U :=
  haveI : IsIso x.down.1 := x.down.2
  ULift.up (inv x.down.1 ≫ (e.app U x).down.1)

private lemma presheafIsoDifference_naturality
    (e : (F.presheafIso G O M).toFunctor ⋙ uliftFunctor.{w} ⟶
      (F.presheafIso G O N).toFunctor ⋙ uliftFunctor.{w})
    {U V : Dᵒᵖ} (f : U ⟶ V)
    (x : ((F.presheafIso G O M).toFunctor ⋙ uliftFunctor.{w}).obj U) :
    ((G.op ⋙ F.presheafHom M N) ⋙ uliftFunctor.{w}).map f
        (presheafIsoDifference G e U x) =
      presheafIsoDifference G e V
        (((F.presheafIso G O M).toFunctor ⋙ uliftFunctor.{w}).map f x) := by
  apply ULift.ext
  have : IsIso x.down.1 := x.down.2
  have hn := NatTrans.naturality_apply e f x
  change (F.presheafHom M N).map (G.map f.unop).op
      (inv x.down.1 ≫ (e.app U x).down.1) =
    inv ((F.presheafHom O M).map (G.map f.unop).op x.down.1) ≫
      (e.app V (((F.presheafIso G O M).toFunctor ⋙ uliftFunctor.{w}).map f x)).down.1
  rw [hn]
  exact (Pseudofunctor.presheafHom_map_comp (G.map f.unop) (inv x.down.1)
    (e.app U x).down.1).trans
      (congrArg (· ≫ _) (Pseudofunctor.presheafHom_map_inv (G.map f.unop) x.down.1))

/-- Postcompose local isomorphisms by a natural family of isomorphisms. -/
private noncomputable def presheafIsoPostcomp
    (ε : ∀ U : Dᵒᵖ, (G.op ⋙ F.presheafHom M N).obj U)
    (hε : ∀ U, IsIso (ε U))
    (hεmap : ∀ {U V : Dᵒᵖ} (f : U ⟶ V),
      (G.op ⋙ F.presheafHom M N).map f (ε U) = ε V) :
    (F.presheafIso G O M).toFunctor ⋙ uliftFunctor.{w} ⟶
      (F.presheafIso G O N).toFunctor ⋙ uliftFunctor.{w} where
  app U := TypeCat.ofHom fun x ↦
    ⟨⟨x.down.1 ≫ ε U, @IsIso.comp_isIso' _ _ _ _ _ _ _ x.down.2 (hε U)⟩⟩
  naturality U V f := by
    ext x
    apply ULift.ext
    apply Subtype.ext
    change (F.presheafHom O M).map (G.map f.unop).op x.down.1 ≫ ε V =
      (F.presheafHom O N).map (G.map f.unop).op (x.down.1 ≫ ε U)
    exact ((Pseudofunctor.presheafHom_map_comp (G.map f.unop) x.down.1 (ε U)).trans
      (congrArg (_ ≫ ·) (hεmap f))).symm

end

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

variable (L L' : modulesPseudofunctor.obj (.mk (op X)))
  [SheafOfModules.IsInvertible.{u, u, u} (L : X.Modules)]
  [SheafOfModules.IsInvertible.{u, u, u} (L' : X.Modules)]

/-- The isomorphism `V^* 𝒪 ≅ V^* L` underlying a section of `Isom(𝒪, L)`. -/
def etaleIsoTorsorVal {U : X.Etaleᵒᵖ} (x : (etaleIsoTorsor L).sheaf.obj.obj U) :
    (modulesPseudofunctor.map ((toProEt X ⋙ ProEt.forget X).obj U.unop).hom.op.toLoc).toFunctor.obj
        (unitObj X) ⟶
      (modulesPseudofunctor.map
        ((toProEt X ⋙ ProEt.forget X).obj U.unop).hom.op.toLoc).toFunctor.obj
        L :=
  x.down.1

instance {U : X.Etaleᵒᵖ} (x : (etaleIsoTorsor L).sheaf.obj.obj U) :
    IsIso (etaleIsoTorsorVal L x) :=
  x.down.2

lemma etaleIsoTorsorVal_injective {U : X.Etaleᵒᵖ} :
    Function.Injective (etaleIsoTorsorVal L (U := U)) :=
  fun _ _ h ↦ ULift.ext (Subtype.ext h)

/-- The section of `Isom(𝒪, L)` given by an isomorphism `V^* 𝒪 ≅ V^* L`. -/
def etaleIsoTorsorMk {U : X.Etaleᵒᵖ}
    (φ : (modulesPseudofunctor.map
      ((toProEt X ⋙ ProEt.forget X).obj U.unop).hom.op.toLoc).toFunctor.obj
        (unitObj X) ⟶
      (modulesPseudofunctor.map
        ((toProEt X ⋙ ProEt.forget X).obj U.unop).hom.op.toLoc).toFunctor.obj
        L) (hφ : IsIso φ) : (etaleIsoTorsor L).sheaf.obj.obj U :=
  ⟨⟨φ, hφ⟩⟩

@[simp]
lemma etaleIsoTorsorVal_mk {U : X.Etaleᵒᵖ}
    (φ : (modulesPseudofunctor.map
      ((toProEt X ⋙ ProEt.forget X).obj U.unop).hom.op.toLoc).toFunctor.obj
        (unitObj X) ⟶
      (modulesPseudofunctor.map
        ((toProEt X ⋙ ProEt.forget X).obj U.unop).hom.op.toLoc).toFunctor.obj
        L) (hφ : IsIso φ) : etaleIsoTorsorVal L (etaleIsoTorsorMk L φ hφ) = φ :=
  rfl

lemma etaleIsoTorsorVal_vadd {U : X.Etaleᵒᵖ} (a : X.gmSheaf.obj.obj U)
    (x : (etaleIsoTorsor L).sheaf.obj.obj U) :
    etaleIsoTorsorVal L ((etaleIsoTorsor L).vadd U a x) =
      smulMor _ ((Additive.toMul a.down : Γ(U.unop.left, ⊤)ˣ) : Γ(U.unop.left, ⊤)) ≫
        etaleIsoTorsorVal L x :=
  rfl

/-- **The torsor `Isom(𝒪, L)` determines `L`.** An isomorphism of `𝔾ₘ`-torsors
`Isom(𝒪, L) ≅ Isom(𝒪, L')` comes from an isomorphism `L ≅ L'`: the local isomorphisms
`t⁻¹ ≫ e(t)`, for local trivialisations `t` of `L`, do not depend on `t` and glue. -/
lemma nonempty_iso_of_etaleIsoTorsor_iso
    (e : Sheaf.Torsor.Iso (etaleIsoTorsor L) (etaleIsoTorsor L')) : Nonempty (L ≅ L') := by
  have := Modules.IsInvertible.of_sheafOfModules (L : X.Modules)
  have := Modules.IsInvertible.of_sheafOfModules (L' : X.Modules)
  have : (L : X.Modules).IsQuasicoherent := IsInvertible.isQuasicoherent _
  have : (L' : X.Modules).IsQuasicoherent := IsInvertible.isQuasicoherent _
  let G := toProEt X ⋙ ProEt.forget X
  let F : Sheaf X.smallEtaleTopology (Type (u + 1)) :=
    ⟨etaleHom L L' ⋙ uliftFunctor.{u + 1},
      (isSheaf_iff_isSheaf_of_type _ _).2 ((Presieve.isSheaf_comp_uliftFunctor_iff _).2
        ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_etaleHom L L')))⟩
  let g : ∀ U, (etaleIsoTorsor L).sheaf.obj.obj U → F.obj.obj U :=
    presheafIsoDifference G e.iso.hom.hom
  have : MorphismProperty.ContainsIdentities
      (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.Etale.instIsMultiplicativeScheme.toContainsIdentities
  have hT : Limits.IsTerminal (Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ X
  have hg : ∀ ⦃U V : X.Etaleᵒᵖ⦄ (f : U ⟶ V) (x : (etaleIsoTorsor L).sheaf.obj.obj U),
      F.obj.map f (g U x) = g V ((etaleIsoTorsor L).sheaf.obj.map f x) := by
    intro U V f x
    exact presheafIsoDifference_naturality G e.iso.hom.hom f x
  have hinv : ∀ U (a : X.gmSheaf.obj.obj U) (x : (etaleIsoTorsor L).sheaf.obj.obj U),
      g U ((etaleIsoTorsor L).vadd U a x) = g U x := by
    intro U a x
    apply ULift.ext
    have hv := e.map_vadd U a x
    change inv (etaleIsoTorsorVal L ((etaleIsoTorsor L).vadd U a x)) ≫
        etaleIsoTorsorVal L' (e.iso.hom.hom.app U ((etaleIsoTorsor L).vadd U a x)) =
      inv (etaleIsoTorsorVal L x) ≫ etaleIsoTorsorVal L' (e.iso.hom.hom.app U x)
    rw [IsIso.inv_comp_eq, congrArg (etaleIsoTorsorVal L') hv, etaleIsoTorsorVal_vadd,
      etaleIsoTorsorVal_vadd]
    exact ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (IsIso.hom_inv_id_assoc (etaleIsoTorsorVal L x) _))).symm
  obtain ⟨σ, hσ⟩ := (etaleIsoTorsor L).exists_section_of_invariant F hT g hg hinv
  have hR := (etaleIsoTorsor L).nonemptySieve_mem (Etale.mk (𝟙 X))
  have hsh (A B : modulesPseudofunctor.obj (.mk (op X))) [(A : X.Modules).IsQuasicoherent]
      [(B : X.Modules).IsQuasicoherent] :=
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_etaleHom A B)) _ hR
  have hiso : IsIso σ.down := Pseudofunctor.isIso_of_isIso_presheafHom_map G σ.down
    (hsh L' L) (hsh L L) (hsh L' L') (fun W f hf ↦ by
      obtain ⟨x⟩ := hf
      have : IsIso (etaleIsoTorsorVal L x) := x.down.2
      have h1 := hσ (op W) x
      rw [show hT.from W = f from hT.hom_ext _ _] at h1
      have h2 : inv (etaleIsoTorsorVal L x) ≫ etaleIsoTorsorVal L' (e.iso.hom.hom.app _ x) =
          (modulesPseudofunctor.presheafHom L L').map (G.map f).op σ.down :=
        congrArg ULift.down h1
      have : IsIso (etaleIsoTorsorVal L' (e.iso.hom.hom.app _ x)) :=
        (e.iso.hom.hom.app _ x).down.2
      rw [← h2]
      exact IsIso.comp_isIso)
  exact ⟨(Cat.Hom.toNatIso (modulesPseudofunctor.mapId _)).symm.app L ≪≫
    @asIso _ _ _ _ σ.down hiso ≪≫
    (Cat.Hom.toNatIso (modulesPseudofunctor.mapId _)).app L'⟩

/-- Isomorphic modules have isomorphic torsors of trivialisations. -/
lemma etaleIsoTorsor_equiv_of_iso (e : L ≅ L') : etaleIsoTorsor L ≈ etaleIsoTorsor L' := by
  have : MorphismProperty.ContainsIdentities
      (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.Etale.instIsMultiplicativeScheme.toContainsIdentities
  have hT : Limits.IsTerminal (Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ X
  let G := toProEt X ⋙ ProEt.forget X
  let ε₀ : (etaleHom L L').obj (op (Etale.mk (𝟙 X))) :=
    ((Cat.Hom.toNatIso (modulesPseudofunctor.mapId _)).app L ≪≫ e ≪≫
      ((Cat.Hom.toNatIso (modulesPseudofunctor.mapId _)).app L').symm).hom
  have hε₀ : IsIso ε₀ := Iso.isIso_hom _
  let ε (U : X.Etaleᵒᵖ) : (etaleHom L L').obj U := (etaleHom L L').map (hT.from U.unop).op ε₀
  have hε (U : X.Etaleᵒᵖ) : IsIso (ε U) :=
    Pseudofunctor.isIso_presheafHom_map (F := modulesPseudofunctor) (M := L) (N := L')
      (G.map (hT.from U.unop)) ε₀
  have hεmap {U V : X.Etaleᵒᵖ} (f : U ⟶ V) : (etaleHom L L').map f (ε U) = ε V := by
    have h1 : (hT.from U.unop).op ≫ f = (hT.from V.unop).op := Quiver.Hom.unop_inj (hT.hom_ext _ _)
    calc (etaleHom L L').map f (ε U) = (etaleHom L L').map ((hT.from U.unop).op ≫ f) ε₀ :=
          (Functor.map_comp_apply _ _ _ _).symm
      _ = ε V := by rw [h1]
  let φ : (etaleIsoTorsor L).sheaf ⟶ (etaleIsoTorsor L').sheaf :=
    ⟨presheafIsoPostcomp G ε hε (fun f ↦ hεmap f)⟩
  exact ⟨Sheaf.Torsor.Iso.ofHom φ fun U a x ↦ etaleIsoTorsorVal_injective L' (U := U)
    (Category.assoc _ _ _)⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The class of the étale `𝔾ₘ`-torsor `Isom(𝒪_X, L)` of an invertible module `L`. -/
noncomputable def Pic.etaleTorsorClass (L : X.Pic) :
    _root_.Quotient (Sheaf.Torsor.setoid (G := X.gmSheaf)) :=
  haveI : SheafOfModules.IsInvertible.{u, u, u} ((fromSkeleton X.Modules).obj L.val) :=
    Pic.isInvertible L
  _root_.Quotient.mk _ (Modules.etaleIsoTorsor
    (((fromSkeleton X.Modules).obj L.val : modulesPseudofunctor.obj (.mk (op X)))))

lemma Pic.etaleTorsorClass_mk (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M] :
    (Pic.mk M).etaleTorsorClass =
      _root_.Quotient.mk _
        (Modules.etaleIsoTorsor ((M : modulesPseudofunctor.obj (.mk (op X))))) := by
  have : SheafOfModules.IsInvertible.{u, u, u} ((fromSkeleton X.Modules).obj (toSkeleton M)) :=
    Pic.isInvertible (Pic.mk M)
  have : SheafOfModules.IsInvertible.{u, u, u} ((fromSkeleton X.Modules).obj (Pic.mk M).val) :=
    Pic.isInvertible (Pic.mk M)
  exact _root_.Quotient.sound
    (Modules.etaleIsoTorsor_equiv_of_iso _ _ (fromSkeletonToSkeletonIso M))

/-- **`L ↦ Isom(𝒪_X, L)` is injective**: invertible modules whose étale torsors of
trivialisations are isomorphic are isomorphic. -/
theorem Pic.injective_etaleTorsorClass : Function.Injective (Pic.etaleTorsorClass (X := X)) := by
  intro L L' h
  have : SheafOfModules.IsInvertible.{u, u, u} ((fromSkeleton X.Modules).obj L.val) :=
    Pic.isInvertible L
  have : SheafOfModules.IsInvertible.{u, u, u} ((fromSkeleton X.Modules).obj L'.val) :=
    Pic.isInvertible L'
  obtain ⟨e⟩ := Quotient.exact (s := Sheaf.Torsor.setoid) h
  obtain ⟨f⟩ := Modules.nonempty_iso_of_etaleIsoTorsor_iso _ _ e
  exact Pic.eq_iff_nonempty_iso.2 ⟨f⟩

end AlgebraicGeometry.Scheme

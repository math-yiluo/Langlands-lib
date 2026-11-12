import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionPresheaf

/-! # Sheaves after composition of bases -/

universe u

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition

open OriginalBaseTransport

variable {S T : Scheme.{u}}

/-- The absolute total presheaf of a relative fppf sheaf is an fppf sheaf. -/
theorem isSheaf_totalPresheaf (F : Presheaf S)
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F) :
    CategoryTheory.Presheaf.IsSheaf Scheme.fppfTopology (totalPresheaf F) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro V R hR x hx
  let Q := CategoryTheory.uliftYoneda.{u + 1}.obj S
  have hQ : Presieve.IsSheaf Scheme.fppfTopology Q :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((GrothendieckTopology.uliftYoneda.{u + 1} Scheme.fppfTopology).obj S).property
  let y := x.map (totalToBase F)
  have hy : y.Compatible := hx.map (totalToBase F)
  obtain ⟨s, hs, hsu⟩ := hQ R hR y hy
  let U : Over S := Over.mk (show V ⟶ S from s.down)
  let RS : Sieve U := (Sieve.overEquiv U).symm (show Sieve U.left from R)
  have hRS : RS ∈ fppfTopology S U := by
    change Sieve.overEquiv U RS ∈ Scheme.fppfTopology U.left
    rw [show Sieve.overEquiv U RS = R from (Sieve.overEquiv U).apply_symm_apply R]
    exact hR
  have hstr : ∀ {W : Over S} (f : W ⟶ U) (hf : RS f),
      (totalToBase F).app (op W.left) (x f.left hf) = ULift.up W.hom := by
    intro W f hf
    have hh := hs f.left hf
    change ULift.up (f.left ≫ s.down) = _ at hh
    exact hh.symm.trans (congrArg ULift.up f.w)
  let z : Presieve.FamilyOfElements F RS.arrows := fun W f hf =>
    (totalFiberIso F).inv.app (op W) ⟨x f.left hf, hstr f hf⟩
  have hz : z.Compatible := by
    intro W₁ W₂ W a b f₁ f₂ hf₁ hf₂ hab
    dsimp only [z]
    rw [← (totalFiberIso F).inv.naturality_apply a.op
      (⟨x f₁.left hf₁, hstr f₁ hf₁⟩ : (fiberPresheaf (totalToBase F)).obj (op W₁)),
      ← (totalFiberIso F).inv.naturality_apply b.op
      (⟨x f₂.left hf₂, hstr f₂ hf₂⟩ : (fiberPresheaf (totalToBase F)).obj (op W₂))]
    apply congrArg
    apply Subtype.ext
    exact hx a.left b.left hf₁ hf₂ (congrArg CommaMorphism.left hab)
  obtain ⟨t, ht, htu⟩ := hF.isSheafFor RS hRS z hz
  refine ⟨⟨s.down, t⟩, ?_, ?_⟩
  · intro W f hf
    let fS : Over.mk (f ≫ s.down) ⟶ U := Over.homMk f rfl
    have hh := ht fS hf
    have hh' := congrArg (fun v =>
      ((totalFiberIso F).hom.app (op (Over.mk (f ≫ s.down))) v).val) hh
    change (totalPresheaf F).map f.op ⟨s.down, t⟩ = x f hf
    exact hh'.trans (by
      change ((totalFiberIso F).hom.app (op (Over.mk (f ≫ s.down)))
        ((totalFiberIso F).inv.app (op (Over.mk (f ≫ s.down)))
          (⟨x f hf, hstr fS hf⟩ :
            (fiberPresheaf (totalToBase F)).obj (op (Over.mk (f ≫ s.down)))))).val = _
      exact congrArg Subtype.val ((totalFiberIso F).inv_hom_id_app_apply
        (op (Over.mk (f ≫ s.down))) ⟨x f hf, hstr fS hf⟩))
  · rintro ⟨s', t'⟩ ht'
    have he : ULift.up s' = s := hsu (ULift.up s') (ht'.map (totalToBase F))
    have he' : s' = s.down := congrArg ULift.down he
    subst s'
    have htt : t' = t := htu t' (by
      intro W f hf
      have hh : (fiberPresheaf (totalToBase F)).map f.op
          ((totalFiberIso F).hom.app (op U) t') =
            ⟨x f.left hf, hstr f hf⟩ := by
        apply Subtype.ext
        exact ht' f.left hf
      have hh' := congrArg ((totalFiberIso F).inv.app (op W)) hh
      rw [(totalFiberIso F).inv.naturality_apply,
        Iso.hom_inv_id_app_apply] at hh'
      exact hh')
    subst t'
    rfl

/-- Forget the equation fixing the structure map of a relative fibre section. -/
def fiberToRestriction {F : AbsolutePresheaf.{u}}
    (s : F ⟶ CategoryTheory.uliftYoneda.{u + 1}.obj S) :
    fiberPresheaf s ⟶ (Over.forget S).op ⋙ F where
  app _ := TypeCat.ofHom Subtype.val
  naturality {_ _} _ := rfl

/-- Fixing the structure map of an absolute fppf sheaf gives a relative fppf sheaf. -/
theorem isSheaf_fiberPresheaf {F : AbsolutePresheaf.{u}}
    (s : F ⟶ CategoryTheory.uliftYoneda.{u + 1}.obj S)
    (hF : CategoryTheory.Presheaf.IsSheaf Scheme.fppfTopology F) :
    CategoryTheory.Presheaf.IsSheaf (fppfTopology S) (fiberPresheaf s) := by
  rw [isSheaf_iff_isSheaf_of_type]
  have hF' : Presieve.IsSheaf (fppfTopology S) ((Over.forget S).op ⋙ F) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Over.forget S).op_comp_isSheaf_of_isSheaf
        (fppfTopology S) Scheme.fppfTopology F hF)
  let Q := CategoryTheory.uliftYoneda.{u + 1}.obj S
  have hQ : Presieve.IsSheaf (fppfTopology S) ((Over.forget S).op ⋙ Q) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Over.forget S).op_comp_isSheaf_of_isSheaf
        (fppfTopology S) Scheme.fppfTopology Q
        ((GrothendieckTopology.uliftYoneda.{u + 1} Scheme.fppfTopology).obj S).property)
  intro U R hR x hx
  obtain ⟨t, ht, htu⟩ := hF' R hR (x.map (fiberToRestriction s))
    (hx.map (fiberToRestriction s))
  have hst : s.app (op U.left) t = ULift.up U.hom := by
    apply (hQ R hR).isSeparatedFor.ext
    intro W f hf
    change Q.map f.left.op (s.app (op U.left) t) = Q.map f.left.op (ULift.up U.hom)
    calc
      Q.map f.left.op (s.app (op U.left) t) =
          s.app (op W.left) (F.map f.left.op t) :=
        (s.naturality_apply f.left.op t).symm
      _ = s.app (op W.left) (x f hf).val := congrArg (s.app (op W.left)) (ht f hf)
      _ = ULift.up W.hom := (x f hf).property
      _ = Q.map f.left.op (ULift.up U.hom) := congrArg ULift.up f.w.symm
  refine ⟨⟨t, hst⟩, ?_, ?_⟩
  · intro W f hf
    apply Subtype.ext
    exact ht f hf
  · intro t' ht'
    apply Subtype.ext
    exact htu t'.val (ht'.map (fiberToRestriction s))

/-- Composing bases preserves the fppf sheaf condition for arbitrary scheme maps. -/
theorem isSheaf_presheaf (g : S ⟶ T) (F : Presheaf S)
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F) :
    CategoryTheory.Presheaf.IsSheaf (fppfTopology T) (presheaf g F) :=
  isSheaf_fiberPresheaf (totalToBase F ≫ CategoryTheory.uliftYoneda.{u + 1}.map g)
    (isSheaf_totalPresheaf F hF)

/-- An fppf sheaf over the composed base, retaining each original structure map. -/
def sheaf (g : S ⟶ T) (F : FppfSheaf S) : FppfSheaf T :=
  ⟨presheaf g F.obj, isSheaf_presheaf g F.obj F.property⟩

/-- Composition of bases acts functorially on fppf sheaves. -/
def sheafFunctor (g : S ⟶ T) : FppfSheaf S ⥤ FppfSheaf T where
  obj := sheaf g
  map f := ⟨map g f.hom⟩
  map_id F := by
    apply Sheaf.hom_ext
    exact (presheafFunctor g).map_id F.obj
  map_comp f h := by
    apply Sheaf.hom_ext
    exact (presheafFunctor g).map_comp f.hom h.hom

end Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition

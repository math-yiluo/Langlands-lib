/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraColimit
import WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps

/-! # Including a limit of affine schemes in all schemes over the base

Source: Stacks Project, Limits, Lemmas 01YX and 01YW, the local universal-property
argument in the relative-spectrum construction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable def structureAlgebraObj {X S : Scheme.{u}} (f : X ⟶ S) :
    S.CommAlgebraSheaf :=
  Under.mk (⟨f.c⟩ : Scheme.sheaf _ ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj (Scheme.sheaf _))

private theorem algebra_eqToHom_app {S : Scheme.{u}}
    {A B : S.CommAlgebraSheaf} (e : A = B) (V : S.Opensᵒᵖ) :
    (eqToHom e).right.hom.app V = eqToHom (by cases e; rfl) := by
  cases e
  rfl

private theorem exists_over_map_of_algebra {S X Y : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) [IsAffineHom g] (α : structureAlgebraObj g ⟶ structureAlgebraObj f) :
    ∃ (h : X ⟶ Y) (w : h ≫ g = f), ∀ U : S.affineOpens,
      h.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (by rw [← w, Scheme.Hom.comp_preimage]) = α.right.hom.app (op U.1) := by
  obtain ⟨k, hw, hc, ha⟩ := affine_algebra_local_maps f g α
  let 𝒰 := X.openCoverOfIsOpenCover (fun U : S.affineOpens ↦ f ⁻¹ᵁ U.1)
    (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))
  let h : X ⟶ Y := 𝒰.glueMorphisms k hc
  have hi (U : S.affineOpens) : (f ⁻¹ᵁ U.1).ι ≫ h = k U :=
    𝒰.ι_glueMorphisms k hc U
  have w : h ≫ g = f := by
    apply 𝒰.hom_ext
    intro U
    change (f ⁻¹ᵁ U.1).ι ≫ h ≫ g = (f ⁻¹ᵁ U.1).ι ≫ f
    rw [← Category.assoc, hi, hw]
  refine ⟨h, w, ?_⟩
  intro U
  have e : ⊤ ≤ k U ⁻¹ᵁ (g ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage]
    simp
  have ea := ha U e
  simp only [← hi U] at ea
  rw [Scheme.Hom.comp_appLE] at ea
  simp only [Scheme.Opens.ι_appLE] at ea
  apply (cancel_mono (f ⁻¹ᵁ U.1).topIso.inv).mp
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso_inv, Category.assoc,
    ← Functor.map_comp] at ea ⊢
  convert ea using 1
  congr 1

private noncomputable def structureAlgebra (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ S.CommAlgebraSheaf := by
  refine {
    obj := fun Y ↦ structureAlgebraObj Y.unop.hom
    map := fun {Y Y'} h ↦ Under.homMk ⟨{
      app := fun V ↦ h.unop.left.appLE (Y.unop.hom ⁻¹ᵁ V.unop)
        (Y'.unop.hom ⁻¹ᵁ V.unop)
        (by rw [← Over.w h.unop, Scheme.Hom.comp_preimage])
      naturality := ?_ }⟩ ?_
    map_id := ?_
    map_comp := ?_ }
  · intro U V i
    change Y.unop.left.presheaf.map
        ((TopologicalSpace.Opens.map Y.unop.hom.base).map i.unop).op ≫ _ = _ ≫
      Y'.unop.left.presheaf.map ((TopologicalSpace.Opens.map Y'.unop.hom.base).map i.unop).op
    simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change Y.unop.hom.app V.unop ≫ h.unop.left.appLE _ _ _ =
      Y'.unop.hom.app V.unop
    rw [← Scheme.Hom.comp_appLE]
    exact (Scheme.Hom.congr_app (Over.w h.unop).symm V.unop).symm
  · intro Y
    apply StructuredArrow.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change Scheme.Hom.appLE (𝟙 Y.unop.left) _ _ _ = 𝟙 _
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
      homOfLE_refl, op_id, Category.id_comp]
    exact CategoryTheory.Functor.map_id _ _
  · intro Y Y' Y'' h k
    apply StructuredArrow.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change (k.unop.left ≫ h.unop.left).appLE _ _ _ =
      h.unop.left.appLE _ _ _ ≫ k.unop.left.appLE _ _ _
    rw [Scheme.Hom.appLE_comp_appLE]

private theorem structureAlgebra_bijective (S : Scheme.{u}) (X Y : Over S)
    [IsAffineHom Y.hom] :
    Function.Bijective (fun h : X ⟶ Y ↦ (structureAlgebra S).map h.op) := by
  constructor
  · intro a b hab
    apply Over.OverMorphism.ext
    apply Scheme.hom_ext_of_forall
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (show X.hom x ∈ (⊤ : S.Opens) from trivial) isOpen_univ
    refine ⟨X.hom ⁻¹ᵁ U, hxU, ?_⟩
    have : IsAffine (Y.hom ⁻¹ᵁ U).toScheme := hU.preimage Y.hom
    have hh : a.left.resLE (Y.hom ⁻¹ᵁ U) (X.hom ⁻¹ᵁ U)
        (by rw [← Over.w a, Scheme.Hom.comp_preimage]) =
      b.left.resLE (Y.hom ⁻¹ᵁ U) (X.hom ⁻¹ᵁ U)
        (by rw [← Over.w b, Scheme.Hom.comp_preimage]) := by
      apply ext_of_isAffine
      simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
      have he := congrArg (fun t ↦ t.right.hom.app (op U)) hab
      change a.left.appLE (Y.hom ⁻¹ᵁ U) (X.hom ⁻¹ᵁ U) _ =
        b.left.appLE (Y.hom ⁻¹ᵁ U) (X.hom ⁻¹ᵁ U) _ at he
      rw [he]
    simpa only [Scheme.Hom.resLE_comp_ι] using
      congrArg (· ≫ (Y.hom ⁻¹ᵁ U).ι) hh
  · intro α
    obtain ⟨h, w, ha⟩ := exists_over_map_of_algebra X.hom Y.hom α
    refine ⟨Over.homMk h w, ?_⟩
    apply Under.UnderMorphism.ext
    apply CategoryTheory.Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext _ _ (B := fun U : S.affineOpens ↦ U.1)
      (by
        change TopologicalSpace.Opens.IsBasis (Set.range (fun U : S.affineOpens ↦ U.1))
        rw [show Set.range (fun U : S.affineOpens ↦ U.1) = S.affineOpens by
          ext V
          constructor
          · rintro ⟨U, rfl⟩
            exact U.2
          · intro hV
            exact ⟨⟨V, hV⟩, rfl⟩]
        exact S.isBasis_affineOpens)
    intro U
    exact ha U

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A directed inverse limit in schemes affine over `S` is also a limit in `Over S`.

Source: Stacks Project, Limits, Lemma 01YX (lemma-directed-inverse-system-has-limit),
the universal-property argument, using Lemma 01YW on each affine open of the base.
(blueprint: lem-weil-pbc-affine-over-limit-inclusion)

Proof: Send the limiting cone through the relative-spectrum anti-equivalence to a
colimit of quasi-coherent algebras. The directed algebra-colimit theorem constructs a
colimit in all algebra sheaves whose vertex is quasi-coherent. Thus the full-subcategory
inclusion creates this colimit and preserves the given colimit cocone.

Define the contravariant structure-algebra functor on all schemes over S, not only the
affine ones. The object and morphism clauses of the anti-equivalence identify its
restriction with the underlying algebra functor. Consequently the given cone's
structure algebras form a colimit in all algebra sheaves.

For an arbitrary test scheme T over S and an affine Y over S, the structure-algebra map
on Hom(T,Y) is bijective. Injectivity follows by restricting to inverse images of affine
base opens and using the Gamma--Spec adjunction. For surjectivity,
`affine_algebra_local_maps` constructs compatible maps on these inverse images;
scheme-morphism gluing produces the global map over S. Its algebra map is the prescribed
one by equality on the affine basis. No quasi-separatedness of S or T is needed.

Apply the algebra colimit's universal property to the structure algebras of any test
cone. The Hom bijection produces its unique scheme factorization. Functoriality and
injectivity give the projection identities, and colimit uniqueness gives uniqueness
of the factorization. This is the required universal property in Over S. -/
theorem isLimit_affineOver_inclusion
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (S : Scheme.{u})
    (F : Jᵒᵖ ⥤ ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))
    (c : Cone F) (hc : IsLimit c) :
    Nonempty (IsLimit
      ((ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)).mapCone c)) := by
  classical
  let P : ObjectProperty S.CommAlgebraSheaf := fun A ↦ A.toModule.IsQuasicoherent
  let I := ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)
  let K := structureAlgebra S
  obtain ⟨_, E, hobj, _, hmap, _⟩ := affine_morphism_relative_spec S
  let G := F.rightOp ⋙ E.functor
  let d := E.functor.mapCocone (coconeRightOpOfCone c)
  have hd : IsColimit d :=
    isColimitOfPreserves E.functor (isColimitCoconeRightOpOfCone F hc)
  obtain ⟨a, ⟨ha⟩, hqc, _⟩ := Scheme.quasiCoherentAlgebra_colimit S J
    (G ⋙ P.ι) (fun j ↦ (G.obj j).property)
  let : HasColimit (G ⋙ P.ι) := ⟨⟨a, ha⟩⟩
  let : CreatesColimit G P.ι := createsColimitFullSubcategoryInclusion' G ha hqc
  have hd' : IsColimit (P.ι.mapCocone d) := isColimitOfPreserves P.ι hd
  let e : E.functor ⋙ P.ι ≅ I.op ⋙ K := NatIso.ofComponents
    (fun Y ↦ eqToIso (hobj Y.unop)) (by
      intro Y Y' h
      apply Under.UnderMorphism.ext
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      change (E.functor.map h).hom.right.hom.app V ≫
          (eqToHom (hobj Y'.unop)).right.hom.app V =
        (eqToHom (hobj Y.unop)).right.hom.app V ≫
          h.unop.hom.left.appLE (Y.unop.obj.hom ⁻¹ᵁ V.unop)
            (Y'.unop.obj.hom ⁻¹ᵁ V.unop)
            (by rw [← Over.w h.unop.hom, Scheme.Hom.comp_preimage])
      simp only [algebra_eqToHom_app]
      erw [hmap Y'.unop Y.unop h.unop V.unop]
      simp)
  have hK : IsColimit ((I.op ⋙ K).mapCocone (coconeRightOpOfCone c)) :=
    IsColimit.mapCoconeEquiv e hd'
  let c' := I.mapCone c
  let : IsAffineHom c'.pt.hom := c.pt.property
  let (j : Jᵒᵖ) : IsAffineHom (F.obj j).obj.hom := (F.obj j).property
  have hK' : IsColimit (K.mapCocone (coconeRightOpOfCone c')) := hK
  let lift (s : Cone (F ⋙ I)) : s.pt ⟶ c'.pt :=
    Classical.choose ((structureAlgebra_bijective S s.pt c'.pt).2
      (hK'.desc (K.mapCocone (coconeRightOpOfCone s))))
  have hlift (s : Cone (F ⋙ I)) :
      K.map (lift s).op = hK'.desc (K.mapCocone (coconeRightOpOfCone s)) :=
    Classical.choose_spec ((structureAlgebra_bijective S s.pt c'.pt).2
      (hK'.desc (K.mapCocone (coconeRightOpOfCone s))))
  refine ⟨{ lift := lift, fac := ?_, uniq := ?_ }⟩
  · intro s j
    apply (structureAlgebra_bijective S s.pt (F.obj j).obj).1
    change K.map ((lift s) ≫ c'.π.app j).op = K.map (s.π.app j).op
    rw [op_comp, K.map_comp, hlift]
    exact hK'.fac (K.mapCocone (coconeRightOpOfCone s)) j.unop
  · intro s m w
    apply (structureAlgebra_bijective S s.pt c'.pt).1
    change K.map m.op = K.map (lift s).op
    rw [hlift]
    apply hK'.uniq (K.mapCocone (coconeRightOpOfCone s))
    intro j
    change K.map (c'.π.app (op j)).op ≫ K.map m.op =
      K.map (s.π.app (op j)).op
    rw [← K.map_comp, ← op_comp, w]

end AlgebraicGeometry

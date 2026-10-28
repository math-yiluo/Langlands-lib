import Langlands.CategoryTheory.EquivariantDiagramPreadditive
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.Functor

/-! # Complexes of varying-group equivariant diagrams -/

universe uG uI vI uC vC uι

namespace Langlands.EquivariantDiagram

open CategoryTheory

variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{uG}}
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable {ι : Type uι} (c : ComplexShape ι)

/-- A complex of equivariant diagrams gives an equivariant diagram of complexes. -/
def complexToDiagram :
    HomologicalComplex (EquivariantDiagram D C) c ⥤
      EquivariantDiagram D (HomologicalComplex C c) where
  obj K :=
    { obj := (((forget (D := D) (C := C)).mapHomologicalComplex c).obj K).asFunctor
      ρ i :=
        { toFun g :=
            { f n := (K.X n).ρ i g
              comm' p q _ := (K.d p q).comm i g }
          map_one' := by
            apply HomologicalComplex.hom_ext
            intro n
            exact (K.X n).ρ i |>.map_one
          map_mul' g h := by
            apply HomologicalComplex.hom_ext
            intro n
            exact (K.X n).ρ i |>.map_mul g h }
      comm f g := by
        apply HomologicalComplex.hom_ext
        intro n
        exact (K.X n).comm f g }
  map φ :=
    { hom :=
        { app i :=
            { f n := (φ.f n).hom.app i
              comm' p q _ := NatTrans.congr_app (congrArg Hom.hom (φ.comm p q)) i }
          naturality i j f := by
            apply HomologicalComplex.hom_ext
            intro n
            exact (φ.f n).hom.naturality f }
      comm i g := by
        apply HomologicalComplex.hom_ext
        intro n
        exact (φ.f n).comm i g }
  map_id K := by
    apply Hom.ext
    apply NatTrans.ext
    funext i
    apply HomologicalComplex.hom_ext
    intro n
    rfl
  map_comp φ ψ := by
    apply Hom.ext
    apply NatTrans.ext
    funext i
    apply HomologicalComplex.hom_ext
    intro n
    rfl

/-- Evaluate an equivariant diagram of complexes degree by degree. -/
def diagramToComplex :
    EquivariantDiagram D (HomologicalComplex C c) ⥤
      HomologicalComplex (EquivariantDiagram D C) c where
  obj M :=
    { X n := (mapFunctor (HomologicalComplex.eval C c n)).obj M
      d p q := (mapNatTrans (HomologicalComplex.dNatTrans C c p q)).app M
      shape p q h := by
        apply Hom.ext
        apply NatTrans.ext
        funext i
        exact (M.obj.obj i).shape p q h
      d_comp_d' p q r _ _ := by
        apply Hom.ext
        apply NatTrans.ext
        funext i
        exact (M.obj.obj i).d_comp_d p q r }
  map φ :=
    { f n := (mapFunctor (HomologicalComplex.eval C c n)).map φ
      comm' p q _ := (mapNatTrans (HomologicalComplex.dNatTrans C c p q)).naturality φ }
  map_id M := by
    apply HomologicalComplex.hom_ext
    intro n
    exact (mapFunctor (HomologicalComplex.eval C c n)).map_id M
  map_comp φ ψ := by
    apply HomologicalComplex.hom_ext
    intro n
    exact (mapFunctor (HomologicalComplex.eval C c n)).map_comp φ ψ

/-- Interchanging degree and group-diagram axes is an equivalence. -/
def complexEquivalence :
    HomologicalComplex (EquivariantDiagram D C) c ≌
      EquivariantDiagram D (HomologicalComplex C c) where
  functor := complexToDiagram c
  inverse := diagramToComplex c
  unitIso := NatIso.ofComponents (fun K => Iso.refl K) (by
    intro K L φ
    simp only [Functor.id_map, Functor.comp_map, Iso.refl_hom]
    apply HomologicalComplex.hom_ext
    intro n
    apply Hom.ext
    apply NatTrans.ext
    funext i
    change (φ.f n).hom.app i ≫ 𝟙 _ = 𝟙 _ ≫ (φ.f n).hom.app i
    simp only [Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents (fun M => Iso.refl M) (by
    intro M N φ
    simp only [Functor.id_map, Functor.comp_map, Iso.refl_hom]
    apply Hom.ext
    apply NatTrans.ext
    funext i
    apply HomologicalComplex.hom_ext
    intro n
    change (φ.hom.app i).f n ≫ 𝟙 _ = 𝟙 _ ≫ (φ.hom.app i).f n
    simp only [Category.comp_id, Category.id_comp])
  functor_unitIso_comp K := by
    apply Hom.ext
    apply NatTrans.ext
    funext i
    apply HomologicalComplex.hom_ext
    intro n
    change 𝟙 ((K.X n).obj.obj i) ≫ 𝟙 _ = 𝟙 _
    exact Category.comp_id _

end Langlands.EquivariantDiagram

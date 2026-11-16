import Langlands.Geometry.FormalGroup.DeligneShiftReframe
import Langlands.Geometry.FormalGroup.DeligneAdmissibleBaseChange

/-! # Actual shift and frame comparisons under arbitrary base change -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F] {X Y : TopCat.{u}}

namespace LatticePiSheaf

/-- Degree translation and inverse image compare by identity on the actual total lattice. -/
def inverseImageShiftIso (M : LatticePiSheaf d π Y) (f : X ⟶ Y) (k : ZMod d) :
    (M.shift k).inverseImage f ≅ (M.inverseImage f).shift k where
  hom := {
    total := 𝟙 _
    component _ := 𝟙 _
    inclusion i := by
      change 𝟙 _ ≫ _ = _ ≫ (latticeScalarFunctor d π X).map (𝟙 _)
      simp only [Category.id_comp]
      rfl }
  inv := {
    total := 𝟙 _
    component _ := 𝟙 _
    inclusion i := by
      change 𝟙 _ ≫ _ = _ ≫ (latticeScalarFunctor d π X).map (𝟙 _)
      simp only [Category.id_comp]
      rfl }
  hom_inv_id := Hom.ext_total (Category.id_comp _)
  inv_hom_id := Hom.ext_total (Category.id_comp _)

end LatticePiSheaf

/-- The total rational inverse-image comparison intertwines all integer Pi powers. -/
theorem inverseImageRationalLatticeIso_zpow (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (hπ : algebraMap O F π ≠ 0)
    (n : ℤ) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map
        (rationalPiAut F Y d π M hπ ^ n).hom ≫
          (inverseImageRationalLatticeIso F f M).hom =
      (inverseImageRationalLatticeIso F f M).hom ≫
        (rationalPiAut F X d π
          ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) hπ ^ n).hom := by
  let P := TopCat.Sheaf.pullback (ModuleCat.{u} F) f
  let e := inverseImageRationalLatticeIso F f M
  let T := (Aut.autMulEquivOfIso e).toMonoidHom.comp
    (P.mapAut (rationalLattice F Y d π M))
  have hT : T (rationalPiAut F Y d π M hπ) =
      rationalPiAut F X d π
        ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) hπ := by
    apply Aut.ext
    change e.inv ≫ P.map (rationalPiAut F Y d π M hπ).hom ≫ e.hom = _
    rw [inverseImageRationalLatticeIso_pi, Iso.inv_hom_id_assoc]
  have h := map_zpow T (rationalPiAut F Y d π M hπ) n
  rw [hT] at h
  have hh := congrArg Iso.hom h
  change e.inv ≫ P.map (rationalPiAut F Y d π M hπ ^ n).hom ≫ e.hom = _ at hh
  have hhh := congrArg (fun t => e.hom ≫ t) hh
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hhh

namespace FramedLatticePiSheaf

/-- Inverse image commutes with precomposition by an actual rational frame automorphism. -/
theorem inverseImage_reframe (M : FramedLatticePiSheaf d π Y F) (f : X ⟶ Y)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    (M.reframe F g).inverseImage f = (M.inverseImage f).reframe F g := by
  dsimp only [inverseImage, reframe]
  congr 1
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  have hc := (inverseImageConstantIso (O := F) f).inv.naturality g.toModuleIso.hom
  dsimp only [Functor.comp_map] at hc
  erw [← Category.assoc, ← hc, Category.assoc]

variable (M : FramedLatticePiSheaf d π Y F) (f : X ⟶ Y)
  (hπ : algebraMap O F π ≠ 0) (k : ℤ)

/-- The total frame of a pulled integer shift is the shifted pulled total frame. -/
theorem frameToTotal_inverseImage_shiftInt :
    ((M.shiftInt F hπ k).inverseImage f).frameToTotal F =
      ((M.inverseImage f).shiftInt F hπ k).frameToTotal F := by
  apply (cancel_epi ((inverseImageConstantIso (O := F) f).hom.app
    (ModuleCat.of F (Fin d → F)))).mp
  rw [← frameToTotal_pullback, frameToTotal_shiftInt, Functor.map_comp,
    Category.assoc]
  change (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map (M.frameToTotal F) ≫
      (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map
        (rationalPiAut F Y d π M.lattice.sheaf hπ ^ k).hom ≫
          (inverseImageRationalLatticeIso F f M.lattice.sheaf).hom = _
  erw [inverseImageRationalLatticeIso_zpow]
  rw [← Category.assoc, frameToTotal_pullback, Category.assoc]
  erw [← frameToTotal_shiftInt]

/-- The actual rational frames lift the identity-total lattice comparison for every integer. -/
def inverseImageShiftIntIso :
    (M.shiftInt F hπ k).inverseImage f ≅ (M.inverseImage f).shiftInt F hπ k :=
  isoOfTotalFrame F (M.lattice.inverseImageShiftIso f (k : ZMod d)) (by
    change ((M.shiftInt F hπ k).inverseImage f).frameToTotal F ≫
      (rationalSheafFunctor F X).map ((latticeScalarFunctor d π X).map (𝟙 _)) = _
    rw [frameToTotal_comp_totalId, frameToTotal_inverseImage_shiftInt])

end FramedLatticePiSheaf

variable {S S' : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

namespace GradedPiSheaf

/-- Structural pullback and cyclic translation compare by identity on the actual total module. -/
def pullbackShiftIso {a : Γ(S, ⊤)}
    (M : GradedPiSheaf d S.sheaf (schemeScalar S a)) (f : S' ⟶ S) (k : ZMod d) :
    (M.shift k).pullback f ≅ (M.pullback f).shift k where
  hom := {
    val := 𝟙 _
    homogeneous _U _i _x hx := hx }
  inv := {
    val := 𝟙 _
    homogeneous _U _i _x hx := hx }
  hom_inv_id := Hom.ext (Category.id_comp _)
  inv_hom_id := Hom.ext (Category.id_comp _)

end GradedPiSheaf

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ) (f : S' ⟶ S)

/-- Actual inverse image commutes with rational reframing of the four data. -/
theorem pullback_reframe (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    (D.reframe g).pullback f = (D.pullback f).reframe g := by
  dsimp only [pullback, reframe]
  congr 1
  exact D.eta.inverseImage_reframe f.base g

/-- The identity-total comparisons preserve the actual u map. -/
theorem pullbackShiftInt_u (hπ : algebraMap O F π ≠ 0) (k : ℤ) :
    (latticeScalarFunctor d π (S' : TopCat)).map
        (D.eta.inverseImageShiftIntIso f.base hπ k).hom.lattice.total ≫
          ((D.pullback f).shiftInt hπ k).u =
      ((D.shiftInt hπ k).pullback f).u ≫
        (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).map
          (D.tangent.graded.pullbackShiftIso f (k : ZMod d)).hom.val.val := by
  change (latticeScalarFunctor d π (S' : TopCat)).map (𝟙 _) ≫ _ =
    _ ≫ (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).map (𝟙 _)
  change (latticeScalarFunctor d π (S' : TopCat)).map
      (𝟙 ((D.eta.lattice.inverseImage f.base).sheaf)) ≫ D.pullbackU f =
    D.pullbackU f ≫ (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).map
      (𝟙 ((Scheme.Modules.pullback f).obj D.tangent.graded.module))
  erw [(latticeScalarFunctor d π (S' : TopCat)).map_id,
    (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).map_id]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Integer degree translation commutes with pullback through genuine four-data isomorphisms. -/
def pullbackShiftIntIso (hπ : algebraMap O F π ≠ 0) (k : ℤ) :
    (D.shiftInt hπ k).pullback f ≅ (D.pullback f).shiftInt hπ k :=
  isoOfComponents (D.eta.inverseImageShiftIntIso f.base hπ k)
    (D.tangent.graded.pullbackShiftIso f (k : ZMod d))
    (D.pullbackShiftInt_u f hπ k)

end SheafPreDatum

end Langlands.DeligneFormalSpace

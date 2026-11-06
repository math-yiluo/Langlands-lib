import Langlands.GroupScheme.Absolute.TripleCellProjection
import Langlands.GroupScheme.OpenCellIsomorphism

/-! # An isomorphism from isomorphisms on the three dynamic factors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section General

variable {S : Scheme.{u}} {D G MD ZD UD MG ZG UG : GroupScheme S}

/-- Three-factor multiplication is natural in each of its subgroup sources. -/
theorem tensorHom_comp_tripleCellMultiplication
    (aM : MD ⟶ MG) (aZ : ZD ⟶ ZG) (aU : UD ⟶ UG)
    (iM : MG ⟶ G) (iZ : ZG ⟶ G) (iU : UG ⟶ G) :
    (aM.hom.hom ⊗ₘ (aZ.hom.hom ⊗ₘ aU.hom.hom)) ≫
        tripleCellMultiplication iM iZ iU =
      tripleCellMultiplication (aM ≫ iM) (aZ ≫ iZ) (aU ≫ iU) := by
  simp only [tripleCellMultiplication, SubgroupFunctor.cellMultiplication,
    MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc,
    Grp.comp_hom_hom]

/-- The identity of the ambient group belongs to every three-factor cell. -/
theorem identity_tripleCellMultiplication
    (iM : MD ⟶ D) (iZ : ZD ⟶ D) (iU : UD ⟶ D) :
    lift (1 : 𝟙_ (Over S) ⟶ MD.X)
        (lift (1 : 𝟙_ (Over S) ⟶ ZD.X) (1 : 𝟙_ (Over S) ⟶ UD.X)) ≫
      tripleCellMultiplication iM iZ iU = 1 := by
  simp only [lift_tripleCellMultiplication, MonObj.one_comp, one_mul]

private theorem range_le_of_compatible_factor_iso {M N : GroupScheme S}
    (e : M ≅ N) (i : M ⟶ D) (j : N ⟶ G) (p : D ⟶ G)
    (h : e.hom ≫ j = i ≫ p) : SubgroupFunctor.range j ≤ SubgroupFunctor.range p := by
  rw [← SubgroupFunctor.range_iso_comp e j, h]
  intro T x hx
  obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr
    ⟨a ≫ i.hom.hom, by rw [Grp.comp_hom_hom, Category.assoc]⟩

end General

section Field

variable {k : Type u} [Field k]
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth D.X.hom] [IsAffineHom D.X.hom] [ConnectedSpace D.X.left]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (χD : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D)
    (χG : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {MD ZD UD MG ZG UG : GroupScheme (Spec (CommRingCat.of k))}
    {iMD : MD ⟶ D} {iZD : ZD ⟶ D} {iUD : UD ⟶ D}
    {iMG : MG ⟶ G} {iZG : ZG ⟶ G} {iUG : UG ⟶ G}
    (hMD : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χD)).IsRepresentedBy iMD)
    (hZD : (centralizer χD).IsRepresentedBy iZD)
    (hUD : (unipotent χD).IsRepresentedBy iUD)
    (hMG : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χG)).IsRepresentedBy iMG)
    (hZG : (centralizer χG).IsRepresentedBy iZG)
    (hUG : (unipotent χG).IsRepresentedBy iUG)
    (p : D ⟶ G) (eM : MD ≅ MG) (eZ : ZD ≅ ZG) (eU : UD ≅ UG)
    (hpM : eM.hom ≫ iMG = iMD ≫ p)
    (hpZ : eZ.hom ≫ iZG = iZD ≫ p)
    (hpU : eU.hom ≫ iUG = iUD ≫ p)

/-- A homomorphism of smooth connected affine groups is an isomorphism if it
is an isomorphism on the opposite unipotent, centralizer and unipotent factors. -/
def isoOfTripleCellIsomorphisms : D ≅ G := by
  let forgetGroup : GroupScheme (Spec (CommRingCat.of k)) ⥤
      Over (Spec (CommRingCat.of k)) := Grp.forget₂Mon _ ⋙ Mon.forget _
  let e : MD.X ⊗ (ZD.X ⊗ UD.X) ≅ MG.X ⊗ (ZG.X ⊗ UG.X) :=
    tensorIso (forgetGroup.mapIso eM)
    (tensorIso (forgetGroup.mapIso eZ) (forgetGroup.mapIso eU))
  have hcell : tripleCellMultiplication iMD iZD iUD ≫ p.hom.hom =
      e.hom ≫ tripleCellMultiplication iMG iZG iUG := by
    rw [tripleCellMultiplication_comp_hom, ← hpM, ← hpZ, ← hpU]
    exact (tensorHom_comp_tripleCellMultiplication eM.hom eZ.hom eU.hom iMG iZG iUG).symm
  have : IsOpenImmersion (tripleCellMultiplication iMD iZD iUD).left :=
    isOpenImmersion_tripleCellMultiplication χD hMD hZD hUD
  have : IsOpenImmersion (tripleCellMultiplication iMG iZG iUG).left :=
    isOpenImmersion_tripleCellMultiplication χG hMG hZG hUG
  have : IsIso e.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso e).hom)
  have : IsOpenImmersion e.hom.left := IsOpenImmersion.of_isIso _
  have hcomp : IsOpenImmersion
      (tripleCellMultiplication iMD iZD iUD ≫ p.hom.hom).left := by
    rw [hcell]
    change IsOpenImmersion (e.hom.left ≫ (tripleCellMultiplication iMG iZG iUG).left)
    infer_instance
  have : Mono (tripleCellMultiplication iMD iZD iUD ≫ p.hom.hom) :=
    Over.mono_of_mono_left _
  have hM : unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χG) ≤ SubgroupFunctor.range p := by
    rw [← hMG.2]
    exact range_le_of_compatible_factor_iso eM iMD iMG p hpM
  have hZ : centralizer χG ≤ SubgroupFunctor.range p := by
    rw [← hZG.2]
    exact range_le_of_compatible_factor_iso eZ iZD iZG p hpZ
  have hU : unipotent χG ≤ SubgroupFunctor.range p := by
    rw [← hUG.2]
    exact range_le_of_compatible_factor_iso eU iUD iUG p hpU
  have hgeom := projection_geometry_of_contains_dynamicFactors χG p hM hZ hU
  have : Flat p.hom.hom.left := hgeom.1
  have : Surjective p.hom.hom.left := hgeom.2.1
  have : QuasiCompact p.hom.hom.left := hgeom.2.2.2
  have : GeometricallyIntegral D.X.hom :=
    smoothConnectedAffineGeometry.1 k D inferInstance inferInstance inferInstance
  exact OpenCell.iso p (tripleCellMultiplication iMD iZD iUD)
    (lift (1 : 𝟙_ _ ⟶ MD.X) (lift (1 : 𝟙_ _ ⟶ ZD.X) (1 : 𝟙_ _ ⟶ UD.X)))
    (identity_tripleCellMultiplication iMD iZD iUD)

@[simp]
theorem isoOfTripleCellIsomorphisms_hom :
    (isoOfTripleCellIsomorphisms χD χG hMD hZD hUD hMG hZG hUG
      p eM eZ eU hpM hpZ hpU).hom = p := rfl

end Field

end Langlands.GroupScheme.Dynamic

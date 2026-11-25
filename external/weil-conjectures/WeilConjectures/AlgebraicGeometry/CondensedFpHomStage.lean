/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationMatrices
import all WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus

/-!
# Filtered Hom factorization for finitely presented internal module sheaves

Source: the finite-presentation Hom argument in archived `TwoColimit.lean`.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
open MonObj

section HomStage
variable {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
  (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R]
  {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
  {D : I ⥤ Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R}
  (c : Cocone D) (hc : IsColimit c)

include hc

private lemma regular_hom_stage (a : Mod.regular R ⟶ c.pt) :
    ∃ (i : I) (b : Mod.regular R ⟶ D.obj i), b ≫ c.ι.app i = a := by
  obtain ⟨i, b, hb⟩ := unitHom_stage Y I _ ((Mod.forget R).mapCocone c)
    (isColimitOfPreserves (Mod.forget R) hc) (η[R] ≫ a.hom)
  refine ⟨i, Mod.regularLift (D.obj i) b, Mod.regular_hom_ext ?_⟩
  rw [Mod.comp_hom', ← Category.assoc, Mod.one_comp_regularLift]
  exact hb

private lemma free_hom_stage (n : ℕ) (a : Mod.finiteFree R n ⟶ c.pt) :
    ∃ (i : I) (b : Mod.finiteFree R n ⟶ D.obj i), b ≫ c.ι.app i = a := by
  classical
  choose i b hb using fun j : Fin n ↦ regular_hom_stage R c hc
    (biproduct.ι (fun _ : Fin n ↦ Mod.regular R) j ≫ a)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let t (j : Fin n) : i j ⟶ k :=
    Classical.choice (hk (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  refine ⟨k, biproduct.desc (fun j ↦ b j ≫ D.map (t j)), ?_⟩
  apply biproduct.hom_ext'
  intro j
  rw [biproduct.ι_desc_assoc, Category.assoc, c.w]
  exact hb j

private lemma regular_hom_eventual_eq {i : I}
    (a b : Mod.regular R ⟶ D.obj i)
    (h : a ≫ c.ι.app i = b ≫ c.ι.app i) :
    ∃ (j : I) (t : i ⟶ j), a ≫ D.map t = b ≫ D.map t := by
  let F := D ⋙ Mod.forget R
  let cf := (Mod.forget R).mapCocone c
  let U := Scheme.ProEt.mk (𝟙 Y)
  let : CompactSpace U.left := ‹CompactSpace Y›
  let : QuasiSeparatedSpace U.left := ‹QuasiSeparatedSpace Y›
  have hs : (cf.ι.app i).hom.app (Opposite.op U)
      (unitHomSectionsEquiv Y (D.obj i).X (η[R] ≫ a.hom)) =
    (cf.ι.app i).hom.app (Opposite.op U)
      (unitHomSectionsEquiv Y (D.obj i).X (η[R] ≫ b.hom)) := by
    erw [← unitHomSectionsEquiv_naturality, ← unitHomSectionsEquiv_naturality]
    apply congrArg (unitHomSectionsEquiv Y c.pt.X)
    have hh := congrArg (fun z ↦ η[R] ≫ z.hom) h
    simp only [Mod.comp_hom'] at hh
    exact hh
  obtain ⟨j, t, ht⟩ := AlgebraicGeometry.abelian_eventual_equality F cf
    (isColimitOfPreserves (Mod.forget R) hc) _ _ hs
  refine ⟨j, t, Mod.regular_hom_ext ?_⟩
  apply (unitHomSectionsEquiv Y (D.obj j).X).injective
  simp only [Mod.comp_hom']
  erw [unitHomSectionsEquiv_naturality, unitHomSectionsEquiv_naturality]
  exact ht

private lemma free_hom_eventual_eq (n : ℕ) {i : I}
    (a b : Mod.finiteFree R n ⟶ D.obj i)
    (h : a ≫ c.ι.app i = b ≫ c.ι.app i) :
    ∃ (j : I) (t : i ⟶ j), a ≫ D.map t = b ≫ D.map t := by
  classical
  choose j t ht using fun k : Fin n ↦ regular_hom_eventual_eq R c hc
    (biproduct.ι (fun _ : Fin n ↦ Mod.regular R) k ≫ a)
    (biproduct.ι (fun _ : Fin n ↦ Mod.regular R) k ≫ b)
    (by simpa only [Category.assoc] using congrArg (biproduct.ι _ k ≫ ·) h)
  obtain ⟨j', t', v, hv⟩ := IsFiltered.wideSpan t
  refine ⟨j', t', ?_⟩
  apply biproduct.hom_ext'
  intro k
  rw [← hv k, D.map_comp]
  simpa only [Category.assoc] using congrArg (· ≫ D.map (v k)) (ht k)

/-- A map from a globally finitely presented internal module on a qcqs scheme
factors through a stage of every filtered colimit of internal modules.

Source: the Hom finite-presentation argument in the archived `TwoColimit.lean`;
qcqs section continuity is `proetale_qcqs_fp_section_calculus`.
(auxiliary; not a blueprint node).

Proof: homomorphisms from the regular module are sections of the underlying sheaf
on the terminal pro-etale object. Such sections descend to a filtered stage on a
qcqs scheme, and equality is eventual. The same two assertions hold for a finite
free module by taking a common upper object (and a common wide-span cocone for
the equality witnesses). Present the source as the cokernel of a map of finite
free modules. Descend the map on its generators. Its composite with the relations
vanishes in the colimit, so eventual equality makes it vanish at a later stage.
The cokernel universal property then gives the desired factorization. This also
covers zero generators and relations since a filtered category is nonempty.
-/
theorem condensed_fp_hom_stage (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R)
    (hP : Mod.IsFinitelyPresented R P) (a : P ⟶ c.pt) :
    ∃ (i : I) (b : P ⟶ D.obj i), b ≫ c.ι.app i = a := by
  obtain ⟨n, m, d, ⟨e⟩⟩ := hP
  obtain ⟨i, b, hb⟩ := free_hom_stage R c hc n (cokernel.π d ≫ e.inv ≫ a)
  have hd : (d ≫ b) ≫ c.ι.app i = (0 : Mod.finiteFree R m ⟶ D.obj i) ≫ c.ι.app i := by
    rw [Category.assoc, hb]
    simp
  obtain ⟨j, t, ht⟩ := free_hom_eventual_eq R c hc m (d ≫ b) 0 hd
  have hd' : d ≫ (b ≫ D.map t) = 0 := by
    simpa only [Category.assoc, zero_comp] using ht
  have hb' : (b ≫ D.map t) ≫ c.ι.app j = cokernel.π d ≫ e.inv ≫ a := by
    rw [Category.assoc, c.w, hb]
  refine ⟨j, e.hom ≫ cokernel.desc d (b ≫ D.map t) hd', ?_⟩
  apply (cancel_epi (cokernel.π d ≫ e.inv)).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, cokernel.π_desc_assoc] using hb'

end HomStage

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fintype.EquivFin
import Mathlib.CategoryTheory.Sites.Spaces
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.QuasicoherentSheafHom

/-! # Local finite free presentations of coherent modules -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true in
/-- A coherent source has a finite free cokernel presentation near each point.
Source: Stacks Project, Modules, Lemma 01BW (lemma-coherent-finite-presentation).
(blueprint: lem-weil-pbc-coherent-local-finite-presentation).

Proof:
Finite type gives an open neighbourhood W of x and an epimorphism from a finite
free module to G.over W. Reindex its finite basis by ULift (Fin n). The kernel
is of finite type by the second condition of RingedSpace.IsCoherent. Choose a
smaller neighbourhood V of x and an epimorphism from a free module with basis
ULift (Fin m) to the restriction of this kernel. Restriction to a smaller open
preserves epimorphisms and kernels: stalks are unchanged at points of that open.
Compose this second epimorphism with the restricted kernel inclusion to obtain
a map a between the two finite free modules on V. Its image is the kernel of
the first epimorphism restricted to V, so that epimorphism is a cokernel of a
in the abelian category of module sheaves. Cokernel uniqueness gives the stated
isomorphism. Identify the finite free modules with the finite biproducts of the
restricted unit; the empty basis gives the zero object, so ranks zero are allowed. -/
theorem coherent_local_finite_presentation
    (X : Scheme.{u}) (G : X.Modules)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ (m n : ℕ)
      (a : (⨁ fun _ : Fin m ↦ (SheafOfModules.unit X.ringCatSheaf).over V) ⟶
        (⨁ fun _ : Fin n ↦ (SheafOfModules.unit X.ringCatSheaf).over V)),
      Nonempty ((cokernel a) ≅ G.over V) := by
  -- Finite generators with a finite-type kernel give local finite presentations.
  have hstep
      {C : Type u} [SmallCategory C] [Limits.HasBinaryProducts C]
      {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
      [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
      [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
      (M : SheafOfModules.{u} R) (G : M.GeneratingSections)
      [G.IsFiniteType] [(Limits.kernel G.π).IsFiniteType] :
        M.IsFinitePresentation := by
    classical
    obtain ⟨r, hr⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (Limits.kernel G.π)
    let H (j : r.I) := SheafOfModules.overFunctor R (r.X j)
    have (j : r.I) : Limits.PreservesColimitsOfSize.{u, u} (H j) :=
      inferInstanceAs (Limits.PreservesColimitsOfSize.{u, u}
        (SheafOfModules.pushforward (F := Over.forget (r.X j)) (𝟙 (R.over (r.X j)))))
    let e (j : r.I) := SheafOfModules.mapFreeIso (H j) G.I (Iso.refl _)
    let a₀ (j : r.I) := (r.generators j).π ≫ (H j).map (kernel.ι G.π)
    let b₀ (j : r.I) := (H j).map G.π
    have hab₀ (j : r.I) : a₀ j ≫ b₀ j = 0 := by
      simp only [a₀, b₀, Category.assoc, ← Functor.map_comp, kernel.condition,
        Functor.map_zero, comp_zero]
    have hcol₀ (j : r.I) : IsColimit (CokernelCofork.ofπ (b₀ j) (hab₀ j)) := by
      let c := CokernelCofork.ofπ G.π (kernel.condition G.π)
      have hc : IsColimit c := Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι G.π) (kernel.condition G.π)) (kernelIsKernel _)
      exact isCokernelEpiComp (c.mapIsColimit hc (H j)) (r.generators j).π rfl
    let a (j : r.I) := a₀ j ≫ (e j).inv
    let b (j : r.I) := (e j).hom ≫ b₀ j
    have hab (j : r.I) : a j ≫ b j = 0 := by
      simp only [a, b, Category.assoc, Iso.inv_hom_id_assoc, hab₀]
    have hcol (j : r.I) : IsColimit (CokernelCofork.ofπ (b j) (hab j)) :=
      IsCokernel.ofIso _ (hcol₀ j) _ (Iso.refl _) (e j).symm (Iso.refl _)
        (by simp [a]) (by simp [b])
    let D : M.QuasicoherentData :=
      { I := r.I
        X := r.X
        coversTop := r.coversTop
        presentation j := SheafOfModules.presentationOfIsCokernelFree (a j) (b j)
          (hab j) (hcol j) }
    have : D.IsFinitePresentation := ⟨fun j ↦ by
      have := hr.isFiniteType j
      exact ⟨⟨inferInstanceAs (Finite G.I)⟩,
        ⟨inferInstanceAs (Finite (r.generators j).I)⟩⟩⟩
    exact D.isFinitePresentation
  classical
  -- Cache the slice instances to avoid repeating nested sheafification searches.
  let J := Opens.grothendieckTopology X
  have : HasSheafify J AddCommGrpCat.{u} := inferInstance
  have : J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have (U : X.Opens) : HasSheafify (J.over U) AddCommGrpCat.{u} := inferInstance
  have (U : X.Opens) : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  have (U : X.Opens) (V : Over U) :
      HasSheafify ((J.over U).over V) AddCommGrpCat.{u} := inferInstance
  have (U : X.Opens) (V : Over U) :
      ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have : G.IsFiniteType := hG.1
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData G
  have hfp (i : q.I) : (G.over (q.X i)).IsFinitePresentation := by
    have := hq.isFiniteType i
    let _ := Fintype.ofFinite (q.generators i).I
    let n := Fintype.card (q.generators i).I
    let e := (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over (q.X i))).mapIso
      ((Equiv.ulift.trans (Fintype.equivFin (q.generators i).I).symm).toIso)
    let f := e.hom ≫ (q.generators i).π
    have : Epi f := inferInstanceAs (Epi (e.hom ≫ (q.generators i).π))
    let σ := SheafOfModules.GeneratingSections.ofEpiFree f
    have : σ.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
    have : (kernel σ.π).IsFiniteType := by
      simpa only [σ, SheafOfModules.GeneratingSections.ofEpiFree_π]
        using hG.2 (q.X i) n f
    exact hstep (G.over (q.X i)) σ
  have : G.IsFinitePresentation := by
    exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _
      G q.I q.X q.coversTop hfp
  obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData G
  have hcover := (Opens.coversTop_iff X p.X).mp p.coversTop
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hcover.ge (show x ∈ (⊤ : X.Opens) from trivial))
  let P := p.presentation i
  have : P.IsFinite := hp.isFinite_presentation i
  let _ := Fintype.ofFinite P.generators.I
  let _ := Fintype.ofFinite P.relations.I
  let n := Fintype.card P.generators.I
  let m := Fintype.card P.relations.I
  let η : (SheafOfModules.unit X.ringCatSheaf).over (p.X i) ≅
      SheafOfModules.unit (X.ringCatSheaf.over (p.X i)) := Iso.refl _
  let eg := finiteFreeIso (X.ringCatSheaf.over (p.X i)) _ η P.generators.I
  let er := finiteFreeIso (X.ringCatSheaf.over (p.X i)) _ η P.relations.I
  let a₀ := P.relations.π ≫ kernel.ι P.generators.π
  let a := er.hom ≫ a₀ ≫ eg.inv
  let b := eg.hom ≫ P.generators.π
  have hab : a ≫ b = 0 := by simp [a, b, a₀]
  have hc : IsColimit (CokernelCofork.ofπ b hab) :=
    IsCokernel.ofIso _ P.isColimit _ er.symm eg.symm (Iso.refl _) (by simp [a, a₀])
      (by simp [b])
  refine ⟨p.X i, hxi, m, n, a, ⟨?_⟩⟩
  exact (hc.coconePointUniqueUpToIso (cokernelIsCokernel a)).symm

end AlgebraicGeometry.Scheme.Modules

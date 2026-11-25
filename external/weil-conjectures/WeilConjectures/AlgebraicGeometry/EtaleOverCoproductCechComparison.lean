/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover
import WeilConjectures.AlgebraicGeometry.EtaleOverCoproductPowerCofan

/-! # Čech comparison for a finite coproduct over an étale object
Source: Stacks Project, Tag 03OZ, equation-sheaf-coprod.
(blueprint: new-etale-over-coproduct-cech-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

private theorem cofan_sections_isIso {X : Scheme.{u}} {J : Type (u + 1)} [Finite J]
    (Z : X.Etale) (D : J → X.Etale) (d : ∀ j, D j ⟶ Z)
    (hd : IsColimit (Cofan.mk Z.left (fun j ↦ (d j).left)))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (Pi.lift fun j ↦ G.obj.map (d j).op) := by
  let H := fun j ↦ (D j).left
  let a := fun j ↦ (d j).left
  have : IsIso (Sigma.desc a) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk Z.left a)).mp ⟨hd⟩
  have hopen (j : J) : IsOpenImmersion (a j) := by
    rw [← Sigma.ι_comp_desc a j]
    infer_instance
  have hmono (j : J) : Mono (d j) := by
    have : IsOpenImmersion (d j).left := hopen j
    exact (Etale.forget X ⋙ Over.forget X).mono_of_mono_map
      (by change Mono (d j).left; infer_instance)
  have hcov : Sieve.ofArrows D d ∈ X.smallEtaleTopology Z := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨y, rfl⟩ := (Sigma.desc a).surjective z
    obtain ⟨j, v, hv⟩ := (sigmaOpenCover H).exists_eq y
    change (Sigma.ι H j).base v = y at hv
    obtain rfl := hv.symm
    refine Set.mem_iUnion.mpr ⟨j, v, ?_⟩
    simp [← Scheme.Hom.comp_apply, a, H]
  have hdisj (j k : J) (hjk : j ≠ k) :
      Disjoint (Set.range (d j).left.base) (Set.range (d k).left.base) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨v, hv⟩ ⟨w, hw⟩
    have he : (Sigma.ι H j).base v = (Sigma.ι H k).base w := by
      apply (Sigma.desc a).homeomorph.injective
      simpa [← Scheme.Hom.comp_apply, a, H] using hv.trans hw.symm
    exact hjk (congrArg Sigma.fst ((sigmaι_eq_iff H j k v w).mp he))
  exact Etale.isIso_piLift_of_disjoint G D d hcov hdisj

/-- Replacing a finite family over an étale object by its coproduct preserves the Čech complex.
Source: Stacks Project, Tag 03OZ, equation-sheaf-coprod and its Čech-complex consequence.
(blueprint: new-etale-over-coproduct-cech-comparison)

Proof: the product-cofan theorem transports scheme fibre-product distribution to the
canonical tuple-indexed products in Over U. A scheme coproduct cofan has open, monic,
pairwise disjoint inclusions covering its point; the disjoint-cover sheaf theorem therefore
makes restriction to these tuple summands an isomorphism on sections. Construct the
cosimplicial restriction map from the singleton family to the original family using
Pi.map of the given coprojections. After every product projection, its naturality is
Pi.map_π and functoriality of G, for every simplex map. Applying the alternating-coface
complex functor gives a chain map. In each degree it factors as the singleton-tuple
product projection (an isomorphism by productUniqueIso) followed by the disjoint-cover
restriction isomorphism. Componentwise invertibility gives an isomorphism of complexes;
its inverse has the orientation in the statement. For empty I, the tuple family is empty
in every positive power, so the empty-cover sheaf axiom supplies the same argument.
Neither affineness nor coverage of U is required. Finite large index types are handled
by the existing Small instances without changing the coefficient universe. -/
theorem nonempty_etale_over_coproduct_cech_iso
    (X : Scheme.{u}) (U : X.Etale) (I : Type (u + 1)) [Finite I]
    (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U)
    (W : X.Etale) (g : W ⟶ U) (c : ∀ i : I, V i ⟶ W)
    (hc : IsColimit (Cofan.mk W.left (fun i ↦ (c i).left)))
    (hw : ∀ i : I, c i ≫ g = f i)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
      ((Over.forget U).op ⋙ G.obj)) ≅
      ((cechComplexFunctor fun _ : Fin 1 ↦ Over.mk g).obj
        ((Over.forget U).op ⋙ G.obj))) := by
  let A := FormalCoproduct.mk I (fun i : I ↦ Over.mk (f i))
  let B := FormalCoproduct.mk (Fin 1) (fun _ : Fin 1 ↦ Over.mk g)
  let P := (Over.forget U).op ⋙ G.obj
  let b : (FormalCoproduct.cosimplicialObjectFunctor B.cech).obj P ⟶
      (FormalCoproduct.cosimplicialObjectFunctor A.cech).obj P :=
    { app := fun n ↦ Pi.lift fun t ↦ Pi.π _ (fun _ ↦ 0) ≫
        P.map (Limits.Pi.map (fun r ↦ Over.homMk (c (t r)) (hw (t r)))).op
      naturality := by
        intro n k α
        apply Pi.hom_ext
        intro t
        dsimp [FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
          FormalCoproduct.cech, FormalCoproduct.mapPower]
        simp only [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
        rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
        congr 2
        apply congrArg Quiver.Hom.op
        apply Pi.hom_ext
        intro r
        dsimp [A, B]
        simp only [Function.comp_def, Category.assoc, Pi.map_π, Pi.lift_comp_π,
          Pi.lift_comp_π_assoc] }
  let m := (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).map b
  have h (n : ℕ) : IsIso (m.f n) := by
    let Z : X.Etale := (∏ᶜ fun _ : Fin (n + 1) ↦ Over.mk g).left
    let D : (Fin (n + 1) → I) → X.Etale := fun t ↦
      (∏ᶜ fun r ↦ Over.mk (f (t r))).left
    let d : ∀ t, D t ⟶ Z := fun t ↦
      (Limits.Pi.map (fun r ↦ Over.homMk (c (t r)) (hw (t r)))).left
    obtain ⟨hd⟩ := etale_over_coproduct_power_isColimit X U I V f W g c hc hw n
    have hs : IsIso (Pi.lift fun t ↦ G.obj.map (d t).op) :=
      cofan_sections_isIso Z D d hd G
    let e := productUniqueIso (fun t : Fin (n + 1) → Fin 1 ↦
      P.obj (op (∏ᶜ fun r ↦ B.obj (t r))))
    have he : m.f n = e.hom ≫ (Pi.lift fun t ↦ G.obj.map (d t).op) := by
      change (Pi.lift fun t ↦
        (Pi.π (fun _ : Fin (n + 1) → Fin 1 ↦ G.obj.obj (op Z)) (fun _ ↦ 0)) ≫
          G.obj.map (d t).op) = e.hom ≫ (Pi.lift fun t ↦ G.obj.map (d t).op)
      apply Pi.hom_ext
      intro t
      dsimp [e]
      simp only [Category.assoc, Pi.lift_comp_π]
      rfl
    rw [he]
    exact @IsIso.comp_isIso _ _ _ _ _ e.hom _ e.isIso_hom hs
  have : IsIso m := HomologicalComplex.Hom.isIso_of_components m
  exact ⟨(asIso m).symm⟩

end AlgebraicGeometry.Scheme

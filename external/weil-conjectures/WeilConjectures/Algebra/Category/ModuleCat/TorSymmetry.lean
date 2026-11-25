/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.Algebra.Homology.DoubleComplexCokernelHomologyIso
import WeilConjectures.Algebra.Homology.TensorResolutionColumnCokernelIso
import WeilConjectures.Algebra.Homology.TensorResolutionRowCokernelIso
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Symmetry of Tor for modules over a commutative ring

Source: Stacks Project, Algebra, Lemma Tag 00M3.
(blueprint: lem-weil-pbc-tor-symmetry).
-/

@[expose] public section

universe u

namespace CategoryTheory

private theorem tor_resolution_naturality
    {R : Type u} [CommRing R] (i : ℕ) {M M' N N' : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (P' : ProjectiveResolution M')
    (f : M ⟶ M') (g : N ⟶ N') (a : P.complex ⟶ P'.complex)
    (ha : a.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ f) :
    (((Tor' (ModuleCat R) i).map f).app N ≫ ((Tor' (ModuleCat R) i).obj M').map g) ≫
        (P'.isoLeftDerivedObj (MonoidalCategory.tensorRight N') i).hom =
      (P.isoLeftDerivedObj (MonoidalCategory.tensorRight N) i).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat R) (.down ℕ) i).map
          (ChainComplex.tensorMap a g) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat R) (.down ℕ) i
  have h₁ := ProjectiveResolution.isoLeftDerivedObj_hom_naturality
    f P P' a ha (MonoidalCategory.tensorRight N) i
  have h₂ : ((Tor' (ModuleCat R) i).obj M').map g ≫
      (P'.isoLeftDerivedObj (MonoidalCategory.tensorRight N') i).hom =
      (P'.isoLeftDerivedObj (MonoidalCategory.tensorRight N) i).hom ≫
        H.map ((NatTrans.mapHomologicalComplex
          ((MonoidalCategory.tensoringRight (ModuleCat R)).map g) (.down ℕ)).app P'.complex) := by
    change (NatTrans.leftDerived ((MonoidalCategory.tensoringRight (ModuleCat R)).map g) i).app M' ≫
      (P'.isoLeftDerivedObj (MonoidalCategory.tensorRight N') i).hom = _
    rw [P'.leftDerived_app_eq]
    simp [H]
  rw [Category.assoc, h₂, ← Category.assoc]
  change (((MonoidalCategory.tensorRight N).leftDerived i).map f ≫
    (P'.isoLeftDerivedObj (MonoidalCategory.tensorRight N) i).hom) ≫ _ = _
  rw [h₁, Category.assoc]
  simp only [Functor.comp_map, ChainComplex.tensorMap, Functor.map_comp]
  rfl

/-- Tor computed by resolving its first argument is naturally symmetric in its two arguments.
The components of the natural isomorphism are isomorphisms of `R`-modules.

Source: Stacks Project, Algebra, Lemma Tag 00M3 (lemma-tor-left-right).
(blueprint: lem-weil-pbc-tor-symmetry)

Proof: Form the tensor bicomplex of chosen projective resolutions. Its rows and columns
are exact in positive degrees by flatness of projective modules. Identify the column
cokernel complex with the first resolution tensored with the second module, and identify
the row cokernel complex with the second resolution tensored with the first module
(using tensor commutativity). Compose these identifications on homology with the
natural double-complex comparison and the projective-resolution computations of Tor.
The cokernel identifications and double-complex comparison commute with the tensor
of lifts of module maps. The resolution computation also commutes with these lifts,
so the composite is natural in both arguments. Package these components as a natural
isomorphism of the curried bifunctors. -/
theorem nonempty_tor'_flip_iso (R : Type u) [CommRing R] (i : ℕ) :
    Nonempty (Tor' (ModuleCat.{u} R) i ≅ (Tor' (ModuleCat.{u} R) i).flip) := by
  obtain ⟨col, hcol⟩ := HomologicalComplex₂.tensorResolutionColumnCokernelIso R
  obtain ⟨row, hrow⟩ := HomologicalComplex₂.tensorResolutionRowCokernelIso R
  obtain ⟨θ, hθ⟩ := HomologicalComplex₂.doubleComplexCokernelHomologyIso R
  let E := fun A : HomologicalComplex₂ (ModuleCat.{u} R) (.down ℕ) (.down ℕ) =>
    (∀ (p q : ℕ), 0 < p →
      (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
        (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
          HomologicalComplex.zero_f])).Exact) ∧
    (∀ (p q : ℕ), 0 < q →
      (ShortComplex.mk ((A.X p).d (q + 1) q) ((A.X p).d q (q - 1))
        (by simp)).Exact)
  have ex (M N : ModuleCat.{u} R) (P : ProjectiveResolution M)
      (Q : ProjectiveResolution N) :
      E (((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex) := by
    constructor
    · intro p q hp
      cases p with
      | zero => simp at hp
      | succ p =>
        have : Module.Flat R (Q.complex.X q) := Module.Flat.of_projective
        simpa [  ShortComplex.map] using
          Module.Flat.rTensor_shortComplex_exact (Q.complex.X q) _ (P.exact_succ p)
    · intro p q hq
      cases q with
      | zero => simp at hq
      | succ q =>
        have : Module.Flat R (P.complex.X p) := Module.Flat.of_projective
        simpa [  ShortComplex.map] using
          Module.Flat.lTensor_shortComplex_exact (P.complex.X p) _ (Q.exact_succ q)
  let H := HomologicalComplex.homologyFunctor (ModuleCat R) (.down ℕ) i
  let σ (M N : ModuleCat.{u} R) :=
    let P := projectiveResolution M
    let Q := projectiveResolution N
    P.isoLeftDerivedObj (MonoidalCategory.tensorRight N) i ≪≫
      H.mapIso (col M N P Q).symm ≪≫
        θ (((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex) (ex M N P Q) i ≪≫
          H.mapIso (row M N P Q) ≪≫
            (Q.isoLeftDerivedObj (MonoidalCategory.tensorRight M) i).symm
  have nat (M N M' N' : ModuleCat.{u} R) (f : M ⟶ M') (g : N ⟶ N') :
      (((Tor' (ModuleCat R) i).map f).app N ≫ ((Tor' (ModuleCat R) i).obj M').map g) ≫
          (σ M' N').hom =
        (σ M N).hom ≫
          (((Tor' (ModuleCat R) i).map g).app M ≫ ((Tor' (ModuleCat R) i).obj N').map f) := by
    let P := projectiveResolution M
    let Q := projectiveResolution N
    let P' := projectiveResolution M'
    let Q' := projectiveResolution N'
    let a := ProjectiveResolution.lift f P P'
    let b := ProjectiveResolution.lift g Q Q'
    let Φ := (CategoryTheory.Functor.uncurry.obj
      (CategoryTheory.Functor.mapBifunctorHomologicalComplex
        (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (.down ℕ) (.down ℕ))).map
        (X := (P.complex, Q.complex)) (Y := (P'.complex, Q'.complex)) (a, b)
    let U := HomologicalComplex.opcyclesMap
      ((HomologicalComplex₂.flipFunctor (ModuleCat R) (.down ℕ) (.down ℕ)).map Φ) 0
    let V := HomologicalComplex.opcyclesMap Φ 0
    have ha := ProjectiveResolution.lift_commutes_zero f P P'
    have hb := ProjectiveResolution.lift_commutes_zero g Q Q'
    have hc := congrArg H.map (hcol M N M' N' P Q P' Q' f g a b ha hb)
    have hr := congrArg H.map (hrow M N M' N' P Q P' Q' f g a b ha hb)
    simp only [Functor.map_comp] at hc hr
    have hc' : H.map (ChainComplex.tensorMap a g) ≫ H.map (col M' N' P' Q').inv =
        H.map (col M N P Q).inv ≫ H.map U := by
      have h := congrArg (fun k => H.map (col M N P Q).inv ≫ k ≫
        H.map (col M' N' P' Q').inv) hc
      simpa only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
        Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.assoc, Functor.map_id, Category.id_comp,
        Category.comp_id] using h
    have ht := hθ (((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P.complex).obj Q.complex)
      (((CategoryTheory.Functor.mapBifunctorHomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ)).obj P'.complex).obj Q'.complex)
      (ex M N P Q) (ex M' N' P' Q') Φ i
    change _ ≫ H.map V = H.map U ≫ _ at ht
    have hq : H.map (ChainComplex.tensorMap b f) ≫
        (Q'.isoLeftDerivedObj (MonoidalCategory.tensorRight M') i).inv =
      (Q.isoLeftDerivedObj (MonoidalCategory.tensorRight M) i).inv ≫
        (((Tor' (ModuleCat R) i).map g).app M ≫
          ((Tor' (ModuleCat R) i).obj N').map f) := by
      have h := congrArg (fun k => (Q.isoLeftDerivedObj (MonoidalCategory.tensorRight M) i).inv ≫
        k ≫ (Q'.isoLeftDerivedObj (MonoidalCategory.tensorRight M') i).inv)
        (tor_resolution_naturality i Q Q' g f b hb)
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Iso.inv_hom_id_assoc] using h.symm
    dsimp only [σ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    change _ ≫ ((P'.isoLeftDerivedObj (MonoidalCategory.tensorRight N') i).hom ≫
      H.map (col M' N' P' Q').inv ≫ _ ≫ H.map (row M' N' P' Q').hom ≫
        (Q'.isoLeftDerivedObj (MonoidalCategory.tensorRight M') i).inv) = _
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc]
    rw [tor_resolution_naturality i P P' f g a ha]
    simp only [Category.assoc]
    rw [← Category.assoc (H.map (ChainComplex.tensorMap a g)), hc']
    simp only [Category.assoc]
    rw [← Category.assoc (H.map U), ← ht]
    simp only [Category.assoc]
    rw [← Category.assoc (H.map V), ← hr]
    simp only [Category.assoc]
    rw [hq]
  refine ⟨NatIso.ofComponents (fun M => NatIso.ofComponents (fun N => σ M N) ?_) ?_⟩
  · intro N N' g
    change ((Tor' (ModuleCat R) i).obj M).map g ≫ (σ M N').hom =
      (σ M N).hom ≫ ((Tor' (ModuleCat R) i).map g).app M
    have h := nat M N M N' (𝟙 M) g
    simp only [Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id] at h
    exact h
  · intro M M' f
    apply NatTrans.ext
    funext N
    change ((Tor' (ModuleCat R) i).map f).app N ≫ (σ M' N).hom =
      (σ M N).hom ≫ ((Tor' (ModuleCat R) i).obj N).map f
    have h := nat M N M' N f (𝟙 N)
    simp only [Functor.map_id, NatTrans.id_app, Category.comp_id] at h
    exact h

end CategoryTheory

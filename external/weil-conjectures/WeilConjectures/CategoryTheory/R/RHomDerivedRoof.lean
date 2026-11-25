/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.KInjectiveBridge
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

import WeilConjectures.CategoryTheory.R.RHomNaturalCocycleMap
import WeilConjectures.CategoryTheory.R.RHomInjectiveCocycleBijective

/-!
# The natural RHom comparison and its roof normalization

Source: Stacks Tags 06XR and 070I (blueprint: lem-sc-p1-rhom-hom-derived-roof).
-/

@[expose] public section

universe w w₂ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

/-- The natural RHom comparison with its cocycle roof formula, before shift compatibility.
Source: Stacks Project, Tags 06XR (part 1) and 070I
(blueprint: lem-sc-p1-rhom-hom-derived-roof).

Proof: represent a bounded below derived object by a bounded below complex of injectives.
Cocycles from M to its degree n terms are degree n Hom-complex cocycles from M[0].
The boundary subgroup consists precisely of null-homotopic maps, so taking the quotient
identifies H^n(Hom(M,I)) with homotopy-category maps M[0] to I[n]. Bounded below
injective complexes and their shifts are K-injective. The K-injective localization
bijection identifies these maps with derived-category maps. Postcompose with the inverse
of the resolution map to obtain the stated roof. All operations preserve addition.
The derived unit on an injective complex is invertible and identifies the source with
H^n(RHom(M,Q(I))). Extend the comparison along a representing isomorphism to every
object of D+. For a derived morphism between two such objects, the K-injective
localization bijection gives a lift between resolutions, unique up to homotopy.
Applying Hom(M,-) to the lift and passing to cohomology yields naturality, since the
lift commutes with the resolution maps in the derived category. Taking the identity
morphism with two resolutions proves independence of the resolution and hence the
formula for every r, not only the resolution used to construct the comparison. -/
theorem exists_rhom_hom_derived_roof
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w₂} AddCommGrpCat.{v}] (M : C) :
    let V := preadditiveCoyoneda.obj (op M)
    let RV := V.rightDerivedFunctorPlus
    let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
    let S := (DerivedCategory.singleFunctor C 0).obj M
    ∃ ψ : ∀ (X : DerivedCategory.Plus C) (n : ℤ),
        (H n).obj (RV.obj X) ≃+ (S ⟶ X.obj⟦n⟧),
      (∀ (X Y : DerivedCategory.Plus C) (g : X ⟶ Y) (n : ℤ)
          (a : (H n).obj (RV.obj X)),
        ψ Y n ((H n).map (RV.map g) a) =
          ψ X n a ≫ ((DerivedCategory.Plus.ι (C := C)).map g)⟦n⟧') ∧
      (∀ (K : CochainComplex.Plus C) (r : CochainComplex.KInjectiveResolutionChoice K.obj)
          (hb : CochainComplex.plus C r.complex)
          (_hi : ∀ k : ℤ, Injective (r.complex.X k)) (n : ℤ)
          (f : M ⟶ r.complex.X n) (hf : f ≫ r.complex.d n (n + 1) = 0),
        let I : CochainComplex.Plus C := ⟨r.complex, hb⟩
        letI := r.quasiIso
        let e : (DerivedCategory.Plus.Q (C := C)).obj K ≅
            (DerivedCategory.Plus.Q (C := C)).obj I :=
          (DerivedCategory.Plus.ι (C := C)).preimageIso
            ((DerivedCategory.Plus.QCompιIso C).app K ≪≫
              asIso (DerivedCategory.Q.map r.map) ≪≫
              (DerivedCategory.Plus.QCompιIso C).symm.app I)
        let J := V.rightDerivedComplexWithResolution K r
        let a := J.homologyπ n ((J.sc n).abCyclesIso.inv
          ⟨f, by
            change f ≫ r.complex.d n ((ComplexShape.up ℤ).next n) = 0
            rw [CochainComplex.next]
            exact hf⟩)
        let b := (DerivedCategory.Plus.homologyFunctorObjQIso
          (V.mapCochainComplexPlus.obj I) n).inv a
        let η := V.rightDerivedFunctorPlusUnit.app I
        ψ ((DerivedCategory.Plus.Q (C := C)).obj K) n
            ((H n).map (RV.map e.inv)
              ((H n).map η b)) =
          ShiftedHom.map (Cocycle.equivHomShift.symm
              (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)) DerivedCategory.Q ≫
            (CategoryTheory.inv (DerivedCategory.Q.map r.map))⟦n⟧' ≫
            ((DerivedCategory.Plus.QCompιIso C).inv.app K)⟦n⟧') := by
  classical
  dsimp only
  let V := preadditiveCoyoneda.obj (op M)
  let RV := V.rightDerivedFunctorPlus
  let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
  let S := (DerivedCategory.singleFunctor C 0).obj M
  obtain ⟨τ, hnat, hnorm⟩ := exists_rhom_natural_cocycle_map M
  have hbij (X : DerivedCategory.Plus C) (n : ℤ) : Function.Bijective (τ X n) := by
    obtain ⟨m, hm⟩ := X.2
    have : X.IsGE m := (X.isGE_ι_obj_iff m).1 hm
    obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso X m
    let I := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
    have hi (k : ℤ) : Injective (I.obj.X k) := (L.obj.X k).2
    have hb := rhom_injective_cocycle_map_bijective M I hi n
      (τ ((DerivedCategory.Plus.Q (C := C)).obj I) n) (hnorm I hi n)
    let B := ((DerivedCategory.Plus.ι (C := C)).mapIso e)
    constructor
    · intro a b hab
      have h := congrArg (fun x ↦ x ≫ B.inv⟦n⟧') hab
      have ha := hnat _ _ e.inv n a
      have hc := hnat _ _ e.inv n b
      have heq : (H n).map (RV.map e.inv) a = (H n).map (RV.map e.inv) b := by
        apply hb.1
        exact ha.trans (h.trans hc.symm)
      have := congrArg (fun x ↦ (H n).map (RV.map e.hom) x) heq
      simpa [← AddCommGrpCat.comp_apply, ← Functor.map_comp] using this
    · intro b
      obtain ⟨a, ha⟩ := hb.2 (b ≫ B.inv⟦n⟧')
      refine ⟨(H n).map (RV.map e.hom) a, ?_⟩
      rw [hnat, ha]
      simp [B, ← Functor.map_comp]
  let ψ (X : DerivedCategory.Plus C) (n : ℤ) := AddEquiv.ofBijective (τ X n) (hbij X n)
  refine ⟨ψ, ?_, ?_⟩
  · exact hnat
  · intro K r hb hi n f hf
    let I : CochainComplex.Plus C := ⟨r.complex, hb⟩
    let := r.quasiIso
    let e : (DerivedCategory.Plus.Q (C := C)).obj K ≅
        (DerivedCategory.Plus.Q (C := C)).obj I :=
      (DerivedCategory.Plus.ι (C := C)).preimageIso
        ((DerivedCategory.Plus.QCompιIso C).app K ≪≫
          asIso (DerivedCategory.Q.map r.map) ≪≫
          (DerivedCategory.Plus.QCompιIso C).symm.app I)
    change τ _ n ((H n).map (RV.map e.inv) _) = _
    rw [hnat]
    erw [hnorm I hi n f hf]
    have he : (DerivedCategory.Plus.ι (C := C)).map e.inv =
        (DerivedCategory.Plus.QCompιIso C).hom.app I ≫
          CategoryTheory.inv (DerivedCategory.Q.map r.map) ≫
          (DerivedCategory.Plus.QCompιIso C).inv.app K := by
      change (DerivedCategory.Plus.ι (C := C)).map
        ((DerivedCategory.Plus.ι (C := C)).preimage _) = _
      rw [Functor.map_preimage]
      simp only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, asIso_inv, Category.assoc]
    rw [he]
    simp only [Functor.map_comp, Category.assoc]
    simp only [I, ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Functor

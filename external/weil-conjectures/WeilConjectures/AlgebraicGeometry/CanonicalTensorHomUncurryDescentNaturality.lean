/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Naturality forced by componentwise uncurrying

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-descent-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

private theorem derived_arrow_rep
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {A B : DerivedCategory C} (a : A ⟶ B) :
    ∃ (P Q : CochainComplex C ℤ) (g : P ⟶ Q)
      (eP : DerivedCategory.Q.obj P ≅ A) (eQ : DerivedCategory.Q.obj Q ≅ B),
      eP.hom ≫ a = DerivedCategory.Q.map g ≫ eQ.hom := by
  let P := (DerivedCategory.Q (C := C)).objPreimage A
  let Q := (DerivedCategory.Q (C := C)).objPreimage B
  let eP := (DerivedCategory.Q (C := C)).objObjPreimageIso A
  let eQ := (DerivedCategory.Q (C := C)).objObjPreimageIso B
  obtain ⟨R, s, hs, g, hg⟩ := DerivedCategory.right_fac (eP.hom ≫ a ≫ eQ.inv)
  let := hs
  refine ⟨R, Q, g, asIso (DerivedCategory.Q.map s) ≪≫ eP, eQ, ?_⟩
  have h := congrArg (fun f ↦ DerivedCategory.Q.map s ≫ f ≫ eQ.hom) hg
  simpa [Category.assoc] using h

private theorem naturality_transport
    {D : Type*} [Category D] [MonoidalCategory D]
    (H : Dᵒᵖ × D ⥤ D)
    (t : ∀ K L M : D, (K ⟶ H.obj (op L, M)) → (K ⊗ L ⟶ M))
    (hi : ∀ (K K' L L' M M' : D) (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ H.obj (op L, M)),
      t K' L' M' (a.hom ≫ f ≫ H.map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ t K L M f ≫ c.hom)
    {K K' L L' M M' P P' N N' I I' : D}
    (eK : P ≅ K) (eK' : P' ≅ K') (eL : N ≅ L) (eL' : N' ≅ L')
    (eM : I ≅ M) (eM' : I' ≅ M')
    (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
    (a₀ : P' ⟶ P) (b₀ : N' ⟶ N) (c₀ : I ⟶ I')
    (ha : eK'.hom ≫ a = a₀ ≫ eK.hom)
    (hb : eL'.hom ≫ b = b₀ ≫ eL.hom)
    (hc : eM.hom ≫ c = c₀ ≫ eM'.hom)
    (hn : ∀ f : P ⟶ H.obj (op N, I),
      t P' N' I' (a₀ ≫ f ≫ H.map (X := (op N, I)) (Y := (op N', I')) (b₀.op, c₀)) =
        (a₀ ⊗ₘ b₀) ≫ t P N I f ≫ c₀)
    (f : K ⟶ H.obj (op L, M)) :
    t K' L' M' (a ≫ f ≫ H.map (b.op, c)) =
      (a ⊗ₘ b) ≫ t K L M f ≫ c := by
  have hc' : c ≫ eM'.inv = eM.inv ≫ c₀ := by
    have h := congrArg (fun g ↦ eM.inv ≫ g ≫ eM'.inv) hc
    simpa [Category.assoc] using h
  have hm :
      H.map (X := (op L, M)) (Y := (op L', M')) (b.op, c) ≫
        H.map (X := (op L', M')) (Y := (op N', I')) (eL'.hom.op, eM'.inv) =
      H.map (X := (op L, M)) (Y := (op N, I)) (eL.hom.op, eM.inv) ≫
        H.map (X := (op N, I)) (Y := (op N', I')) (b₀.op, c₀) := by
    rw [← H.map_comp, ← H.map_comp]
    congr 1
    ext
    · exact hb
    · exact hc'
  have hinput : eK'.hom ≫ (a ≫ f ≫ H.map (X := (op L, M)) (Y := (op L', M')) (b.op, c)) ≫
      H.map (X := (op L', M')) (Y := (op N', I')) (eL'.hom.op, eM'.inv) =
      a₀ ≫ (eK.hom ≫ f ≫
        H.map (X := (op L, M)) (Y := (op N, I)) (eL.hom.op, eM.inv)) ≫
          H.map (X := (op N, I)) (Y := (op N', I')) (b₀.op, c₀) := by
    simp only [Category.assoc]
    rw [← Category.assoc eK'.hom a, ha]
    simp only [Category.assoc]
    rw [hm]
  have h := hn (eK.hom ≫ f ≫
    H.map (X := (op L, M)) (Y := (op N, I)) (eL.hom.op, eM.inv))
  have ht := hi K' P' L' N' M' I' eK' eL' eM'.symm (a ≫ f ≫ H.map (b.op, c))
  have hs := hi K P L N M I eK eL eM.symm f
  dsimp only [Iso.symm_hom] at ht hs
  simp only [Category.assoc] at hinput h ht hs
  rw [← hinput, ht, hs] at h
  have hab : (a₀ ⊗ₘ b₀) ≫ (eK.hom ⊗ₘ eL.hom) =
      (eK'.hom ⊗ₘ eL'.hom) ≫ (a ⊗ₘ b) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ha, hb]
  simp only [Category.assoc] at h
  rw [← Category.assoc (a₀ ⊗ₘ b₀), hab] at h
  apply (cancel_epi (eK'.hom ⊗ₘ eL'.hom)).mp
  apply (cancel_mono eM'.inv).mp
  simpa only [Category.assoc, hc'] using h

/-- The representative localization equation forces three-variable naturality.
Assume also transport along isomorphisms; this is essential when the chosen
derived category has objects which are not literally images of complexes.
No existence of a family, or existence of chain representatives, is asserted here.
Source: Stacks Project, cohomology.tex, Tag 08DJ, naturality of evaluation;
sites-cohomology.tex, Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-descent-naturality).

Proof: Choose K-flat representatives for the four source objects K,K',L,L',
and the functorial K-injective models for M and M'. Represent maps between them
by roofs, using common K-flat resolutions for source denominators. Maps to a
K-injective complex are actual chain maps modulo homotopy. On these models,
restrict the two uncurried chain maps to every total tensor summand. Naturality
of the sheaf tensor-Hom adjunction and of the Hom product projections identifies
both sides with evaluation after precomposition in P and L and postcomposition
in I(M). The coproduct universal property proves equality of the chain maps.
Apply Q and the assumed representative equation to these chain maps. Naturality
of Q's lax tensor map, of the derived Hom localization factorization, and of the
functorial resolution map gives the claimed equality on representatives.
Use the assumed isomorphism transport to cancel the localized quasi-isomorphisms
in the roofs and the representative isomorphisms to obtain the equation for
arbitrary derived maps a,b,c. Homotopy invariance ensures that none of the roof
choices affects the calculation. The identity and zero-map cases obey the same
component equation, without boundedness assumptions. -/
theorem tensorHomUncurry_descent_natural (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M))
    (ht : ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlatTensor →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M)
    (hi : letI := schemeDerivedTensorMonoidal X
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      t K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ t K L M f ≫ c.hom) :
    letI := schemeDerivedTensorMonoidal X
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      t K' L' M' (a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.op, c)) =
        (a ⊗ₘ b) ≫ t K L M f ≫ c := by
  let := schemeDerivedTensorMonoidal X
  have hn := tensorHomUncurry_chain_natural X t ht hi
  intro K K' L L' M M' a b c f
  obtain ⟨P', P, a₀, eK', eK, ha⟩ := derived_arrow_rep a
  obtain ⟨N', N, b₀, eL', eL, hb⟩ := derived_arrow_rep b
  obtain ⟨I, I', c₀, eM, eM', hc⟩ := derived_arrow_rep c
  exact naturality_transport
    (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf) t hi eK eK' eL eL' eM eM'
    a b c (DerivedCategory.Q.map a₀) (DerivedCategory.Q.map b₀) (DerivedCategory.Q.map c₀)
    ha hb hc (hn P P' N N' I I' a₀ b₀ c₀) f

end AlgebraicGeometry

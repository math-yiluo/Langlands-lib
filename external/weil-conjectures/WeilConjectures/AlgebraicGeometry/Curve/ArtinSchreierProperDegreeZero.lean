/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.ArtinSchreier
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

/-! # Degree-zero Artin–Schreier surjectivity on proper curves

Source: blueprint sec-proper-base-change/sk-thm-p1/lem-sc-c5,
Artin–Schreier branch; Stacks Project Tag 0A3P.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- On a smooth proper connected curve, Frobenius minus identity is onto in
 degree-zero additive cohomology.
 Source: blueprint `proposition-p-torsion-smooth-proper-curve--4`, characteristic-p branch, and
 `proposition-p-torsion-smooth-proper-curve--4`, paragraph 2; Stacks Project Tag 0A3P.
 (blueprint: lem-sc-artin-schreier-proper-degree-zero)

 Proof: The natural section identifications a identify G with the additive structure
 sheaf. The degree-zero comparison with global sections is natural in wp, so wp induces
 x ↦ x^p-x on Γ(C,O_C). Smoothness implies reducedness; properness, connectedness and
 algebraic closedness identify the global section ring with k via its structural map.
 This map commutes with powers and subtraction. Every a in k has a root of T^p-T-a
 because k is algebraically closed. Transport this surjectivity through the global
 section identification and the degree-zero comparison; surjectivity of a homomorphism
 of additive groups is epimorphy. No assumption about higher cohomology is used. 
(blueprint: lemma-weil-pbc-smooth-curve-artin-schreier-proper-degree-zero)
-/
theorem epi_etaleCohomology_artinSchreier_zero_of_isProper
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (wp : G ⟶ G)
    (_ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hwp : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x) :
    Epi ((Etale.cohomology AddCommGrpCat.{u + 1} C (0 : ℤ)).map
      ((DerivedCategory.singleFunctor
        (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).map wp)) := by
  classical
  have : ConnectedSpace C := IsConnectedCurve.connectedSpace (f := f)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IsReduced C := isReduced_of_isReduced_stalk C
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : IsProper (C ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  let ρ : k →+* Γ(C, ⊤) := Scheme.globalSectionsRingHom k
  have hρ : Function.Surjective ρ :=
    Scheme.GlobalSectionsBijective.bijective_globalSectionsRingHom.surjective
  have hs : Function.Surjective (fun x : Γ(C, ⊤) ↦ x ^ p - x) := by
    intro y
    obtain ⟨c, rfl⟩ := hρ y
    obtain ⟨d, hd⟩ := (IsAlgClosed.artinSchreier_surjective_and_kernel (k := k) p).1 c
    refine ⟨ρ d, ?_⟩
    change ρ d ^ p - ρ d = ρ c
    change d ^ p - d = c at hd
    rw [← map_pow, ← map_sub, hd]
  let U : C.Etaleᵒᵖ := .op (Scheme.Etale.mk (𝟙 C))
  have hw : Function.Surjective (wp.hom.app U) := by
    intro y
    obtain ⟨x, hx⟩ := hs (a U y)
    refine ⟨(a U).symm x, (a U).injective ?_⟩
    rw [hwp, AddEquiv.apply_symm_apply]
    exact hx
  have ht : IsTerminal (Scheme.Etale.mk (𝟙 C)) :=
    MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale C
  have hH : Function.Surjective (Sheaf.H.map wp 0) := by
    intro y
    obtain ⟨x, hx⟩ := hw (Sheaf.H.equiv₀ G ht y)
    refine ⟨(Sheaf.H.equiv₀ G ht).symm x, (Sheaf.H.equiv₀ G ht).injective ?_⟩
    rw [← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply]
    exact hx
  obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso C 0
  let E := (e.app G).addCommGroupIsoToAddEquiv
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨x, hx⟩ := hH (E.symm y)
  refine ⟨E x, ?_⟩
  have hn := ConcreteCategory.congr_hom (e.hom.naturality wp) x
  change E (Sheaf.H.map wp 0 x) = _ at hn
  rw [hx, AddEquiv.apply_symm_apply] at hn
  exact hn.symm

end AlgebraicGeometry

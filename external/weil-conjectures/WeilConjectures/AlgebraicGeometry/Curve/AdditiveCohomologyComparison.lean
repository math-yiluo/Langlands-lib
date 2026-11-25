/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.EtaleTensorUnitSectionsNatural
import WeilConjectures.AlgebraicGeometry.EtaleQcoherentSourceComparisonNatural

/-! # Scalar-compatible comparison for additive first cohomology -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry




private theorem exists_chain_equiv
    {A B C D E F : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]
    (a : A ≃+ B) (b : B ≃+ C) (c : C ≃+ D) (d : D ≃+ E) (e : E ≃+ F) :
    ∃ t : A ≃+ F, ∀ (fA : A → A) (fB : B → B) (fC : C → C)
      (fD : D → D) (fE : E → E) (fF : F → F),
      (∀ x, a (fA x) = fB (a x)) → (∀ x, b (fB x) = fC (b x)) →
      (∀ x, c (fC x) = fD (c x)) → (∀ x, d (fD x) = fE (d x)) →
      (∀ x, e (fE x) = fF (e x)) → ∀ x, t (fA x) = fF (t x) := by
  refine ⟨((((a.trans b).trans c).trans d).trans e), ?_⟩
  intro fA fB fC fD fE fF ha hb hc hd he x
  change e (d (c (b (a (fA x))))) = fF (e (d (c (b (a x)))))
  rw [ha, hb, hc, hd, he]

private theorem exists_iso_of_sections {C : Scheme.{u}}
    (G H : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (d : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ H.obj.obj U)
    (hd : ∀ {U V : C.Etaleᵒᵖ} (g : U ⟶ V) (x : G.obj.obj U),
      d V (G.obj.map g x) = H.obj.map g (d U x)) :
    ∃ i : G ≅ H, ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U), i.hom.hom.app U x = d U x := by
  let p : G.obj ≅ H.obj := NatIso.ofComponents
    (fun U ↦ (d U).toAddCommGrpIso) (fun g ↦ by ext x; exact hd g x)
  exact ⟨ObjectProperty.isoMk _ p, fun _ _ ↦ rfl⟩

private theorem exists_iso_of_section_coordinates {C : Scheme.{u}}
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (E : Sheaf C.smallEtaleTopology AddCommGrpCat.{u})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (b : ∀ U : C.Etaleᵒᵖ, E.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hb : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : E.obj.obj U),
      b V (E.obj.map g x) = g.unop.left.appTop (b U x)) :
    let L := sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
    ∃ i : G ≅ L.obj E, ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      i.hom.hom.app U x = ULift.up ((b U).symm (a U x)) := by
  let L := sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
  let d : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ (L.obj E).obj.obj U :=
    fun U ↦ ((a U).trans (b U).symm).trans AddEquiv.ulift.symm
  exact exists_iso_of_sections G (L.obj E) d (by
    intro U V g x
    apply ULift.ext
    apply (b V).injective
    change b V ((b V).symm (a V (G.obj.map g x))) =
      b V (E.obj.map g ((b U).symm (a U x)))
    rw [hb, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ha])

private theorem section_coordinates_intertwine {C : Scheme.{u}}
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (E : Sheaf C.smallEtaleTopology AddCommGrpCat.{u})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (b : ∀ U : C.Etaleᵒᵖ, E.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (i : G ≅ (sheafCompose C.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).obj E)
    (hi : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      i.hom.hom.app U x = ULift.up ((b U).symm (a U x)))
    (μ : G ⟶ G) (θ : E ⟶ E) (r : ∀ U : C.Etaleᵒᵖ, Γ(U.unop.left, ⊤))
    (hμ : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (μ.hom.app U x) = a U x * r U)
    (hθ : ∀ (U : C.Etaleᵒᵖ) (x : E.obj.obj U),
      b U (θ.hom.app U x) = b U x * r U) :
    μ ≫ i.hom = i.hom ≫ (sheafCompose C.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).map θ := by
  ext U y
  change i.hom.hom.app U (μ.hom.app U y) =
    ((sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map θ).hom.app U
      (i.hom.hom.app U y)
  rw [hi, hi]
  apply ULift.ext
  apply (b U).injective
  change b U ((b U).symm (a U (μ.hom.app U y))) =
    b U (θ.hom.app U ((b U).symm (a U y)))
  rw [AddEquiv.apply_symm_apply, hθ, AddEquiv.apply_symm_apply, hμ]

private theorem map_smulHom_field
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    (M : C.Modules) (c : k) (x : Scheme.Modules.H M 1) :
    letI : C.Over (Spec (.of k)) := ⟨f⟩
    Scheme.Modules.H.map (M.smulHom (Scheme.globalSectionsRingHom k c)) 1 x =
      c • x := by
  rfl

/-- Compare the larger-coefficient derived additive cohomology with ordinary
structure-sheaf cohomology, including its canonical scalar maps.
Source: Stacks Project, Tags 03P2 and 03FD; the coefficient-universe argument
is the separated-case finite affine open cover argument of Tag 03P2,
applied in each coefficient universe.
(blueprint: lem-sc-additive-cohomology-scalar-comparison)

Proof: Identify G sectionwise with the universe lift of the associated etale
sheaf of the unit O_C-module. The unit tensor-pullback identifications turn a
into this sheaf isomorphism; ha is precisely its naturality. Apply the natural
Ext/derived comparison to the sheaf in degree zero. C is quasi-compact and
separated: IsCurve f supplies quasi-compactness and separatedness over Spec k,
and the latter is separated over the terminal scheme. Choose a finite affine
open cover of C. All finite intersections are affine. Both the associated
etale sheaf and its coefficient lift are acyclic on these intersections by
affine quasi-coherent acyclicity in their respective coefficient universes.
Thus the Cech-to-cohomology spectral sequence has only its degree-zero row
and identifies each degree-one group with the Cech complex's first homology.
In every degree the cover tuples form a finite set. Lowering the finitely
many lifted components identifies the two cochain groups and commutes with
restrictions and alternating sums. It identifies kernels and images, hence
induces an additive equivalence of first cohomology. These comparisons are
natural in module endomorphisms: their maps act componentwise on this same
cover and commute with the differentials. No preservation of injective
objects by ULift is used. Compose with the natural etale/Zariski comparison
and the natural module/underlying-abelian comparison. Reindex Ext universes
through their Hom-in-the-derived-category descriptions, naturally in both
arguments. The result is e with codomain the source library's ordinary H^1.
For each c, the section formula identifies mu uniquely with multiplication
by the global section f^*(c). Pullback of the unit module identifies this
map on an etale object with multiplication by its pulled-back section.
The comparisons above therefore intertwine these maps. By the definition
of moduleH and moduleHOfField, the map on ordinary H^1 is precisely c-smul.
This gives the stated identity, without properness, smoothness or finiteness. -/
theorem exists_addEquiv_etaleCohomology_one_structureSheaf
    {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x)) :
    letI : C.Over (Spec (.of k)) := ⟨f⟩
    let T := DerivedCategory.singleFunctor
      (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)
    ∃ e : T.obj G ≃+ Scheme.Modules.H (X := C) (SheafOfModules.unit C.ringCatSheaf) 1,
      ∀ (c : k) (μ : G ⟶ G),
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) →
        ∀ x : T.obj G, e (T.map μ x) = c • e x := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  let : C.IsSeparated := by
    constructor
    rw [← terminal.comp_from f]
    infer_instance
  let M : C.Modules := SheafOfModules.unit C.ringCatSheaf
  let : M.IsQuasicoherent := SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf)
  let E := Scheme.Modules.etaleTensorSectionsSheaf
    (SheafOfModules.unit C.ringCatSheaf)
  let L := sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
  let T := DerivedCategory.singleFunctor
    (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)
  obtain ⟨b, hb, hbs⟩ := Scheme.Modules.exists_etaleTensorUnit_sections_natural C
  obtain ⟨i, hiapp⟩ := exists_iso_of_section_coordinates G
    (Scheme.Modules.etaleTensorSectionsSheaf (SheafOfModules.unit C.ringCatSheaf))
    a b ha hb
  obtain ⟨j⟩ := Scheme.nonempty_sheafH_extDerivedIso C 1
  obtain ⟨m, hm, cH, hcH⟩ :=
    Scheme.Modules.exists_etaleTensorSectionsSheaf_source_comparison_natural C M 1
  let e₀ : T.obj G ≃+ Sheaf.H G 1 :=
    (j.app G).symm.addCommGroupIsoToAddEquiv
  let e₁ : Sheaf.H G 1 ≃+ Sheaf.H (L.obj E) 1 :=
    ((Sheaf.functorH.{u + 1} C.smallEtaleTopology 1).mapIso i).addCommGroupIsoToAddEquiv
  obtain ⟨e, he⟩ := exists_chain_equiv e₀ e₁ cH (AddEquiv.refl _) (AddEquiv.refl _)
  refine ⟨e, ?_⟩
  intro c μ hμ x
  let r : Γ(C, ⊤) := Scheme.globalSectionsRingHom k c
  let φ : M ⟶ M := M.smulHom r
  let θ : E ⟶ E := m φ
  have hi := section_coordinates_intertwine G E a b i hiapp μ θ
    (fun U ↦ (show Γ(U.unop.left, ⊤) from U.unop.hom.appTop r))
    (fun U y ↦ hμ U y) (hbs r θ (hm φ))
  have he₀ (y : T.obj G) : e₀ (T.map μ y) = Sheaf.H.map μ 1 (e₀ y) := by
    exact congrArg (fun t ↦ t y) (j.inv.naturality μ)
  have he₁ (y : Sheaf.H G 1) :
      e₁ (Sheaf.H.map μ 1 y) = Sheaf.H.map (L.map θ) 1 (e₁ y) := by
    change Sheaf.H.map i.hom 1 (Sheaf.H.map μ 1 y) =
      Sheaf.H.map (L.map θ) 1 (Sheaf.H.map i.hom 1 y)
    rw [← Sheaf.H.map_comp_apply, hi, Sheaf.H.map_comp_apply]
  have h := he (T.map μ) (Sheaf.H.map μ 1) (Sheaf.H.map (L.map θ) 1)
    (Scheme.Modules.H.map φ 1) (Scheme.Modules.H.map φ 1)
    (Scheme.Modules.H.map φ 1) he₀ he₁ (hcH φ) (fun _ ↦ rfl) (fun _ ↦ rfl) x
  exact h.trans (map_smulHom_field f M c (e x))

end AlgebraicGeometry

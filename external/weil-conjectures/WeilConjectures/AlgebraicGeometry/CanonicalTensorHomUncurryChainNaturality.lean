/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex

/-! # Naturality on localized chain maps

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-chain-naturality).
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

private theorem hom_model_natural (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L L' M M' : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (b : L' ⟶ L) (c : M ⟶ M') :
    DerivedCategory.Q.map
      ((Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map
        (X := (op L, (schemeHomKInjectiveResolution X).obj M))
        (Y := (op L', (schemeHomKInjectiveResolution X).obj M'))
        (b.op, (schemeHomKInjectiveResolution X).map c)) ≫
      (schemeDerivedInternalHomResolutionIso X L' M').inv =
    (schemeDerivedInternalHomResolutionIso X L M).inv ≫
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).map ((DerivedCategory.Q.map b).op, DerivedCategory.Q.map c) := by
  have : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  let e := Localization.fac
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := X.sheaf)) ⋙ DerivedCategory.Q)
    (derivedInternalHom_inverts (Opens.grothendieckTopology X) X.sheaf
      (CochainComplex.kInjectiveResolutionFunctor.{u}
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
      (CochainComplex.toKInjectiveResolution.{u} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)
  exact e.inv.naturality (X := (op L, M)) (Y := (op L', M')) (b.op, c)

private theorem chain_lift
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P I : CochainComplex C ℤ) [I.IsKInjective]
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) :
    ∃ φ : P ⟶ I, DerivedCategory.Q.map φ = f := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj P) I).surjective
      ((DerivedCategory.quotientCompQhIso C).hom.app P ≫ f ≫
        (DerivedCategory.quotientCompQhIso C).inv.app I)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨φ, ?_⟩
  have h := congrArg (fun k ↦ (DerivedCategory.quotientCompQhIso C).inv.app P ≫ k ≫
    (DerivedCategory.quotientCompQhIso C).hom.app I) hg
  simpa [DerivedCategory.quotientCompQhIso_hom_naturality, Category.assoc] using h

private theorem kflat_arrow_rep (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P P' : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : DerivedCategory.Q.obj P' ⟶ DerivedCategory.Q.obj P) :
    ∃ (F F' : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (g : F' ⟶ F) (e : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj P)
      (e' : DerivedCategory.Q.obj F' ≅ DerivedCategory.Q.obj P'),
      F.IsKFlatTensor ∧ F'.IsKFlatTensor ∧ e'.hom ≫ a = DerivedCategory.Q.map g ≫ e.hom := by
  obtain ⟨F, s, hF, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := X.sheaf) P
  have := hs
  have : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  obtain ⟨R, r, hr, g, hg⟩ := DerivedCategory.right_fac (a ≫ inv (DerivedCategory.Q.map s))
  have := hr
  obtain ⟨F', q, hF', _, hq, _⟩ := CochainComplex.exists_isKFlatResolution (R := X.sheaf) R
  have := hq
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  refine ⟨F, F', q ≫ g, asIso (DerivedCategory.Q.map s),
    asIso (DerivedCategory.Q.map q ≫ DerivedCategory.Q.map r), hF, hF', ?_⟩
  have h := congrArg (fun k ↦ DerivedCategory.Q.map q ≫ DerivedCategory.Q.map r ≫ k ≫
    DerivedCategory.Q.map s) hg
  simpa [Category.assoc] using h

private theorem naturality_transport
    {D : Type*} [Category D] [MonoidalCategory D]
    (H : Dᵒᵖ × D ⥤ D)
    (t : ∀ K L M : D, (K ⟶ H.obj (op L, M)) → (K ⊗ L ⟶ M))
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
    (f : K ⟶ H.obj (op L, M))
    (hs : t P N I (eK.hom ≫ f ≫
      H.map (X := (op L, M)) (Y := (op N, I)) (eL.hom.op, eM.inv)) =
      (eK.hom ⊗ₘ eL.hom) ≫ t K L M f ≫ eM.inv)
    (ht : t P' N' I' (eK'.hom ≫ (a ≫ f ≫ H.map (b.op, c)) ≫
      H.map (X := (op L', M')) (Y := (op N', I')) (eL'.hom.op, eM'.inv)) =
      (eK'.hom ⊗ₘ eL'.hom) ≫ t K' L' M' (a ≫ f ≫ H.map (b.op, c)) ≫ eM'.inv) :
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

-- Keep the functorial composition calculation independent of resolution instances.
private theorem map_comp_naturality_of_lift
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {P P' I I' : C} {H H' : D}
    (a : P' ⟶ P) (φ : P ⟶ I) (g : I ⟶ I')
    (s : Q.obj I ⟶ H) (s' : Q.obj I' ⟶ H') (h : H ⟶ H') (f : Q.obj P ⟶ H)
    (hg : Q.map g ≫ s' = s ≫ h) (hφ : Q.map φ ≫ s = f) :
    Q.map (a ≫ φ ≫ g) ≫ s' = Q.map a ≫ f ≫ h := by
  simp only [Functor.map_comp, Category.assoc]
  rw [hg, ← Category.assoc (Q.map φ), hφ]

/-- Componentwise uncurrying is natural on the images of actual chain maps.
The input `f` is an arbitrary derived morphism; the three variable maps are chain maps.
Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-chain-naturality).

Proof: Represent the derived images of a and b by chain maps between K-flat
complexes, using right fractions followed by K-flat resolutions of their
sources. The localized quasi-isomorphisms give commuting squares with the
original maps. On these models the Hom complex from the K-flat L-model into
I(M) is K-injective. The bijectivity of Qh on homotopy classes and fullness of
the homotopy quotient lift the transported f to a chain map φ. Naturality of
the fixed internal-Hom factorization identifies the transported input with
the localization of a₀;φ;Hom(b₀,I(c)). Apply ht to this input and to φ, then
use schemeTensorHomUncurry_localized_evaluation for the two explicit evaluation
composites. Finally use hi to transport the equality along the replacement
isomorphisms. Tensor functoriality identifies the source factors, and
cancellation of the tensor of the replacement isomorphisms gives the result.
Only the componentwise localized evaluation remains a separate theorem; the
lifting, replacement squares, factorization naturality and cancellation are
proved here. Identities, zero maps and unbounded complexes require no extra
hypotheses. -/
theorem tensorHomUncurry_chain_natural (X : Scheme.{u})
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
    ∀ (P P' L L' M M' : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (a : P' ⟶ P) (b : L' ⟶ L) (c : M ⟶ M')
      (f : DerivedCategory.Q.obj P ⟶
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M)),
      t (DerivedCategory.Q.obj P') (DerivedCategory.Q.obj L') (DerivedCategory.Q.obj M')
          (DerivedCategory.Q.map a ≫ f ≫
            (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).map ((DerivedCategory.Q.map b).op,
                DerivedCategory.Q.map c)) =
        (DerivedCategory.Q.map a ⊗ₘ DerivedCategory.Q.map b) ≫
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) f ≫
            DerivedCategory.Q.map c := by
  let : Abelian (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance
  let := schemeDerivedTensorMonoidal X
  let Q := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  intro P P' L L' M M' a b c f
  obtain ⟨F, F', a₀, eP, eP', hF, hF', ha⟩ :=
    kflat_arrow_rep X P P' (Q.map a)
  obtain ⟨N, N', b₀, eL, eL', hN, hN', hb⟩ :=
    kflat_arrow_rep X L L' (Q.map b)
  have hn (f₀ : Q.obj F ⟶
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op (Q.obj N), Q.obj M)) :
      t (Q.obj F') (Q.obj N') (Q.obj M')
        (Q.map a₀ ≫ f₀ ≫
          (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
            X.toRingedSpace.sheaf).map ((Q.map b₀).op, Q.map c)) =
      (Q.map a₀ ⊗ₘ Q.map b₀) ≫
        t (Q.obj F) (Q.obj N) (Q.obj M) f₀ ≫ Q.map c := by
    have : IsGrothendieckAbelian.{u}
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
      SheafOfModules.isGrothendieckAbelian _
    have : ((schemeHomKInjectiveResolution X).obj M).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M
    have : (homComplex (R := X.sheaf) N
        ((schemeHomKInjectiveResolution X).obj M)).IsKInjective :=
      CochainComplex.isKInjective_homComplex_of_isKFlat N _ hN
    obtain ⟨φ, hφ⟩ := chain_lift F
      (homComplex (R := X.sheaf) N ((schemeHomKInjectiveResolution X).obj M))
      (f₀ ≫ (schemeDerivedInternalHomResolutionIso X N M).hom)
    have hf : Q.map φ ≫
        (schemeDerivedInternalHomResolutionIso X N M).inv = f₀ :=
      (Iso.comp_inv_eq _).2 hφ
    let ψ : F' ⟶ homComplex (R := X.sheaf) N'
        ((schemeHomKInjectiveResolution X).obj M') :=
      a₀ ≫ φ ≫ (Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map
        (X := (op N, (schemeHomKInjectiveResolution X).obj M))
        (Y := (op N', (schemeHomKInjectiveResolution X).obj M'))
        (b₀.op, (schemeHomKInjectiveResolution X).map c)
    have hψ : Q.map ψ ≫
        (schemeDerivedInternalHomResolutionIso X N' M').inv =
        Q.map a₀ ≫ f₀ ≫
          (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
            X.toRingedSpace.sheaf).map ((Q.map b₀).op, Q.map c) := by
      exact map_comp_naturality_of_lift Q a₀ φ _ _ _ _ f₀
        (hom_model_natural X N N' M M' b₀ c) hf
    rw [← hψ, ht F' N' M' hF' ψ, ← hf, ht F N M hF φ]
    exact schemeTensorHomUncurry_localized_evaluation X F F' N N' M M' a₀ b₀ c φ
  exact naturality_transport
    (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf) t eP eP' eL eL'
    (Iso.refl (Q.obj M)) (Iso.refl (Q.obj M'))
    (Q.map a) (Q.map b) (Q.map c)
    (Q.map a₀) (Q.map b₀) (Q.map c)
    ha hb (by simp) hn f
    (hi _ _ _ _ _ _ eP eL (Iso.refl _) f)
    (hi _ _ _ _ _ _ eP' eL' (Iso.refl _)
      (Q.map a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map ((Q.map b).op, Q.map c)))

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Square

import WeilConjectures.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos
import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension

/-! # Localization of an abelian stalk exchange to strict henselian bases

Source: Stacks Project, Tag 03Q9 (restriction complexes), Tag 03QO (closed-point germs),
and the total-space restriction portion of Tag 095T.
(blueprint: lem-weil-pbc-abelian-stalk-exchange-localization).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme Etale

/-- Restriction to compatible strict henselizations conjugates the original exchange
on abelian stalks to the exchange on the strict local bases. Both sides are stalks;
this statement makes no identification with Ext cohomology and claims no invertibility
of either exchange. The morphism f need only be quasi-compact and quasi-separated.

Source: Stacks Project, Tag 03Q9, proof of theorem-higher-direct-images, restriction
complexes; Tag 03QO, exactness of closed-point germs; Tag 095T, final stalk calculation.
(blueprint: lem-weil-pbc-abelian-stalk-exchange-localization).

Proof:
1. Enlarge the separably closed point fields along ν and ν ≫ ι. Lifts to an etale
neighbourhood are unchanged: its fibre is a disjoint union of spectra of finite
separable field extensions, and these extensions of k or k' are already trivial.
Precomposition therefore gives isomorphisms of the point fibre functors, natural in
sheaves. Commute exact inverse image with homology and apply the inverse-image stalk
comparison to identify the source with the direct-image stalk at σ.
2. Apply the unrestricted 03Q9 restriction to f at ν ≫ ι ≫ σ and to f' at ν ≫ τ.
The second morphism is qcqs by base change. Transport the first total space to X₀
using sq₀ and eA. The square sq₁ and the equation hφ identify X₁ with the base change
of X' to Spec B: paste sq₁ and sq₀, then cancel the original pullback sq.
The inverse-image composition isomorphisms identify the resulting coefficients with
p₀^*G and p₁^*p₀^*G, including the degree-zero derived single-complex comparisons.
3. The closed-point germ on either strict local base is an exact isomorphism by
03QO. Locality of φ and hρ identify the image of the closed B-point with the closed
A-point; hρA and hρB identify its reparametrizations with σ and τ. The Leray comparison
and exactness of closed-point sections now identify the two total-space homologies
in step 2 with the two local higher-direct-image stalks in the conclusion. Compose
these isomorphisms with step 1 and take the underlying additive equivalences.
4. Resolve G by a bounded below injective abelian complex I and replace g'^*I by a
K-injective complex J. The termwise exchange is pullback of sections followed by
I -> J. At each pointed affine neighbourhood, restriction before or after this map
agrees: the structural square hφ and the residue square hρ give the same pointed
etale lift, and strict henselian pointed-lift uniqueness identifies the two lifts.
Thus the section-complex square commutes. Filtered colimits are exact, so passing
to homology gives the displayed equation. Conjugation by the unique pullback
isomorphisms used in step 2 preserves this equation by naturality of the mate.
The argument works in degree zero, for the zero sheaf, for inseparable field
extensions, and for nonstandard pullback models; no torsion is used. -/
theorem Etale.exists_addEquiv_strictHenselization_abelian_stalkExchange
    {S T X X' : Scheme.{u}} {g : T ⟶ S} {f : X ⟶ S}
    [QuasiCompact f] [QuasiSeparated f] {f' : X' ⟶ T} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)]
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictLocalizationToBase (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    {X₀ X₁ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f
      (eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)))
    (p₁ : X₁ ⟶ X₀) (f₁ : X₁ ⟶ Spec (.of B))
    (sq₁ : IsPullback p₁ f₁ f₀ (Spec.map (CommRingCat.ofHom φ)))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let G₀ := (p₀)^*[AddCommGrpCat.{u + 1}].obj G
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj G₀
    let C₁ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)
    let C₂ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f')_*[AddCommGrpCat.{u + 1}])).obj K)
    let L₁ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀)
    let L₂ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀)
    let e := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
    let e₀ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁.toCommSq).app K₀)
    let t₀ := pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))
    ∃ (c₁ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₁ ≃+
        (t₀.sheafFiber (A := AddCommGrpCat.{u + 1})).obj L₁)
      (c₂ : ((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj C₂ ≃+
        (t₀.sheafFiber (A := AddCommGrpCat.{u + 1})).obj L₂),
      ∀ x, c₂ ((((pointSmallEtale τ).sheafFiber
          (A := AddCommGrpCat.{u + 1})).map e).hom x) =
        ((t₀.sheafFiber (A := AddCommGrpCat.{u + 1})).map e₀).hom (c₁ x) := by
  classical
  let jA := eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ)
  let jB := eB.hom ≫ strictLocalizationToBase (ν ≫ τ)
  let g₀ := Spec.map (CommRingCat.ofHom φ)
  have h : jB ≫ g = g₀ ≫ jA := by
    simpa only [jB, g₀, jA, Category.assoc] using hφ.symm
  have hp : (p₁ ≫ p₀) ≫ f = (f₁ ≫ jB) ≫ g := by
    calc
      (p₁ ≫ p₀) ≫ f = p₁ ≫ f₀ ≫ jA := by rw [Category.assoc, sq₀.w]
      _ = f₁ ≫ g₀ ≫ jA := by rw [← Category.assoc, sq₁.w, Category.assoc]
      _ = (f₁ ≫ jB) ≫ g := by
        simpa only [Category.assoc] using congrArg (fun z ↦ f₁ ≫ z) h.symm
  let b := sq.lift (p₁ ≫ p₀) (f₁ ≫ jB) hp
  have hb : b ≫ g' = p₁ ≫ p₀ := sq.lift_fst _ _ _
  have hb' : b ≫ f' = f₁ ≫ jB := sq.lift_snd _ _ _
  have outer : IsPullback (b ≫ g') f₁ f (jB ≫ g) := by
    rw [hb, h]
    exact sq₁.paste_horiz sq₀
  have sqB : IsPullback b f₁ f' jB := outer.of_right hb' sq
  let t := ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
  have ht : t ≫ jB = τ := by simpa only [t, jB, Category.assoc] using hρB
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
    (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
  let M₁ := (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
    D+((g)^*[AddCommGrpCat.{u + 1}])).obj K
  let M₂ := (D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
    R+((f')_*[AddCommGrpCat.{u + 1}])).obj K
  let N₁ := (R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙
    D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀
  let N₂ := (D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙
    R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀
  let r₁ := derivedStalkComparison jB t τ ht M₁ N₁
    (exchangeCubeSourceComparison sq₀.toCommSq h G) (q : ℤ)
  let r₂ := derivedStalkComparison jB t τ ht M₂ N₂
    (exchangeCubeTargetComparison sqB.toCommSq hb G) (q : ℤ)
  have hiso := isIso_strictHenselization_exchangeCube_stalkComparisons
    sq σ τ ι hι ν eA eB φ ρA ρB hφ hρA hρB hρ p₀ f₀ sq₀ p₁ f₁ sq₁ b sqB hb G q
  change IsIso r₁ ∧ IsIso r₂ at hiso
  have : IsIso r₁ := hiso.1
  have : IsIso r₂ := hiso.2
  let L₁ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj N₁
  let L₂ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj N₂
  let t₀ := pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))
  let a₁ := (pointSmallEtalePrecomp
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) ρB).sheafFiber.app L₁
  let a₂ := (pointSmallEtalePrecomp
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) ρB).sheafFiber.app L₂
  have : IsIso a₁ := isIso_pointSmallEtalePrecomp_sheafFiber _ _ L₁
  have : IsIso a₂ := isIso_pointSmallEtalePrecomp_sheafFiber _ _ L₂
  let d₁ := r₁ ≫ inv a₁
  let d₂ := r₂ ≫ inv a₂
  let E := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
  let E₀ := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁.toCommSq).app K₀)
  have hc : r₁ ≫ (pointSmallEtale t).sheafFiber.map E₀ =
      (pointSmallEtale τ).sheafFiber.map E ≫ r₂ :=
    exchangeCube_stalk_square sq.toCommSq sq₀.toCommSq sq₁.toCommSq sqB.toCommSq
      h hb t τ ht G (q : ℤ)
  have hn : t₀.sheafFiber.map E₀ ≫ a₂ =
      a₁ ≫ (pointSmallEtale t).sheafFiber.map E₀ :=
    (pointSmallEtalePrecomp
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) ρB).sheafFiber.naturality E₀
  have hd : d₁ ≫ t₀.sheafFiber.map E₀ = (pointSmallEtale τ).sheafFiber.map E ≫ d₂ := by
    apply (cancel_mono a₂).mp
    dsimp only [d₁, d₂]
    simp only [Category.assoc, hn, IsIso.inv_hom_id, Category.comp_id]
    rw [IsIso.inv_hom_id_assoc, hc]
  refine ⟨(asIso d₁).addCommGroupIsoToAddEquiv,
    (asIso d₂).addCommGroupIsoToAddEquiv, ?_⟩
  intro x
  exact congrArg (fun m ↦ m.hom x) hd.symm


end AlgebraicGeometry

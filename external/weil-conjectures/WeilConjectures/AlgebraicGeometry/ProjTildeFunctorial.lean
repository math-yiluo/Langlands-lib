/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Functoriality of associated module sheaves on Proj

Source: Stacks Project, Constructions, Lemma 01M7, final paragraph, and the construction
before Definition 01M6 (blueprint: lem-sc-p1-proj-tilde-functorial).

The three graded modules are indexed by `Fin 3`. Chart and stalk identifications are
written as injective additive maps into the ordinary localizations with prescribed image.
These are precisely the inclusions composed with the equivalences supplied by
`gradedModuleSheaf_exists`; no new associated sheaf is chosen or defined here.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace LocalizedModule HomogeneousLocalization

namespace AlgebraicGeometry.Proj

private theorem away_exists_fraction
    {S N : Type u} [CommRing S] [AddCommGroup N] [Module S N] (f : S)
    (q : LocalizedModule.Away f N) :
    ∃ (y : N) (m : ℕ), q = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := by
  induction q using LocalizedModule.induction_on with
  | h y t =>
    rcases t with ⟨t, m, rfl⟩
    exact ⟨y, m, rfl⟩

private theorem localized_map_smul
    {S N N' : Type u} [CommRing S] [AddCommGroup N] [AddCommGroup N']
    [Module S N] [Module S N'] (T : Submonoid S) (phi : N →ₗ[S] N')
    (r : Localization T) (q : LocalizedModule T N) :
    IsLocalizedModule.map T (mkLinearMap T N) (mkLinearMap T N') phi (r • q) =
      r • IsLocalizedModule.map T (mkLinearMap T N) (mkLinearMap T N') phi q := by
  induction r using Localization.induction_on with
  | H a =>
    rcases a with ⟨r, t⟩
    induction q using LocalizedModule.induction_on with
    | h y h =>
      simp only [mk_smul_mk, IsLocalizedModule.map_LocalizedModules, map_smul]

/-- A fixed degree-preserving map extends to a morphism having the standard-open fraction
formula. No uniqueness, functor laws, or stalk formulas are asserted here.
Source: Stacks Project, Constructions, Lemma 01M7, final paragraph, and the construction
before Definition 01M6. (blueprint: lem-sc-p1-proj-tilde-functorial)

Proof:
1. Localize the linear map at each positive homogeneous f using IsLocalizedModule.map.
   Its formula on fractions is y/f^m ↦ phi(y)/f^m. Degree preservation sends the
   degree-zero fractions into degree-zero fractions. The injective chart maps alpha,
   with their prescribed ranges, therefore transport it to an additive chart map.
2. The localized map is linear over the localized ring. The homogeneous-localization
   inclusion and hscalar give linearity over the homogeneous chart ring. The standard
   section isomorphism identifies that ring with all structure-sheaf sections on D₊(f),
   so the transported chart map is linear over the full section ring.
3. For an inclusion D₊(g) ≤ D₊(f), choose g^e = a*f by standardOpenProperties.
   The hres formula and phi(a^m • y) = a^m • phi(y) show restriction compatibility.
   Every ordinary localized-module element has a fraction representative, so this
   calculation covers every section, including nonhomogeneous representatives.
4. Positive homogeneous standard opens form a basis. Extend the compatible additive
   chart maps by the basis morphism-extension theorem. Scalar compatibility holds on
   this basis and hence on every open by sheaf separatedness, giving a module-sheaf map.
   Its chart components are the transported maps, which gives the displayed formula.
   Empty charts cause no exception: localization at a nilpotent element is the zero
   module and the only section map is zero. No freeness or finiteness is required.
-/
private theorem tilde_chart_map_exists
    {S : Type u} [CommRing S] (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (M : Fin 3 → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module S (M i)]
    (𝓜 : ∀ i, ℤ → AddSubgroup (M i))
    (F : Fin 3 → (Proj 𝒜).Modules)
    (alpha : ∀ (i : Fin 3) (f : S), ∀ (d : ℕ), 0 < d → f ∈ 𝒜 d →
      (F i).val.obj (op (basicOpen 𝒜 f)) →+ LocalizedModule.Away f (M i))
    (halpha : ∀ (i : Fin 3) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d),
      Function.Injective (alpha i f d hd hf) ∧
      Set.range (alpha i f d hd hf) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 i n : Set (M i)))
        (Submonoid.powers f))
    (hscalar : ∀ (i : Fin 3) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (r : HomogeneousLocalization.Away 𝒜 f) (s : (F i).val.obj (op (basicOpen 𝒜 f))),
      alpha i f d hd hf (awayToSection 𝒜 f r • s) =
        algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) r •
          alpha i f d hd hf s)
    (hres : ∀ (i : Fin 3) (f g : S) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
      (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 b) (inc : basicOpen 𝒜 g ≤ basicOpen 𝒜 f)
      (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g ^ e = a * f →
      ∀ (m : ℕ) (y : M i) (s : (F i).val.obj (op (basicOpen 𝒜 f))),
      alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha i g b hb hg ((F i).val.map (homOfLE inc).op s) =
        mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (i j : Fin 3) (phi : M i →ₗ[S] M j)
    (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z) :
    ∃ chi : F i ⟶ F j,
      ∀ (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) (m : ℕ) (y : M i)
        (s : (F i).val.obj (op (basicOpen 𝒜 f))),
        alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
        alpha j f d hd hf (chi.val.app (op (basicOpen 𝒜 f)) s) =
          mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := by
  classical
  let L (f : S) := IsLocalizedModule.map (Submonoid.powers f)
    (mkLinearMap (Submonoid.powers f) (M i)) (mkLinearMap (Submonoid.powers f) (M j)) phi
  have hpre (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (s : (F i).val.obj (op (basicOpen 𝒜 f))) :
      ∃ t : (F j).val.obj (op (basicOpen 𝒜 f)),
        alpha j f d hd hf t = L f (alpha i f d hd hf s) := by
    have hs : alpha i f d hd hf s ∈ degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 i n : Set (M i)))
        (Submonoid.powers f) := by
      rw [← (halpha i f d hd hf).2]
      exact ⟨s, rfl⟩
    rcases hs with ⟨b, y, t, hy, ht, he⟩
    have him : L f (alpha i f d hd hf s) ∈ degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 j n : Set (M j)))
        (Submonoid.powers f) := by
      refine ⟨b, phi y, t, hphi b y hy, ht, ?_⟩
      rw [← he]
      exact (IsLocalizedModule.map_LocalizedModules (Submonoid.powers f) phi y t).symm
    rw [← (halpha j f d hd hf).2] at him
    exact him
  choose c hc using hpre
  have hlin (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (r : (Proj 𝒜).presheaf.obj (op (basicOpen 𝒜 f)))
      (s : (F i).val.obj (op (basicOpen 𝒜 f))) :
      c f d hd hf (r • s) = r • c f d hd hf s := by
    let e := basicOpenIsoAway 𝒜 f hf hd
    have he : e.hom = awayToSection 𝒜 f := rfl
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 r
    rw [he] at ha
    rw [← ha]
    apply (halpha j f d hd hf).1
    rw [hc, hscalar, hscalar, hc]
    exact localized_map_smul (Submonoid.powers f) phi _ _
  let C (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) :
      (F i).val.obj (op (basicOpen 𝒜 f)) →ₗ[
        (Proj 𝒜).ringCatSheaf.obj.obj (op (basicOpen 𝒜 f))]
          (F j).val.obj (op (basicOpen 𝒜 f)) :=
    { toFun := c f d hd hf
      map_add' := fun s t ↦ (halpha j f d hd hf).1 (by simp only [hc, map_add])
      map_smul' := hlin f d hd hf }
  have hC (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (m : ℕ) (y : M i) (s : (F i).val.obj (op (basicOpen 𝒜 f)))
      (hs : alpha i f d hd hf s =
        mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
      alpha j f d hd hf (C f d hd hf s) =
        mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := by
    rw [show C f d hd hf s = c f d hd hf s from rfl, hc, hs]
    exact IsLocalizedModule.map_LocalizedModules (Submonoid.powers f) phi y _
  have hcompat (f g : S) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
      (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 b) (inc : basicOpen 𝒜 g ≤ basicOpen 𝒜 f)
      (s : (F i).val.obj (op (basicOpen 𝒜 f))) :
      C g b hb hg ((F i).val.map (homOfLE inc).op s) =
        (F j).val.map (homOfLE inc).op (C f d hd hf s) := by
    obtain ⟨e, k, a, he, ha, hrel⟩ :=
      ((standardOpenProperties.{u, u, u} 𝒜).2.2.1 f g d b hd hb hf hg).1.mp inc
    obtain ⟨y, m, hs⟩ := away_exists_fraction f (alpha i f d hd hf s)
    apply (halpha j g b hb hg).1
    rw [hC g b hb hg (e * m) (a ^ m • y) _
      (hres i f g d b hd hb hf hg inc e k a he ha hrel m y s hs)]
    rw [hres j f g d b hd hb hf hg inc e k a he ha hrel m (phi y) _
      (hC f d hd hf m y s hs), map_smul]
  let I := {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
  let D : I → Opens (Proj 𝒜) := fun f ↦ basicOpen 𝒜 f.val.1
  have hrange : Set.range D =
      {U | ∃ (f : S) (d : ℕ), 0 < d ∧ f ∈ 𝒜 d ∧ U = basicOpen 𝒜 f} := by
    ext U
    constructor
    · rintro ⟨⟨⟨f, d⟩, hd, hf⟩, rfl⟩
      exact ⟨f, d, hd, hf, rfl⟩
    · rintro ⟨f, d, hd, hf, rfl⟩
      exact ⟨⟨⟨f, d⟩, hd, hf⟩, rfl⟩
  have hB : Opens.IsBasis (Set.range D) := by
    rw [hrange]
    exact (standardOpenProperties.{u, u, u} 𝒜).1
  let beta : (inducedFunctor D).op ⋙ (F i).val.presheaf ⟶
      (inducedFunctor D).op ⋙ (F j).val.presheaf :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        (C U.unop.val.1 U.unop.val.2 U.unop.property.1 U.unop.property.2).toAddMonoidHom
      naturality := by
        intro U V inc
        ext s
        exact hcompat U.unop.val.1 V.unop.val.1 U.unop.val.2 V.unop.val.2
          U.unop.property.1 V.unop.property.1 U.unop.property.2 V.unop.property.2
          ((inducedFunctor D).map inc.unop).le s }
  let H := TopCat.Sheaf.restrictHomEquivHom (F i).val.presheaf
    (⟨(F j).val.presheaf, (F j).isSheaf⟩) hB beta
  have hHB (g : S) (b : ℕ) (hb : 0 < b) (hg : g ∈ 𝒜 b)
      (s : (F i).val.obj (op (basicOpen 𝒜 g))) :
      H.app (op (basicOpen 𝒜 g)) s = C g b hb hg s := by
    exact congrArg (fun k ↦ k s)
      (TopCat.Sheaf.extend_hom_app (F i).val.presheaf
        (⟨(F j).val.presheaf, (F j).isSheaf⟩) hB beta ⟨⟨g, b⟩, hb, hg⟩)
  have hlinear (U : (Opens (Proj 𝒜))ᵒᵖ)
      (r : (Proj 𝒜).ringCatSheaf.obj.obj U) (s : (F i).val.obj U) :
      H.app U (r • s) = r • H.app U s := by
    apply TopCat.Presheaf.IsSheaf.section_ext (F j).isSheaf
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := hB.exists_subset_of_mem_open hx U.unop.2
    rcases hV with ⟨⟨⟨g, b⟩, hb, hg⟩, rfl⟩
    refine ⟨basicOpen 𝒜 g, hVU, hxV, ?_⟩
    have hnat := H.naturality_apply (homOfLE hVU).op
    change (F j).val.map (homOfLE hVU).op (H.app U (r • s)) =
      (F j).val.map (homOfLE hVU).op (r • H.app U s)
    erw [← hnat, (F i).val.map_smul, (F j).val.map_smul, ← hnat]
    erw [hHB g b hb hg, hHB g b hb hg]
    exact (C g b hb hg).map_smul _ _
  let chi : F i ⟶ F j :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
        { toFun := H.app U
          map_add' := (H.app U).hom.map_add
          map_smul' := hlinear U }
       naturality := by
         intro U V inc
         ext s
         exact H.naturality_apply inc s }⟩
  refine ⟨chi, ?_⟩
  intro g b hb hg m y s hs
  change alpha j g b hb hg (H.app (op (basicOpen 𝒜 g)) s) = _
  rw [hHB g b hb hg]
  exact hC g b hb hg m y s hs


/-- A degree-preserving linear map has a unique associated sheaf map, with the indicated
fraction formulas on charts and stalks. These maps preserve composition and identities.
Source: Stacks, Constructions, Lemma 01M7 and the construction before Definition 01M6.
(blueprint: lem-sc-p1-proj-tilde-functorial)

Proof:
1. Localize each degree-preserving linear map with `IsLocalizedModule.map`. The prescribed
   chart ranges and injectivity give additive chart maps with the required fraction formula;
   Mathlib's `basicOpenIsoAway` and the scalar hypotheses make them module-linear.
2. For standard-open inclusions, `standardOpenProperties` supplies a relation `g^e = a*f`.
   The two restriction formulas and linearity of the graded map prove chart naturality.
3. Positive homogeneous standard opens form a basis. Extend the compatible chart maps with
   `TopCat.Sheaf.restrictHomEquivHom`; sheaf extensionality proves scalar compatibility on
   every open. Basis extensionality and chart injectivity prove uniqueness, then composition
   and identity follow from their fraction formulas.
4. For stalks, represent a germ on a basis chart with `exists_mem_germ_eq_of_isBasis`,
   represent its chart image by a fraction, and apply `hgerm` before and after the map.
   `stalkFunctor_map_germ_apply` and `map_LocalizedModules` give the asserted fraction
   formula, including arbitrary (possibly degree-zero) denominators.
-/
theorem tilde_functorial
    {S : Type u} [CommRing S] (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (M : Fin 3 → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module S (M i)]
    (𝓜 : ∀ i, ℤ → AddSubgroup (M i))
    (F : Fin 3 → (Proj 𝒜).Modules)
    (alpha : ∀ (i : Fin 3) (f : S), ∀ (d : ℕ), 0 < d → f ∈ 𝒜 d →
      (F i).val.obj (op (basicOpen 𝒜 f)) →+ LocalizedModule.Away f (M i))
    (halpha : ∀ (i : Fin 3) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d),
      Function.Injective (alpha i f d hd hf) ∧
      Set.range (alpha i f d hd hf) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 i n : Set (M i)))
        (Submonoid.powers f))
    (hscalar : ∀ (i : Fin 3) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (r : HomogeneousLocalization.Away 𝒜 f) (s : (F i).val.obj (op (basicOpen 𝒜 f))),
      alpha i f d hd hf (awayToSection 𝒜 f r • s) =
        algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) r •
          alpha i f d hd hf s)
    (hres : ∀ (i : Fin 3) (f g : S) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
      (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 b) (inc : basicOpen 𝒜 g ≤ basicOpen 𝒜 f)
      (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g ^ e = a * f →
      ∀ (m : ℕ) (y : M i) (s : (F i).val.obj (op (basicOpen 𝒜 f))),
      alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha i g b hb hg ((F i).val.map (homOfLE inc).op s) =
        mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (mu : ∀ (i : Fin 3) (x : Proj 𝒜),
      (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj (F i) →+
        LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl (M i))
    (hgerm : ∀ (i : Fin 3) (x : Proj 𝒜) (f : S) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ 𝒜 d) (hx : x ∈ basicOpen 𝒜 f) (m : ℕ) (y : M i)
      (s : (F i).val.obj (op (basicOpen 𝒜 f)))
      (t : x.asHomogeneousIdeal.toIdeal.primeCompl),
      alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      (t : S) = f ^ m →
      mu i x (TopCat.Presheaf.germ (F i).val.presheaf (basicOpen 𝒜 f) x hx s) = mk y t) :
    ∃ lift : ∀ (i j : Fin 3) (phi : M i →ₗ[S] M j),
      (∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z) → (F i ⟶ F j),
      (∀ (i j : Fin 3) (phi : M i →ₗ[S] M j)
        (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z)
        (chi : F i ⟶ F j),
        (∀ (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) (m : ℕ) (y : M i)
          (s : (F i).val.obj (op (basicOpen 𝒜 f))),
          alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha j f d hd hf (chi.val.app (op (basicOpen 𝒜 f)) s) =
            mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) ↔
          chi = lift i j phi hphi) ∧
      (∀ (i j k : Fin 3) (phi : M i →ₗ[S] M j) (psi : M j →ₗ[S] M k)
        (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z)
        (hpsi : ∀ (z : ℤ) (y : M j), y ∈ 𝓜 j z → psi y ∈ 𝓜 k z),
        lift i k (psi.comp phi) (fun z y hy ↦ hpsi z (phi y) (hphi z y hy)) =
          lift i j phi hphi ≫ lift j k psi hpsi) ∧
      (∀ i : Fin 3, lift i i (LinearMap.id : M i →ₗ[S] M i) (fun _ _ hy ↦ hy) = 𝟙 (F i)) ∧
      (∀ (i j : Fin 3) (phi : M i →ₗ[S] M j)
        (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z)
        (x : Proj 𝒜) (d : ℕ) (h : x.asHomogeneousIdeal.toIdeal.primeCompl)
        (y : M i), (h : S) ∈ 𝒜 d → y ∈ 𝓜 i d →
        ∀ s : (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj (F i),
        mu i x s = mk y h →
        mu j x ((RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).map
          (lift i j phi hphi) s) = mk (phi y) h) := by
  classical
  let P := fun (i j : Fin 3) (phi : M i →ₗ[S] M j) (chi : F i ⟶ F j) ↦
    ∀ (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) (m : ℕ) (y : M i)
      (s : (F i).val.obj (op (basicOpen 𝒜 f))),
      alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha j f d hd hf (chi.val.app (op (basicOpen 𝒜 f)) s) =
        mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)
  have hex (i j : Fin 3) (phi : M i →ₗ[S] M j)
      (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z) :
      ∃ chi : F i ⟶ F j, P i j phi chi :=
    tilde_chart_map_exists 𝒜 M 𝓜 F alpha halpha hscalar hres i j phi hphi
  choose lift hlift using hex
  let B : Set (Opens (Proj 𝒜)) :=
    {U | ∃ (f : S) (d : ℕ), 0 < d ∧ f ∈ 𝒜 d ∧ U = basicOpen 𝒜 f}
  have hB : Opens.IsBasis B := (standardOpenProperties.{u, u, u} 𝒜).1
  have hBrange : Opens.IsBasis (Set.range (fun U : B ↦ U.val)) := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hB
  have hunique (i j : Fin 3) (phi : M i →ₗ[S] M j) (chi chi' : F i ⟶ F j)
      (hc : P i j phi chi) (hc' : P i j phi chi') : chi = chi' := by
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.toPresheaf _).map_injective
    apply TopCat.Sheaf.hom_ext (F i).val.presheaf
      (⟨(F j).val.presheaf, (F j).isSheaf⟩) hBrange
    rintro ⟨U, f, d, hd, hf, rfl⟩
    ext s
    apply (halpha j f d hd hf).1
    obtain ⟨y, m, hy⟩ := away_exists_fraction f (alpha i f d hd hf s)
    exact (hc f d hd hf m y s hy).trans (hc' f d hd hf m y s hy).symm
  refine ⟨lift, ?_, ?_, ?_, ?_⟩
  · intro i j phi hphi chi
    exact ⟨fun hc ↦ hunique i j phi chi (lift i j phi hphi) hc (hlift i j phi hphi),
      fun he ↦ he ▸ hlift i j phi hphi⟩
  · intro i j k phi psi hphi hpsi
    apply hunique i k (psi.comp phi)
    · exact hlift i k (psi.comp phi) _
    · intro f d hd hf m y s hs
      change alpha k f d hd hf
        ((lift j k psi hpsi).val.app (op (basicOpen 𝒜 f))
          ((lift i j phi hphi).val.app (op (basicOpen 𝒜 f)) s)) = _
      exact hlift j k psi hpsi f d hd hf m (phi y) _
        (hlift i j phi hphi f d hd hf m y s hs)
  · intro i
    apply hunique i i LinearMap.id
    · exact hlift i i LinearMap.id _
    · intro f d hd hf m y s hs
      exact hs
  · intro i j phi hphi x d h y hh hy s hs
    let T := x.asHomogeneousIdeal.toIdeal.primeCompl
    let L := IsLocalizedModule.map T (mkLinearMap T (M i)) (mkLinearMap T (M j)) phi
    have hnat (v : (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj (F i)) :
        mu j x ((RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).map
          (lift i j phi hphi) v) = L (mu i x v) := by
      obtain ⟨U, hxU, hU, t, ht⟩ :=
        TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB (F i).val.presheaf x v
      rcases hU with ⟨f, b, hb, hf, rfl⟩
      obtain ⟨z, n, hz⟩ := away_exists_fraction f (alpha i f b hb hf t)
      have hfT : f ∈ T := hxU
      let denom : T := ⟨f ^ n, T.pow_mem hfT n⟩
      have hgi := hgerm i x f b hb hf hxU n z t denom hz rfl
      have hgj := hgerm j x f b hb hf hxU n (phi z)
        ((lift i j phi hphi).val.app (op (basicOpen 𝒜 f)) t) denom
        (hlift i j phi hphi f b hb hf n z t hz) rfl
      rw [← ht]
      change mu j x ((TopCat.Presheaf.stalkFunctor Ab x).map
        ((PresheafOfModules.toPresheaf _).map (lift i j phi hphi).val)
          (TopCat.Presheaf.germ (F i).val.presheaf (basicOpen 𝒜 f) x hxU t)) = _
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      change mu j x (TopCat.Presheaf.germ (F j).val.presheaf (basicOpen 𝒜 f) x hxU
        ((lift i j phi hphi).val.app (op (basicOpen 𝒜 f)) t)) = _
      rw [hgj, hgi]
      exact (IsLocalizedModule.map_LocalizedModules T phi z denom).symm
    rw [hnat, hs]
    exact IsLocalizedModule.map_LocalizedModules T phi y h

end AlgebraicGeometry.Proj

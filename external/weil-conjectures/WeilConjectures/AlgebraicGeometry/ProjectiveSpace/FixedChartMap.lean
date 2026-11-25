/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

import Mathlib.RingTheory.Localization.Module
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties

/-!
# Morphisms from associated-sheaf chart data

## References

* Stacks Project, Tag 01M7, functoriality
* Tag 009U, modules on a basis
* Stacks Project, Tag 01M7 (functoriality), and Tag 009U
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

-- Basis-extension elaboration uses dependent module-section coercions.
private theorem map_of_basis
    (X : Scheme.{u}) (I : Type u) (U : I → X.Opens) (hB : Opens.IsBasis (Set.range U))
    (F G : X.Modules) (χ : ∀ i, F.val.obj (op (U i)) ⟶ G.val.obj (op (U i)))
    (hχ : ∀ (i j : I) (inc : U j ≤ U i) (s : F.val.obj (op (U i))),
      χ j (F.val.map (homOfLE inc).op s) = G.val.map (homOfLE inc).op (χ i s)) :
    ∃ g : F ⟶ G, ∀ i, g.val.app (op (U i)) = χ i := by
  let a : (inducedFunctor U).op ⋙ F.presheaf ⟶ (inducedFunctor U).op ⋙ G.presheaf :=
    { app := fun i ↦ AddCommGrpCat.ofHom (χ i.unop).hom.toAddMonoidHom
      naturality := by
        intro i j f
        ext s
        exact hχ i.unop j.unop (leOfHom ((inducedFunctor U).map f.unop)) s }
  let a' : F.presheaf ⟶ G.presheaf :=
    TopCat.Sheaf.restrictHomEquivHom F.presheaf ⟨G.presheaf, G.isSheaf⟩ hB a
  have ha' (i : I) : a'.app (op (U i)) = a.app (op i) :=
    TopCat.Sheaf.extend_hom_app F.presheaf ⟨G.presheaf, G.isSheaf⟩ hB a i
  have hlin (W : X.Opens) (r : Γ(X, W))
      (s : F.val.obj (op W)) :
      a'.app (op W) (r • s) = r • (a'.app (op W) s : G.val.obj (op W)) := by
    have hcover : (⨆ i : {i : I // U i ≤ W}, U i.val) = W := by
      apply le_antisymm
      · exact iSup_le fun i ↦ i.property
      · intro x hx
        obtain ⟨V, ⟨i, rfl⟩, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp hB hx
        exact Opens.mem_iSup.mpr ⟨⟨i, hVW⟩, hxV⟩
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨G.presheaf, G.isSheaf⟩
      (fun i : {i : I // U i ≤ W} ↦ U i.val) W
      (fun i ↦ homOfLE i.property) (le_of_eq hcover.symm)
    intro i
    have hn (v : Γ(F, W)) :
        a'.app (op (U i.val)) (F.presheaf.map (homOfLE i.property).op v) =
          G.presheaf.map (homOfLE i.property).op (a'.app (op W) v) :=
      ConcreteCategory.congr_hom (a'.naturality (homOfLE i.property).op) v
    change G.presheaf.map (homOfLE i.property).op (a'.app (op W) (r • s)) =
      G.presheaf.map (homOfLE i.property).op (r • (a'.app (op W) s : Γ(G, W)))
    rw [← hn, F.map_smul, G.map_smul, ← hn, ha']
    exact (χ i.val).hom.map_smul _ _
  refine ⟨⟨PresheafOfModules.homMk a' (fun W ↦ hlin W.unop)⟩, ?_⟩
  intro i
  ext s
  exact ConcreteCategory.congr_hom (ha' i) s

-- Extending chart maps elaborates many dependent section and localization types.
/-- A degree-preserving map induces a map between any two sheaves with the prescribed charts. -/
theorem fixed_chart_map (k : Type u) [Field k]
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M)
    (F : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f M)
    (halpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f))
    (hscalar : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • alpha f d hd hf s)
    (hres : ∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : M)
          (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha g b hb hg (F.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (N : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓝 : ℤ → AddSubgroup N)
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (beta : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f N)
    (hbeta : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (beta f d hd hf) ∧
        Set.range (beta f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ (𝓝 n : Set N)) (Submonoid.powers f))
    (hbetascalar : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        beta f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • beta f d hd hf s)
    (hbetares : ∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : N)
          (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          beta f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          beta g b hb hg (G.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (phi : M →ₗ[MvPolynomial (Fin 2) k] N)
    (hphi : ∀ (z : ℤ) (y : M), y ∈ 𝓜 z → phi y ∈ 𝓝 z) :
    ∃ g : F ⟶ G,
      ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d) (m : ℕ) (y : M)
        (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
        beta f d hd hf (g.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) s) =
          mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := by
  classical
  let S := MvPolynomial (Fin 2) k
  let 𝒜 := homogeneousSubmodule (Fin 2) k
  let L (f : S) : LocalizedModule.Away f M →ₗ[S] LocalizedModule.Away f N :=
    IsLocalizedModule.map (Submonoid.powers f)
      (mkLinearMap (Submonoid.powers f) M) (mkLinearMap (Submonoid.powers f) N) phi
  have hL (f : S) (y : M) (t : Submonoid.powers f) : L f (mk y t) = mk (phi y) t :=
    IsLocalizedModule.map_LocalizedModules _ _ _ _
  have hrange (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (s : F.val.obj (op (basicOpen 𝒜 f))) :
      ∃ t : G.val.obj (op (basicOpen 𝒜 f)), beta f d hd hf t = L f (alpha f d hd hf s) := by
    have hs : alpha f d hd hf s ∈ degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers f) := (halpha f d hd hf).2 ▸ Set.mem_range_self s
    obtain ⟨n, y, t, hy, ht, heq⟩ := hs
    apply (show L f (alpha f d hd hf s) ∈ Set.range (beta f d hd hf) from ?_)
    rw [(hbeta f d hd hf).2]
    exact ⟨n, phi y, t, hphi n y hy, ht, by rw [← heq, hL]⟩
  let t (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (s : F.val.obj (op (basicOpen 𝒜 f))) := (hrange f d hd hf s).choose
  have ht (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (s : F.val.obj (op (basicOpen 𝒜 f))) :
      beta f d hd hf (t f d hd hf s) = L f (alpha f d hd hf s) :=
    (hrange f d hd hf s).choose_spec
  have hadd (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (s s' : F.val.obj (op (basicOpen 𝒜 f))) :
      t f d hd hf (s + s') = t f d hd hf s + t f d hd hf s' := by
    apply (hbeta f d hd hf).1
    simp only [ht, map_add]
  have hsm (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (r : (Proj 𝒜).ringCatSheaf.obj.obj (op (basicOpen 𝒜 f)))
      (s : F.val.obj (op (basicOpen 𝒜 f))) :
      t f d hd hf (r • s) = r • t f d hd hf s := by
    let e := basicOpenIsoAway 𝒜 f hf hd
    obtain ⟨r', rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 r
    apply (hbeta f d hd hf).1
    rw [ht]
    change L f (alpha f d hd hf (awayToSection 𝒜 f r' • s)) =
      beta f d hd hf (awayToSection 𝒜 f r' • t f d hd hf s)
    rw [hscalar, hbetascalar, ht]
    exact (L f).map_smul_of_tower _ _
  have hformula (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (m : ℕ) (y : M) (s : F.val.obj (op (basicOpen 𝒜 f)))
      (hs : alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
      beta f d hd hf (t f d hd hf s) =
        mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := by
    rw [ht, hs, hL]
  have hnat (f g : S) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
      (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 b) (inc : basicOpen 𝒜 g ≤ basicOpen 𝒜 f)
      (s : F.val.obj (op (basicOpen 𝒜 f))) :
      t g b hb hg (F.val.map (homOfLE inc).op s) =
        G.val.map (homOfLE inc).op (t f d hd hf s) := by
    obtain ⟨e, c, a, he, ha, hrel⟩ :=
      ((standardOpenProperties.{u, u, u} 𝒜).2.2.1 f g d b hd hb hf hg).1.mp inc
    have hrepr : ∃ (m : ℕ) (y : M), alpha f d hd hf s =
        mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := by
      generalize alpha f d hd hf s = z
      induction z using LocalizedModule.induction_on with
      | _ y v =>
        obtain ⟨m, hm⟩ := v.property
        exact ⟨m, y, by congr 1; exact Subtype.ext hm.symm⟩
    obtain ⟨m, y, hs⟩ := hrepr
    apply (hbeta g b hb hg).1
    rw [ht, hres f g d b hd hb hf hg inc e c a he ha hrel m y s hs, hL]
    rw [hbetares f g d b hd hb hf hg inc e c a he ha hrel m (phi y)
      (t f d hd hf s) (hformula f d hd hf m y s hs), phi.map_smul]
  let I := {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
  let U : I → (Proj 𝒜).Opens := fun i ↦ basicOpen 𝒜 i.val.1
  have hB : Opens.IsBasis (Set.range U) := by
    convert (standardOpenProperties.{u, u, u} 𝒜).1 using 1
    ext W
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val.1, i.val.2, i.property.1, i.property.2, rfl⟩
    · rintro ⟨f, d, hd, hf, rfl⟩
      exact ⟨⟨(f, d), hd, hf⟩, rfl⟩
  let χ (i : I) : F.val.obj (op (U i)) ⟶ G.val.obj (op (U i)) := ModuleCat.ofHom
    { toFun := t i.val.1 i.val.2 i.property.1 i.property.2
      map_add' := hadd _ _ _ _
      map_smul' := hsm _ _ _ _ }
  obtain ⟨g, hg⟩ := map_of_basis (Proj 𝒜) I U hB F G χ
    (fun i j inc s ↦ hnat i.val.1 j.val.1 i.val.2 j.val.2
      i.property.1 j.property.1 i.property.2 j.property.2 inc s)
  refine ⟨g, ?_⟩
  intro f d hd hf m y s hs
  rw [hg ⟨(f, d), hd, hf⟩]
  exact hformula f d hd hf m y s hs

end AlgebraicGeometry.Proj

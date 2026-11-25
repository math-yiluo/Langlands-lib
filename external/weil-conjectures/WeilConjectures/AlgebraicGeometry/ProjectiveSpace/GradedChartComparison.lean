/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Module.DegreeZeroFractions
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import WeilConjectures.Topology.SheafOfModulesFromBasis
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.RingTheory.Localization.Module

/-!
# Comparing Proj module sheaves from fraction charts

## References

* Stacks Project, Constructions, Lemma 01M7
* Sheaves on Spaces, Tags 009N and 009U
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem iso_of_basis (X : TopCat.{u}) (R : TopCat.Sheaf RingCat.{u} X)
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hcap : ∀ U V : B, U.val ⊓ V.val ∈ B)
    (hrefine : ∀ (U : B) (C : Set B),
      (∀ V ∈ C, V.val ≤ U.val) → (⨆ V ∈ C, V.val) = U.val →
      ∃ (n : ℕ) (W : Fin n → B), (⨆ i, (W i).val) = U.val ∧
        ∀ i, ∃ V ∈ C, (W i).val ≤ V.val)
    (F G : SheafOfModules.{u} R)
    (l : ∀ U : B, F.val.obj (op U.val) ≃ₗ[R.obj.obj (op U.val)]
      G.val.obj (op U.val))
    (hl : ∀ (U V : B) (h : V.val ≤ U.val) (s : F.val.obj (op U.val)),
      l V (F.val.map (homOfLE h).op s) = G.val.map (homOfLE h).op (l U s)) :
    Nonempty (F ≅ G) := by
  let r (U V : B) (h : V.val ≤ U.val) : F.val.obj (op U.val) →+
      F.val.obj (op V.val) := (F.val.presheaf.map (homOfLE h).op).hom
  have hid (U : B) (s : F.val.obj (op U.val)) : r U U le_rfl s = s := by
    simp [r]
  have hcomp (U V W : B) (hVU : V.val ≤ U.val) (hWV : W.val ≤ V.val)
      (s : F.val.obj (op U.val)) :
      r V W hWV (r U V hVU s) = r U W (hWV.trans hVU) s := by
    change F.val.presheaf.map _ (F.val.presheaf.map _ s) = F.val.presheaf.map _ s
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hscalar (U V : B) (h : V.val ≤ U.val) (a : R.obj.obj (op U.val))
      (s : F.val.obj (op U.val)) :
      r U V h (a • s) = R.obj.map (homOfLE h).op a • r U V h s :=
    F.val.map_smul _ _ _
  have hglue (U : B) (n : ℕ) (V : Fin n → B) (hV : ∀ i, (V i).val ≤ U.val)
      (hcover : (⨆ i, (V i).val) = U.val) (s : ∀ i, F.val.obj (op (V i).val))
      (hs : ∀ i j,
        r (V i) ⟨(V i).val ⊓ (V j).val, hcap (V i) (V j)⟩ inf_le_left (s i) =
        r (V j) ⟨(V i).val ⊓ (V j).val, hcap (V i) (V j)⟩ inf_le_right (s j)) :
      ∃! t : F.val.obj (op U.val), ∀ i, r U (V i) (hV i) t = s i := by
    let F' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F.val.presheaf, F.isSheaf⟩
    exact F'.existsUnique_gluing' (fun i ↦ (V i).val) U.val
      (fun i ↦ homOfLE (hV i)) hcover.ge s (by
        intro i j
        exact hs i j)
  obtain ⟨_, _, _, _, huniq, _⟩ := Opens.exists_sheafOfModules_from_basis X B hB hcap
    hrefine R (fun U ↦ F.val.obj (op U.val)) r hid hcomp hscalar hglue
  obtain ⟨eF, _, _⟩ := huniq F (fun U ↦ LinearEquiv.refl _ _) (by
    intro U V h s
    rfl)
  obtain ⟨eG, _, _⟩ := huniq G (fun U ↦ (l U).symm) (by
    intro U V h s
    apply (l V).injective
    simp only [LinearEquiv.apply_symm_apply]
    calc
      G.val.map (homOfLE h).op s =
          l V (F.val.map (homOfLE h).op ((l U).symm s)) := by
        simpa only [LinearEquiv.apply_symm_apply] using (hl U V h ((l U).symm s)).symm
      _ = l V (r U V h ((l U).symm s)) := by
        congr 1)
  exact ⟨eF.symm ≪≫ eG⟩

private theorem exists_localizedEquiv_mk {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (T : Submonoid R) (e : M ≃ₗ[R] N) :
    ∃ L : LocalizedModule T M ≃ₗ[Localization T] LocalizedModule T N,
      ∀ (y : M) (h : T), L (mk y h) = mk (e y) h := by
  refine ⟨IsLocalizedModule.mapEquiv T (mkLinearMap _ M) (mkLinearMap _ N)
    (Localization T) e, ?_⟩
  intro y h
  exact LocalizedModule.map_mk _ _ _ _

private theorem exists_away_fraction {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (f : R) (x : LocalizedModule.Away f M) :
    ∃ (y : M) (m : ℕ), x = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := by
  induction x using LocalizedModule.induction_on with
  | h y s =>
    obtain ⟨m, hm⟩ := s.property
    have hs : s = (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hm.symm
    exact ⟨y, m, by rw [hs]⟩

private theorem away_chart_map_naturality {R M N P P' Q Q' : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f g : R) (e : M →ₗ[R] N)
    (A : P → LocalizedModule.Away f M) (A' : P' → LocalizedModule.Away g M)
    (B : Q → LocalizedModule.Away f N) (B' : Q' → LocalizedModule.Away g N)
    (φ : P → Q) (φ' : P' → Q')
    (L : LocalizedModule.Away f M → LocalizedModule.Away f N)
    (L' : LocalizedModule.Away g M → LocalizedModule.Away g N)
    (hB' : Function.Injective B')
    (hφ : ∀ s, B (φ s) = L (A s)) (hφ' : ∀ s, B' (φ' s) = L' (A' s))
    (hL : ∀ (y : M) (h : Submonoid.powers f), L (mk y h) = mk (e y) h)
    (hL' : ∀ (y : M) (h : Submonoid.powers g), L' (mk y h) = mk (e y) h)
    (u : P → P') (v : Q → Q') (a : R) (d : ℕ)
    (hres : ∀ (m : ℕ) (y : M) (s : P),
      A s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      A' (u s) = mk (a ^ m • y) (⟨g ^ (d * m), ⟨d * m, rfl⟩⟩ : Submonoid.powers g))
    (hbetaRes : ∀ (m : ℕ) (y : N) (s : Q),
      B s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      B' (v s) = mk (a ^ m • y) (⟨g ^ (d * m), ⟨d * m, rfl⟩⟩ : Submonoid.powers g))
    (s : P) : φ' (u s) = v (φ s) := by
  obtain ⟨y, m, hs⟩ := exists_away_fraction f (A s)
  have ht : B (φ s) = mk (e y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := by
    rw [hφ, hs, hL]
  apply hB'
  rw [hφ', hres m y s hs, hbetaRes m (e y) (φ s) ht, hL', map_smul]

private theorem addEquiv_of_matching_ranges
    {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    (A : M →+ P) (B : N →+ Q) (hA : Function.Injective A) (hB : Function.Injective B)
    (e : P ≃+ Q) (hrange : ∀ x, x ∈ A.range ↔ e x ∈ B.range) :
    ∃ φ : M ≃+ N, ∀ s, B (φ s) = e (A s) := by
  let toB : M →+ B.range :=
    { toFun := fun s ↦ ⟨e (A s), (hrange _).mp ⟨s, rfl⟩⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun s t ↦ Subtype.ext (by simp) }
  let φ : M →+ N := (AddMonoidHom.ofInjective hB).symm.toAddMonoidHom.comp toB
  have hφ (s : M) : B (φ s) = e (A s) := AddMonoidHom.apply_ofInjective_symm hB _
  have hbij : Function.Bijective φ := by
    constructor
    · intro s t hst
      apply hA
      apply e.injective
      rw [← hφ, ← hφ, hst]
    · intro t
      have ht : e.symm (B t) ∈ A.range := by
        apply (hrange _).mpr
        rw [AddEquiv.apply_symm_apply]
        exact ⟨t, rfl⟩
      obtain ⟨s, hs⟩ := ht
      refine ⟨s, hB ?_⟩
      rw [hφ, hs, AddEquiv.apply_symm_apply]
  exact ⟨AddEquiv.ofBijective φ hbij, hφ⟩

private theorem iso_of_indexed_basis (X : TopCat.{u}) (R : TopCat.Sheaf RingCat.{u} X)
    {I : Type u} (D : I → Opens X) (hB : Opens.IsBasis (Set.range D))
    (hcap : ∀ U V : Set.range D, U.val ⊓ V.val ∈ Set.range D)
    (hrefine : ∀ (U : Set.range D) (C : Set (Set.range D)),
      (∀ V ∈ C, V.val ≤ U.val) → (⨆ V ∈ C, V.val) = U.val →
      ∃ (n : ℕ) (W : Fin n → Set.range D), (⨆ i, (W i).val) = U.val ∧
        ∀ i, ∃ V ∈ C, (W i).val ≤ V.val)
    (F G : SheafOfModules.{u} R)
    (lin : ∀ i, F.val.obj (op (D i)) ≃ₗ[R.obj.obj (op (D i))] G.val.obj (op (D i)))
    (hlin : ∀ i j (h : D j ≤ D i) (s : F.val.obj (op (D i))),
      lin j (F.val.map (homOfLE h).op s) = G.val.map (homOfLE h).op (lin i s)) :
    Nonempty (F ≅ G) := by
  classical
  let idx (U : Set.range D) : I := U.property.choose
  have hidx (U : Set.range D) : D (idx U) = U.val := U.property.choose_spec
  let l (U : Set.range D) : F.val.obj (op U.val) ≃ₗ[R.obj.obj (op U.val)]
      G.val.obj (op U.val) := (hidx U) ▸ lin (idx U)
  have hlin' (i j : I) (U V : Opens X) (hi : D i = U) (hj : D j = V)
      (inc : V ≤ U) (s : F.val.obj (op U)) :
      (hj ▸ lin j) (F.val.map (homOfLE inc).op s) =
        G.val.map (homOfLE inc).op ((hi ▸ lin i) s) := by
    subst U V
    exact hlin i j inc s
  apply iso_of_basis X R (Set.range D) hB hcap hrefine F G l
  intro U V h s
  exact hlin' (idx U) (idx V) U.val V.val (hidx U) (hidx V) h s

/-- A linear equivalence preserving numerator degrees compares sheaves given by charts. -/
theorem graded_chart_comparison (k : Type u) [Field k]
    (M N : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℕ → Set M) (𝓝 : ℕ → Set N)
    (e : M ≃ₗ[MvPolynomial (Fin 2) k] N)
    (hdegree : ∀ (n : ℕ) (y : M), y ∈ 𝓜 n ↔ e y ∈ 𝓝 n)
    (F G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f M)
    (halpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ 𝓜 n) (Submonoid.powers f))
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
    (beta : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f N)
    (hbeta : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (beta f d hd hf) ∧
        Set.range (beta f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ 𝓝 n) (Submonoid.powers f))
    (hbetaScalar : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        beta f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • beta f d hd hf s)
    (hbetaRes : ∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
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
    : Nonempty (F ≅ G) := by
  classical
  let S := MvPolynomial (Fin 2) k
  let 𝒜 := homogeneousSubmodule (Fin 2) k
  let I := {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
  let D (f : I) := basicOpen 𝒜 f.val.1
  have hL_exists (f : I) :
      ∃ L : LocalizedModule.Away f.val.1 M ≃ₗ[Localization.Away f.val.1]
          LocalizedModule.Away f.val.1 N,
        ∀ (y : M) (h : Submonoid.powers f.val.1), L (mk y h) = mk (e y) h :=
    exists_localizedEquiv_mk (Submonoid.powers f.val.1) e
  choose L hL using hL_exists
  let A (f : I) := alpha f.val.1 f.val.2 f.property.1 f.property.2
  let B (f : I) := beta f.val.1 f.val.2 f.property.1 f.property.2
  have hrange (f : I) (x : LocalizedModule.Away f.val.1 M) :
      x ∈ (A f).range ↔ L f x ∈ (B f).range := by
    change x ∈ Set.range (A f) ↔ L f x ∈ Set.range (B f)
    rw [(halpha f.val.1 f.val.2 f.property.1 f.property.2).2,
      (hbeta f.val.1 f.val.2 f.property.1 f.property.2).2]
    constructor
    · rintro ⟨n, y, h, hy, hh, rfl⟩
      exact ⟨n, e y, h, (hdegree n y).mp hy, hh, (hL f y h).symm⟩
    · rintro ⟨n, y, h, hy, hh, heq⟩
      refine ⟨n, e.symm y, h, ?_, hh, ?_⟩
      · exact (hdegree n (e.symm y)).mpr (by simpa using hy)
      · apply (L f).injective
        simpa only [hL, LinearEquiv.apply_symm_apply] using heq
  have hphi_exists (f : I) : ∃ φ : F.val.obj (op (D f)) ≃+ G.val.obj (op (D f)),
      ∀ s, B f (φ s) = L f (A f s) :=
    addEquiv_of_matching_ranges (A f) (B f)
      (halpha f.val.1 f.val.2 f.property.1 f.property.2).1
      (hbeta f.val.1 f.val.2 f.property.1 f.property.2).1 (L f).toAddEquiv (hrange f)
  choose phi hphi using hphi_exists
  have hphiScalar (f : I) (q : (Proj 𝒜).presheaf.obj (op (D f)))
      (s : F.val.obj (op (D f))) : phi f (q • s) = q • phi f s := by
    let Riso := basicOpenIsoAway 𝒜 f.val.1 f.property.2 f.property.1
    obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso Riso.hom).2 q
    apply (hbeta f.val.1 f.val.2 f.property.1 f.property.2).1
    rw [hphi]
    change L f (A f (awayToSection 𝒜 f.val.1 r • s)) =
      B f (awayToSection 𝒜 f.val.1 r • phi f s)
    rw [hscalar, hbetaScalar, hphi, map_smul]
  let lin (f : I) : F.val.obj (op (D f)) ≃ₗ[(Proj 𝒜).presheaf.obj (op (D f))]
      G.val.obj (op (D f)) :=
    { phi f with map_smul' := hphiScalar f }
  have hlin (f g : I) (inc : D g ≤ D f) (s : F.val.obj (op (D f))) :
      lin g (F.val.map (homOfLE inc).op s) =
        G.val.map (homOfLE inc).op (lin f s) := by
    have hrelation : ∃ (e' c : ℕ) (a : S),
        0 < e' ∧ a ∈ 𝒜 c ∧ g.val.1 ^ e' = a * f.val.1 :=
      ((standardOpenProperties.{u, u, u} 𝒜).2.2.1 f.val.1 g.val.1 f.val.2 g.val.2
        f.property.1 g.property.1 f.property.2 g.property.2).1.mp inc
    obtain ⟨e', c, a, he', ha, hrel⟩ := hrelation
    exact away_chart_map_naturality f.val.1 g.val.1 e.toLinearMap
      (A f) (A g) (B f) (B g) (lin f) (lin g) (L f) (L g)
      (hbeta g.val.1 g.val.2 g.property.1 g.property.2).1
      (hphi f) (hphi g) (hL f) (hL g)
      (F.val.map (homOfLE inc).op) (G.val.map (homOfLE inc).op) a e'
      (hres f.val.1 g.val.1 f.val.2 g.val.2 f.property.1 g.property.1
        f.property.2 g.property.2 inc e' c a he' ha hrel)
      (hbetaRes f.val.1 g.val.1 f.val.2 g.val.2 f.property.1 g.property.1
        f.property.2 g.property.2 inc e' c a he' ha hrel) s
  let basis := Set.range D
  have hBasis : Opens.IsBasis basis := by
    convert (standardOpenProperties.{u, u, u} 𝒜).1 using 1
    ext U
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f.val.1, f.val.2, f.property.1, f.property.2, rfl⟩
    · rintro ⟨f, n, hn, hf, rfl⟩
      exact ⟨⟨⟨f, n⟩, hn, hf⟩, rfl⟩
  have hcap (U V : basis) : U.val ⊓ V.val ∈ basis := by
    obtain ⟨f, hf⟩ := U.property
    obtain ⟨g, hg⟩ := V.property
    refine ⟨⟨⟨f.val.1 * g.val.1, f.val.2 + g.val.2⟩,
      by omega, SetLike.mul_mem_graded f.property.2 g.property.2⟩, ?_⟩
    rw [← hf, ← hg]
    exact ((standardOpenProperties.{u, u, u} 𝒜).2.1 f.val.1 g.val.1 f.val.2 g.val.2
      f.property.1 g.property.1 f.property.2 g.property.2).symm
  have hrefine (U : basis) (C : Set basis) (_hC : ∀ V ∈ C, V.val ≤ U.val)
      (hcover : (⨆ V ∈ C, V.val) = U.val) :
      ∃ (n : ℕ) (W : Fin n → basis), (⨆ i, (W i).val) = U.val ∧
        ∀ i, ∃ V ∈ C, (W i).val ≤ V.val := by
    obtain ⟨f, hf⟩ := U.property
    have hcover' : (⨆ V : C, V.val.val) = D f := by
      simpa only [iSup_subtype, hf] using hcover
    obtain ⟨n, g, t, ht, hgt, hsub⟩ := (standardOpenProperties.{u, u, u} 𝒜).2.2.2.1
      f.val.1 f.val.2 f.property.1 f.property.2 C (fun V ↦ V.val.val) hcover'
    let W (i : Fin n) : basis :=
      ⟨basicOpen 𝒜 (g i), ⟨⟨⟨g i, t i⟩, ht i⟩, rfl⟩⟩
    refine ⟨n, W, ?_, ?_⟩
    · exact hgt.symm.trans hf
    · intro i
      obtain ⟨V, hV⟩ := hsub i
      exact ⟨V.val, V.property, hV⟩
  exact iso_of_indexed_basis (Proj 𝒜).toTopCat (Proj 𝒜).ringCatSheaf
    D hBasis hcap hrefine F G lin hlin

end AlgebraicGeometry.Proj

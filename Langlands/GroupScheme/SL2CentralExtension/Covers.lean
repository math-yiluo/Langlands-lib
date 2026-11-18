import Langlands.GroupScheme.SL2CentralExtension.Local
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.AdjoinRoot

/-! # Fppf covers adjoining roots of monic polynomials and inverting polynomials -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace Langlands.GroupScheme.SL2CentralExtension

variable {S : Scheme.{u}}

/-- The ring map on global sections induced by a morphism of schemes over `S`. -/
abbrev ring {V T : Over S} (g : V ⟶ T) : Γ(T.left, ⊤) →+* Γ(V.left, ⊤) := g.left.appTop.hom

theorem ring_comp {W V T : Over S} (k : W ⟶ V) (g : V ⟶ T) :
    ring (k ≫ g) = (ring k).comp (ring g) := rfl

theorem ring_comp_apply {W V T : Over S} (k : W ⟶ V) (g : V ⟶ T) (a : Γ(T.left, ⊤)) :
    ring (k ≫ g) a = ring k (ring g a) := rfl

/-- A polynomial is *nowhere degenerate* if it does not vanish modulo any prime of the
coefficient ring, i.e. its coefficients generate the unit ideal. -/
def Nondeg {A : Type*} [CommRing A] (f : A[X]) : Prop :=
  ∀ P : Ideal A, P.IsPrime → f ∉ Ideal.map C P

namespace Nondeg

variable {A A' : Type*} [CommRing A] [CommRing A']

theorem of_coeff {f : A[X]} (n : ℕ) (h : IsUnit (f.coeff n)) : Nondeg f := by
  intro P hP hf
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_C_iff.mp hf n) h)

theorem of_coeff₂ {f : A[X]} (i j : ℕ) (a b : A) (h : a * f.coeff i + b * f.coeff j = 1) :
    Nondeg f := by
  intro P hP hf
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← h]
  exact P.add_mem (P.mul_mem_left _ (Ideal.mem_map_C_iff.mp hf i))
    (P.mul_mem_left _ (Ideal.mem_map_C_iff.mp hf j))

theorem mul {f g : A[X]} (hf : Nondeg f) (hg : Nondeg g) : Nondeg (f * g) := by
  intro P hP hfg
  have : (Ideal.map (C : A →+* A[X]) P).IsPrime := @Ideal.isPrime_map_C_of_isPrime _ _ P hP
  rcases this.mem_or_mem hfg with h | h
  · exact hf P hP h
  · exact hg P hP h

theorem map {f : A[X]} (hf : Nondeg f) (ρ : A →+* A') : Nondeg (f.map ρ) := by
  intro P hP hfP
  apply hf (P.comap ρ) (Ideal.comap_isPrime ρ P)
  rw [Ideal.mem_map_C_iff] at hfP ⊢
  intro n
  rw [Ideal.mem_comap]
  simpa [Polynomial.coeff_map] using hfP n

theorem monic {f : A[X]} (hf : f.Monic) : Nondeg f :=
  of_coeff f.natDegree (by rw [Polynomial.coeff_natDegree, hf.leadingCoeff]; exact isUnit_one)

end Nondeg

/-- Inverting a nowhere degenerate polynomial in `A[X]` is faithfully flat over `A`. -/
theorem localizationAway_faithfullyFlat {A : Type u} [CommRing A] {f : A[X]} (hf : Nondeg f) :
    Module.FaithfullyFlat A (Localization.Away f) := by
  refine Module.FaithfullyFlat.of_comap_surjective ?_
  intro p
  have hP := p.isPrime
  let Q : Ideal A[X] := Ideal.map C p.asIdeal
  have hQ : Q.IsPrime := @Ideal.isPrime_map_C_of_isPrime _ _ p.asIdeal hP
  have hdisj : Disjoint (Submonoid.powers f : Set A[X]) Q := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hf p.asIdeal hP (hQ.mem_of_pow_mem n hn)
  let Q' : Ideal (Localization.Away f) := Q.map (algebraMap A[X] (Localization.Away f))
  have hQ' : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) _ Q
    hQ hdisj
  refine ⟨⟨Q', hQ'⟩, ?_⟩
  ext a
  change a ∈ Ideal.comap (algebraMap A (Localization.Away f)) Q' ↔ a ∈ p.asIdeal
  have hQQ : Ideal.comap (algebraMap A[X] (Localization.Away f)) Q' = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) (Localization.Away f) hQ
      hdisj
  rw [IsScalarTower.algebraMap_eq A A[X] (Localization.Away f), ← Ideal.comap_comap, hQQ,
    Ideal.mem_comap, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h n
    rw [Polynomial.coeff_C]
    split_ifs
    · exact h
    · exact p.asIdeal.zero_mem

/-- Adjoining a root of a monic polynomial of positive degree is faithfully flat. -/
theorem adjoinRoot_faithfullyFlat {A : Type u} [CommRing A] {p : A[X]} (hp : p.Monic)
    (hdeg : Nontrivial A → 0 < p.natDegree) : (algebraMap A (AdjoinRoot p)).FaithfullyFlat := by
  cases subsingleton_or_nontrivial A with
  | inl h =>
    have : Subsingleton (AdjoinRoot p) := subsingleton_of_zero_eq_one (by
      rw [← (algebraMap A (AdjoinRoot p)).map_zero, ← (algebraMap A (AdjoinRoot p)).map_one,
        Subsingleton.elim (0 : A) 1])
    exact RingHom.FaithfullyFlat.of_bijective
      ⟨Function.injective_of_subsingleton _, fun x => ⟨0, Subsingleton.elim _ _⟩⟩
  | inr h =>
    have : Module.Free A (AdjoinRoot p) := hp.free_adjoinRoot
    have hinj : Function.Injective (algebraMap A (AdjoinRoot p)) :=
      AdjoinRoot.of.injective_of_monic_of_degree_pos hp
        (Polynomial.natDegree_pos_iff_degree_pos.mp (hdeg h))
    have : Nontrivial (AdjoinRoot p) := hinj.nontrivial
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

namespace Loc

/-- Over an affine test scheme, a faithfully flat finitely presented algebra of global
sections gives an fppf-local factorization of the global-sections map. -/
theorem of_algebra {T : Over S} [IsAffine T.left] {B : CommRingCat.{u}}
    (φ : Γ(T.left, ⊤) ⟶ B) (hφ : φ.hom.FaithfullyFlat) (hfp : φ.hom.FinitePresentation) :
    Loc (fun V (g : V ⟶ T) => ∃ ψ : B ⟶ Γ(V.left, ⊤), φ ≫ ψ = g.left.appTop) := by
  let j₀ : Spec B ⟶ T.left := Spec.map φ ≫ T.left.isoSpec.inv
  let W : Over S := Over.mk (j₀ ≫ T.hom)
  let j : W ⟶ T := Over.homMk j₀
  have hflat := (flat_and_surjective_SpecMap_iff φ).mpr hφ
  have : Flat (Spec.map φ) := hflat.1
  have : Surjective (Spec.map φ) := hflat.2
  have : LocallyOfFinitePresentation (Spec.map φ) :=
    (LocallyOfFinitePresentation.SpecMap_iff φ).mpr hfp
  have : Flat j.left := inferInstanceAs (Flat j₀)
  have : Surjective j.left := inferInstanceAs (Surjective j₀)
  have : LocallyOfFinitePresentation j.left := inferInstanceAs (LocallyOfFinitePresentation j₀)
  have hiso : T.left.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(T.left, ⊤)).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso Γ(T.left, ⊤)).hom, Iso.inv_hom_id,
      ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv,
      Scheme.Hom.id_appTop]
  have hj : j.left.appTop = φ ≫ (Scheme.ΓSpecIso B).inv := by
    change (Spec.map φ ≫ T.left.isoSpec.inv).appTop = _
    rw [Scheme.Hom.comp_appTop, hiso, Scheme.ΓSpecIso_inv_naturality]
  refine (Loc.of_single j).mono ?_
  rintro V g ⟨k, rfl⟩
  refine ⟨(Scheme.ΓSpecIso B).inv ≫ k.left.appTop, ?_⟩
  rw [Over.comp_left, Scheme.Hom.comp_appTop, hj, Category.assoc]

/-- Fppf-locally, a nowhere degenerate polynomial takes a unit value. -/
theorem exists_isUnit_eval {T : Over S} (f : Γ(T.left, ⊤)[X]) (hf : Nondeg f) :
    Loc (fun V (g : V ⟶ T) => ∃ r : Γ(V.left, ⊤), IsUnit ((f.map (ring g)).eval r)) := by
  refine Loc.of_affine fun V g hV => ?_
  let A := Γ(V.left, ⊤)
  let f' : A[X] := f.map (ring g)
  have hf' : Nondeg f' := hf.map _
  let B := CommRingCat.of (Localization.Away f')
  let φ : A ⟶ B := CommRingCat.ofHom (algebraMap A (Localization.Away f'))
  have hφ : φ.hom.FaithfullyFlat := by
    have := localizationAway_faithfullyFlat hf'
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr this
  have hfp : φ.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr inferInstance
  refine (Loc.of_algebra φ hφ hfp).mono ?_
  rintro W k ⟨ψ, hψ⟩
  refine ⟨ψ.hom (algebraMap A[X] (Localization.Away f') X), ?_⟩
  have hunit : IsUnit (algebraMap A[X] (Localization.Away f') f') :=
    IsLocalization.Away.algebraMap_isUnit f'
  convert hunit.map ψ.hom using 1
  have hk : ring k = ψ.hom.comp (algebraMap A (Localization.Away f')) := by
    change (Scheme.Hom.appTop k.left).hom = _
    rw [← hψ]
    rfl
  rw [ring_comp, ← Polynomial.map_map, Polynomial.eval_map]
  change f'.eval₂ (ring k) _ = _
  rw [hk, ← Polynomial.hom_eval₂]
  congr 1
  exact Polynomial.eval₂_algebraMap_X f' (IsScalarTower.toAlgHom A A[X] (Localization.Away f'))

/-- Fppf-locally, a monic polynomial of positive degree has a root. -/
theorem exists_root {T : Over S} (p : Γ(T.left, ⊤)[X]) (hp : p.Monic) (hdeg : 0 < p.natDegree) :
    Loc (fun V (g : V ⟶ T) => ∃ r : Γ(V.left, ⊤), (p.map (ring g)).eval r = 0) := by
  refine Loc.of_affine fun V g hV => ?_
  let A := Γ(V.left, ⊤)
  let p' : A[X] := p.map (ring g)
  have hp' : p'.Monic := hp.map _
  have hdeg' : Nontrivial A → 0 < p'.natDegree := fun _ => by
    rw [hp.natDegree_map]; exact hdeg
  let B := CommRingCat.of (AdjoinRoot p')
  let φ : A ⟶ B := CommRingCat.ofHom (algebraMap A (AdjoinRoot p'))
  have hfp : φ.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr inferInstance
  refine (Loc.of_algebra φ (adjoinRoot_faithfullyFlat hp' hdeg') hfp).mono ?_
  rintro W k ⟨ψ, hψ⟩
  refine ⟨ψ.hom (AdjoinRoot.root p'), ?_⟩
  have h0 : p'.eval₂ (algebraMap A (AdjoinRoot p')) (AdjoinRoot.root p') = 0 :=
    AdjoinRoot.eval₂_root p'
  rw [ring_comp, ← Polynomial.map_map, Polynomial.eval_map]
  change p'.eval₂ (ring k) _ = 0
  have : ring k = ψ.hom.comp (algebraMap A (AdjoinRoot p')) := by
    change (Scheme.Hom.appTop k.left).hom = _
    rw [← hψ]
    rfl
  rw [this, ← Polynomial.hom_eval₂, h0, map_zero]

end Loc

end Langlands.GroupScheme.SL2CentralExtension

import Langlands.CommutativeAlgebra.EtaleLocalSections

/-! # Etale local sections of smooth surjective scheme morphisms -/

universe u

open CategoryTheory Limits

noncomputable section

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry Langlands.CommutativeAlgebra.EtaleLocalSections

/-- A morphism of schemes `f : W ⟶ T` has etale local sections if some surjective etale
morphism `e : V ⟶ T` factors through `f`. -/
def HasEtaleLocalSections {W T : Scheme.{u}} (f : W ⟶ T) : Prop :=
  ∃ (V : Scheme.{u}) (e : V ⟶ T) (s : V ⟶ W), Etale e ∧ Surjective e ∧ s ≫ f = e

/-- A smooth algebra has, near each of its points, a section over an etale algebra: for every
prime `p` of `S` there are an etale `R`-algebra `R'`, an `R`-algebra map `S → R'`, and a prime
of `R'` over the same prime of `R` as `p`. -/
theorem exists_etale_algHom_of_smooth {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (p : Ideal S) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'), Algebra.Etale R R' ∧
      Nonempty (S →ₐ[R] R') ∧
      ∃ 𝔮' : Ideal R', 𝔮'.IsPrime ∧ 𝔮'.comap (algebraMap R R') = p.comap (algebraMap R S) := by
  obtain ⟨g, hg, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
  let Sg := Localization.Away g
  let 𝔮 : Ideal Sg := p.map (algebraMap S Sg)
  have h𝔮 : 𝔮.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers g) Sg p ‹_›
    ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hg)
  have h𝔮c : 𝔮.comap (algebraMap S Sg) = p := IsLocalization.under_map_of_isPrime_disjoint
    (.powers g) Sg ‹_› ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hg)
  obtain ⟨R', _, _, hR', ⟨ψ⟩, 𝔮', h𝔮', hc⟩ := exists_etale_algHom_of_isStandardEtale (R := R) (n := n) (S := Sg) 𝔮
  refine ⟨R', inferInstance, inferInstance, hR', ⟨ψ.comp (IsScalarTower.toAlgHom R S Sg)⟩, 𝔮',
    h𝔮', ?_⟩
  rw [hc, IsScalarTower.algebraMap_eq R S Sg, ← Ideal.comap_comap, h𝔮c]

/-- Every point of the source of a smooth morphism of schemes lies over the image of an affine
etale scheme over the target which maps to the source over the target. -/
theorem exists_etale_spec_of_smooth {W T : Scheme.{u}} (f : W ⟶ T) [Smooth f] (x : W) :
    ∃ (R' : CommRingCat.{u}) (e : Spec R' ⟶ T) (s : Spec R' ⟶ W),
      Etale e ∧ f x ∈ Set.range e ∧ s ≫ f = e := by
  obtain ⟨U, hU, V, hV, hxV, hle, -⟩ := Smooth.exists_isStandardSmooth f x
  have hsm := f.smooth_appLE hU hV hle
  let φ := (f.appLE U V hle).hom
  let : Algebra Γ(T, U) Γ(W, V) := φ.toAlgebra
  have : Algebra.Smooth Γ(T, U) Γ(W, V) := RingHom.smooth_algebraMap.mp hsm
  let px := hV.primeIdealOf ⟨x, hxV⟩
  obtain ⟨R', _, _, hR', ⟨ψ⟩, 𝔮', h𝔮', hc⟩ := exists_etale_algHom_of_smooth (R := Γ(T, U)) (S := Γ(W, V)) px.asIdeal
  let e : Spec (CommRingCat.of R') ⟶ T :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) R')) ≫ hU.fromSpec
  have hψ : f.appLE U V hle ≫ CommRingCat.ofHom ψ.toRingHom =
      CommRingCat.ofHom (algebraMap Γ(T, U) R') := by
    ext a
    exact ψ.commutes a
  refine ⟨CommRingCat.of R', e, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ?_,
    ?_⟩
  · have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) R'))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hR')
    infer_instance
  · refine ⟨⟨𝔮', h𝔮'⟩, ?_⟩
    have hpt : Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) R')) ⟨𝔮', h𝔮'⟩ =
        Spec.map (f.appLE U V hle) px := PrimeSpectrum.ext hc
    change hU.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, U) R')) ⟨𝔮', h𝔮'⟩) = f x
    rw [hpt]
    calc hU.fromSpec (Spec.map (f.appLE U V hle) px)
        = (Spec.map (f.appLE U V hle) ≫ hU.fromSpec) px := rfl
      _ = (hV.fromSpec ≫ f) px := by rw [IsAffineOpen.SpecMap_appLE_fromSpec]
      _ = f x := congrArg f (hV.fromSpec_primeIdealOf ⟨x, hxV⟩)
  · rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hle, ← Category.assoc,
      ← Spec.map_comp, hψ]

/-- **Etale local sections (Stacks 055U).** Every smooth surjective morphism of schemes has a
section after pullback along a single surjective etale morphism of schemes. -/
theorem hasEtaleLocalSections_of_smooth {W T : Scheme.{u}} (f : W ⟶ T) [Smooth f]
    [Surjective f] : HasEtaleLocalSections f := by
  have key : ∀ t : T, ∃ (R' : CommRingCat.{u}) (e : Spec R' ⟶ T) (s : Spec R' ⟶ W),
      Etale e ∧ t ∈ Set.range e ∧ s ≫ f = e := by
    intro t
    obtain ⟨x, rfl⟩ := Surjective.surj (f := f) t
    exact exists_etale_spec_of_smooth f x
  choose R' e s he ht hfac using key
  refine ⟨∐ fun t => Spec (R' t), Sigma.desc e, Sigma.desc s, ?_, ?_, ?_⟩
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) he
  · refine Surjective.sigmaDesc_of_union_range_eq_univ ?_
    exact Set.eq_univ_iff_forall.mpr fun t => Set.mem_iUnion.mpr ⟨t, ht t⟩
  · ext1 t
    simp [hfac]

end Langlands.AlgebraicGeometry

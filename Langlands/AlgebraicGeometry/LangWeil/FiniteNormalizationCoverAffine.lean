import Langlands.AlgebraicGeometry.LangWeil.FiniteNormalizationCoverPieces

/-! # Finite normalization pieces of affine morphisms

For a finite-type algebra `A` over a Noetherian ring `R`, finitely many pieces cover every
field-valued point of `Spec A`. Each piece comes from a prime `Q` of `A`: generic Noether
normalization of `A ⧸ Q` over `R ⧸ (Q ∩ R)`, after inverting one element. -/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil.NormalizationCoverConstruction

/-- A finite injective polynomial map between localizations of quotients gives a piece of
`Spec A → Spec R`. It covers every field-valued point whose kernel contains the kernel of
`A → C` and avoids `g`. -/
theorem exists_piece_of_finite_injective {R A D C D' C' : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [CommRing D] [CommRing C] [Algebra D C] (πR : R →+* D)
    (hπR : Function.Surjective πR) (πA : A →+* C) (hπA : Function.Surjective πA)
    (hcomm : (algebraMap D C).comp πR = πA.comp (algebraMap R A)) (r : D)
    [CommRing D'] [CommRing C'] [Algebra D D'] [IsLocalization.Away r D']
    [Algebra C C'] [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) C']
    [Algebra D' C'] [Algebra D C'] [IsScalarTower D D' C'] [IsScalarTower D C C']
    {d : ℕ} (ψ : MvPolynomial (ULift.{u} (Fin d)) D' →ₐ[D'] C') (hfin : ψ.toRingHom.Finite)
    (hinj : Function.Injective ψ) (g : A) (hg : πA g = algebraMap D C r) :
    ∃ p : Piece (Spec.map (CommRingCat.ofHom (algebraMap R A))),
      ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ Spec (.of A)),
        RingHom.ker πA ≤ RingHom.ker (Spec.preimage x).hom →
        (Spec.preimage x).hom g ≠ 0 → ∃ z : Spec (.of K) ⟶ p.source, z ≫ p.sourceMap = x := by
  have hloc : IsLocalization.Away (algebraMap D C r) C' := by
    have h := (inferInstance :
      IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) C')
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at h
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C C'))) :=
    IsOpenImmersion.of_isLocalization (algebraMap D C r)
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap D D'))) :=
    IsOpenImmersion.of_isLocalization r
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom πA)) :=
    IsClosedImmersion.spec_of_surjective _ hπA
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom πR)) :=
    IsClosedImmersion.spec_of_surjective _ hπR
  have : IsFinite (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
    (IsFinite.SpecMap_iff _).mpr hfin
  have hint : ψ.toRingHom.IsIntegral := hfin.to_isIntegral
  have : Surjective (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
    ⟨hint.comap_surjective hinj⟩
  have hπ : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin d)) (.of D')).inv) ≫
        (AffineSpace (ULift.{u} (Fin d)) (Spec (.of D')) ↘ Spec (.of D')) =
      Spec.map (CommRingCat.ofHom (algebraMap D' C')) := by
    rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap
  refine ⟨{
    base := Spec (.of D')
    source := Spec (.of C')
    baseAffine := inferInstance
    baseMap := Spec.map (CommRingCat.ofHom (algebraMap D D')) ≫ Spec.map (CommRingCat.ofHom πR)
    baseImmersion := inferInstance
    sourceMap :=
      Spec.map (CommRingCat.ofHom (algebraMap C C')) ≫ Spec.map (CommRingCat.ofHom πA)
    sourceImmersion := inferInstance
    dimension := d
    normalization := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin d)) (.of D')).inv
    normalizationFinite := inferInstance
    normalizationSurjective := (inferInstance : Surjective (Spec.map (CommRingCat.ofHom
      ψ.toRingHom) ≫ (AffineSpace.SpecIso (ULift.{u} (Fin d)) (.of D')).inv)).surj
    comm := by
      rw [← Category.assoc, hπ]
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      rw [RingHom.comp_assoc, ← hcomm, ← RingHom.comp_assoc, ← RingHom.comp_assoc,
        ← IsScalarTower.algebraMap_eq D D' C', ← IsScalarTower.algebraMap_eq D C C']
    fibreChain := by
      intro t
      obtain ⟨L, hlen, hL⟩ := exists_ltSeries_fibre ψ hint hinj t
      let e : Fin (d + 1) → Fin (L.length + 1) := Fin.cast (by rw [hlen])
      refine ⟨fun i => L (e i), fun i => ?_, fun i => ?_⟩
      · rw [hπ]
        exact hL (e i)
      · have hlt : L (e i.castSucc) < L (e i.succ) :=
          L.strictMono (by simp [e, Fin.lt_def])
        exact ⟨(PrimeSpectrum.le_iff_specializes _ _).mp hlt.le, hlt.ne⟩ }, ?_⟩
  intro K _ x hker hgx
  let χ : C →+* K := πA.liftOfSurjective hπA ⟨(Spec.preimage x).hom, hker⟩
  have hχ : ∀ a, χ (πA a) = (Spec.preimage x).hom a :=
    πA.liftOfSurjective_comp_apply hπA ⟨(Spec.preimage x).hom, hker⟩
  have hunit : ∀ m : Algebra.algebraMapSubmonoid C (Submonoid.powers r), IsUnit (χ m) := by
    rintro ⟨_, _, ⟨n, rfl⟩, rfl⟩
    change IsUnit (χ (algebraMap D C (r ^ n)))
    rw [map_pow, map_pow, ← hg, hχ]
    exact (Ne.isUnit hgx).pow n
  let ℓ : C' →+* K := IsLocalization.lift hunit
  refine ⟨Spec.map (CommRingCat.ofHom ℓ), ?_⟩
  conv_rhs => rw [← Spec.map_preimage x]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext a
  simp [ℓ, hχ]

/-- Every prime `Q` of a finite-type algebra has an element `g ∉ Q` and a piece of
`Spec A → Spec R` covering every field-valued point whose kernel contains `Q` and
avoids `g`. -/
theorem exists_piece {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (Q : Ideal A) [Q.IsPrime] :
    ∃ g ∉ Q, ∃ p : Piece (Spec.map (CommRingCat.ofHom (algebraMap R A))),
      ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ Spec (.of A)),
        Q ≤ RingHom.ker (Spec.preimage x).hom → (Spec.preimage x).hom g ≠ 0 →
          ∃ z : Spec (.of K) ⟶ p.source, z ≫ p.sourceMap = x := by
  have : Algebra.FiniteType (R ⧸ Q.under R) (A ⧸ Q) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ Q.under R) (A ⧸ Q)
  obtain ⟨r, hr, d, ψ, hfin, hinj⟩ :=
    exists_away_finite_injective (D := R ⧸ Q.under R) (C := A ⧸ Q)
  obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨algebraMap R A r₀, fun h => hr (Ideal.Quotient.eq_zero_iff_mem.mpr h), ?_⟩
  obtain ⟨p, hp⟩ := exists_piece_of_finite_injective (Ideal.Quotient.mk (Q.under R))
    Ideal.Quotient.mk_surjective (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
    (RingHom.ext fun a => Ideal.Quotient.algebraMap_mk_of_liesOver Q (Q.under R) a) _ ψ hfin hinj
    (algebraMap R A r₀) (Ideal.Quotient.algebraMap_mk_of_liesOver Q (Q.under R) r₀).symm
  refine ⟨p, fun K _ x hQ hg => hp K x ?_ hg⟩
  rwa [Ideal.mk_ker]

/-- Finitely many pieces cover every field-valued point of `Spec A → Spec R`, for a
finite-type algebra `A` over a Noetherian ring `R`. -/
theorem exists_finite_affine_pieces (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [Algebra.FiniteType R A] :
    ∃ s : Set (Piece (Spec.map (CommRingCat.ofHom (algebraMap R A)))), s.Finite ∧
      ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ Spec (.of A)),
        ∃ p ∈ s, ∃ z : Spec (.of K) ⟶ p.source, z ≫ p.sourceMap = x := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  obtain ⟨s, hs, hcov⟩ := exists_finite_cover_of_prime
    (fun (p : Piece (Spec.map (CommRingCat.ofHom (algebraMap R A)))) (P : Ideal A) =>
      ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ Spec (.of A)),
        RingHom.ker (Spec.preimage x).hom = P →
          ∃ z : Spec (.of K) ⟶ p.source, z ≫ p.sourceMap = x)
    (fun Q _ => by
      obtain ⟨g, hg, p, hp⟩ := exists_piece (R := R) Q
      refine ⟨g, hg, p, fun P _ hQP hgP K _ x hx => hp K x (hx ▸ hQP) fun h => ?_⟩
      exact hgP (hx ▸ (RingHom.mem_ker.mpr h)))
  refine ⟨s, hs, fun K _ x => ?_⟩
  obtain ⟨p, hp, hc⟩ := hcov (RingHom.ker (Spec.preimage x).hom) (RingHom.ker_isPrime _)
  exact ⟨p, hp, hc K x rfl⟩

end Langlands.AlgebraicGeometry.LangWeil.NormalizationCoverConstruction

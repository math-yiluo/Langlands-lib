import Langlands.AlgebraicGeometry.FiniteEtale.TameConjugationStatement
import Langlands.AlgebraicGeometry.FiniteEtale.TameGaloisRealization
import Langlands.AlgebraicGeometry.FiniteEtale.TameRootSection
import Langlands.AlgebraicGeometry.FiniteEtale.ConnectedCoverFiber
import Langlands.AlgebraicGeometry.FiniteEtale.KummerCover
import Langlands.AlgebraicGeometry.FiniteEtale.StrictLocalCover
import Langlands.CommutativeAlgebra.HenselianCyclotomicExtension

/-! # Proof of tame conjugation along a regular local divisor -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace Langlands.AlgebraicGeometry.FiniteEtale

namespace TameConjugation

open KummerCover

/-- `fundamentalGroupMap` only depends on the morphism, transported along an equality. -/
theorem fundamentalGroupMap_congr {S S' : Scheme.{u}} {Ω : Type u} [Field Ω] {f f' : S' ⟶ S}
    (e : f = f') (t : Spec (.of Ω) ⟶ S') (s : Spec (.of Ω) ⟶ S) (h : t ≫ f = s)
    (ht : ∀ Y : Cover S', Finite (Fiber t Y)) (hs : ∀ Y : Cover S, Finite (Fiber s Y)) :
    fundamentalGroupMap f t s h ht hs = fundamentalGroupMap f' t s (e ▸ h) ht hs := by
  subst e
  rfl

/-- `R → R[1/t] → L` is `R → W → L`. -/
theorem traitGenericRingHom_comp {R W : Type u} (L : Type u) [CommRing R] [CommRing W]
    [IsDomain W] [Field L] [Algebra R W] [Algebra W L] [IsFractionRing W L] (t : R)
    (ht : algebraMap R W t ≠ 0) :
    (traitGenericRingHom L t ht).comp (algebraMap R (Localization.Away t)) =
      (algebraMap W L).comp (algebraMap R W) :=
  IsLocalization.Away.lift_comp _ _

/-- The composite `Spec L ⟶ Spec R[1/t] ⟶ Spec R` is `Spec L ⟶ Spec W ⟶ Spec R`. -/
theorem traitGenericMorphism_comp {R W : Type u} (L : Type u) [CommRing R] [CommRing W]
    [IsDomain W] [Field L] [Algebra R W] [Algebra W L] [IsFractionRing W L] (t : R)
    (ht : algebraMap R W t ≠ 0) :
    traitGenericMorphism L t ht ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t))) =
      Spec.map (CommRingCat.ofHom (algebraMap W L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R W)) := by
  unfold traitGenericMorphism
  rw [specMap_comp, specMap_comp, traitGenericRingHom_comp]

/-- **Trivial action through a strictly Henselian trait.** The image in `π₁(Spec R[1/t])` of an
element of `π₁(Spec L)` acts trivially on the geometric fibre of `Spec R'[1/t]`, for a finite
étale `R`-algebra `R'`: this cover extends to the cover `Spec R'` of `Spec R`, and the action
factors through the trivial group `π₁(Spec W)`. -/
theorem smul_coverU_eq {R : Type u} [CommRing R] (t : R) {W L : Type u} [CommRing W]
    [IsDomain W] [HenselianLocalRing W] [IsSepClosed (ResidueField W)] [Field L] [Algebra W L]
    [IsFractionRing W L] [Algebra R W] (ht : algebraMap R W t ≠ 0) {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of L)) (R' : Type u) [CommRing R']
    [Algebra R R'] [Module.Finite R R'] [Algebra.Etale R R']
    (g : FundamentalGroup s (geometricFiberFinite s))
    (ψ : Fiber (s ≫ traitGenericMorphism L t ht) (coverU t R')) :
    fundamentalGroupMap (traitGenericMorphism L t ht) s (s ≫ traitGenericMorphism L t ht) rfl
      (geometricFiberFinite s) (geometricFiberFinite _) g • ψ = ψ := by
  let j := traitGenericMorphism L t ht
  let i := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t)))
  let jL := Spec.map (CommRingCat.ofHom (algebraMap W L))
  let πW := Spec.map (CommRingCat.ofHom (algebraMap R W))
  have hji : j ≫ i = jL ≫ πW := traitGenericMorphism_comp L t ht
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  let Y₀ : Cover (Spec (.of R)) := cover (Spec.map (CommRingCat.ofHom (algebraMap R R')))
  let φ : (coverU t R').obj.left ⟶ Y₀.obj.left :=
    Spec.map (CommRingCat.ofHom (algebraMap R' (Loc t R')))
  have hφ : φ ≫ Y₀.obj.hom = (coverU t R').obj.hom ≫ i := (projU_comp t R').symm
  let x₀ : Fiber ((s ≫ j) ≫ i) Y₀ := Over.homMk (ψ.left ≫ φ) (by
    change (ψ.left ≫ φ) ≫ Y₀.obj.hom = (s ≫ j) ≫ i
    rw [Category.assoc, hφ, ← Category.assoc, Over.w ψ]
    rfl)
  have key := fundamentalGroupMap_smul_left_of_comp i (s ≫ j) ((s ≫ j) ≫ i) rfl
    (geometricFiberFinite _) (geometricFiberFinite _)
    (fundamentalGroupMap j s (s ≫ j) rfl (geometricFiberFinite s) (geometricFiberFinite _) g)
    x₀ ψ φ hφ rfl
  have htriv : fundamentalGroupMap i (s ≫ j) ((s ≫ j) ≫ i) rfl (geometricFiberFinite _)
      (geometricFiberFinite _)
      (fundamentalGroupMap j s (s ≫ j) rfl (geometricFiberFinite s) (geometricFiberFinite _) g) =
        1 := by
    rw [← MonoidHom.comp_apply, ← fundamentalGroupMap_comp i (s ≫ j) ((s ≫ j) ≫ i) rfl _ _ j s
      rfl (by rw [Category.assoc]) (geometricFiberFinite s), fundamentalGroupMap_congr hji,
      fundamentalGroupMap_comp πW (s ≫ jL) _
        (by rw [Category.assoc, ← hji, ← Category.assoc]) (geometricFiberFinite _)
        (geometricFiberFinite _) jL s rfl, MonoidHom.comp_apply]
    have : Subsingleton (FundamentalGroup (s ≫ jL) (geometricFiberFinite (s ≫ jL))) :=
      subsingleton_fundamentalGroup_of_strictLocal W _ _
    rw [Subsingleton.elim (fundamentalGroupMap jL s (s ≫ jL) rfl _ _ g) 1, map_one]
  rw [htriv, one_smul] at key
  apply Over.OverMorphism.ext
  rw [← cancel_mono φ]
  exact key.symm

/-- **A map from the Kummer cover to the Galois cover.** From a section `sB` of the Galois
cover over the punctured locus `V` of `Spec S[X]/(X ^ n - t)` and an `R`-algebra map `S → R'`,
the Kummer cover of `Spec R'[1/t]` maps to the Galois cover over `Spec R[1/t]`. -/
theorem exists_coverX_hom {R : Type u} [CommRing R] [IsRegularLocalRing R] (t : R)
    {G : Type (u + 1)} [Group G] [Finite G]
    (WA : Scheme.GaloisCover G (Spec (.of (Localization.Away t)))) (n : ℕ) (hn0 : n ≠ 0)
    (hn : IsUnit (n : R)) (S : CommRingCat.{u}) (a : CommRingCat.of R ⟶ S)
    (V : (Spec (.of (AdjoinRoot ((Polynomial.X : Polynomial S) ^ n -
      Polynomial.C (a.hom t))))).Opens)
    (hV : V = PrimeSpectrum.basicOpen (algebraMap S (AdjoinRoot ((Polynomial.X : Polynomial S) ^ n -
      Polynomial.C (a.hom t))) (a.hom t)))
    (sB : V.toScheme ⟶ WA.P)
    (hsB : sB ≫ WA.π ≫ TameRootSection.puncture t = V.ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (AdjoinRoot ((Polynomial.X : Polynomial S) ^ n -
        Polynomial.C (a.hom t))))) ≫ Spec.map a)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Algebra.Etale R R']
    (b : S →+* R') (hb : b.comp a.hom = algebraMap R R') :
    Nonempty (coverX t R' n hn0 hn ⟶ TameGaloisRealization.toCover WA) := by
  classical
  have hbt : b (a.hom t) = algebraMap R R' t := RingHom.congr_fun hb t
  have hroot : Polynomial.eval₂ ((AdjoinRoot.of (kummerPoly t R' n)).comp
      ((algebraMap R' (Loc t R')).comp b)) (AdjoinRoot.root (kummerPoly t R' n))
      ((Polynomial.X : Polynomial S) ^ n - Polynomial.C (a.hom t)) = 0 := by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, RingHom.comp_apply,
      RingHom.comp_apply, hbt, root_pow, sub_self]
  let hh := AdjoinRoot.lift ((AdjoinRoot.of (kummerPoly t R' n)).comp
      ((algebraMap R' (Loc t R')).comp b)) (AdjoinRoot.root (kummerPoly t R' n)) hroot
  have hhg (r : S) : hh (algebraMap S _ r) =
      AdjoinRoot.of (kummerPoly t R' n) (algebraMap R' (Loc t R') (b r)) := by
    rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
    rfl
  have hrange : Set.range (Spec.map (CommRingCat.ofHom hh)) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι, hV]
    rintro _ ⟨y, rfl⟩
    change algebraMap S _ (a.hom t) ∉ (PrimeSpectrum.comap hh y).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hhg, hbt]
    have hunit : IsUnit (AdjoinRoot.of (kummerPoly t R' n) (tt t R')) :=
      (isUnit_tt t R').map _
    exact fun hmem => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)
  let ι := IsOpenImmersion.lift V.ι (Spec.map (CommRingCat.ofHom hh)) hrange
  have hι : ι ≫ V.ι = Spec.map (CommRingCat.ofHom hh) := IsOpenImmersion.lift_fac _ _ _
  refine ⟨ObjectProperty.homMk (Over.homMk (ι ≫ sB) ?_)⟩
  change (ι ≫ sB) ≫ WA.π = projX t R' n ≫ projU t R'
  rw [← cancel_mono (TameRootSection.puncture t), Category.assoc, Category.assoc, hsB,
    ← Category.assoc, hι, show Spec.map a = Spec.map (CommRingCat.ofHom a.hom) from rfl,
    specMap_comp, specMap_comp, Category.assoc, specMap_comp, specMap_comp]
  congr 2
  ext r
  simp only [RingHom.comp_apply]
  have hbr : b (a.hom r) = algebraMap R R' r := RingHom.congr_fun hb r
  rw [hhg, hbr, ← RingHom.comp_apply (locHom t R'), locHom_comp,
    RingHom.comp_apply, AdjoinRoot.algebraMap_eq]

/-- Reassociation of a geometric point followed by two maps of covers. -/
theorem fib_comp {S : Scheme.{u}} {Ω : Type u} [Field Ω] {x : Spec (.of Ω) ⟶ S}
    {Y Z T : Cover S} (p : Fiber x Y) (f : Y ⟶ Z) (g : Z ⟶ T) :
    (p ≫ f.hom) ≫ g.hom = p ≫ (f ≫ g).hom := by
  rw [Category.assoc]
  rfl

/-- **The conjugation identity on a Kummer fibre.** Let `γ` act trivially on the geometric
fibre of `Spec R'[1/t]`, where `R'` carries a root of unity `ζ` of exact order `n` and an
endomorphism `α` with `α ζ = ζ ^ q`. Then some `σ` makes `(γ ^ q)⁻¹ * (σ * γ * σ⁻¹)` fix a
geometric point of the Kummer cover. -/
theorem exists_conj_fixed {R : Type u} [CommRing R] (t : R) (R' : Type u) [CommRing R']
    [IsDomain R'] [Algebra R R'] [Module.Finite R R'] [Algebra.Etale R R']
    (hinj : Function.Injective (algebraMap R R')) (ht : algebraMap R R' t ≠ 0)
    [ConnectedSpace (Spec (.of (Localization.Away t)))]
    [IsLocallyNoetherian (Spec (.of (Localization.Away t)))]
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R)) {ζ : R'} (hζn : ζ ^ n = 1)
    (hζ : ∀ l, 0 < l → l < n → IsUnit (ζ ^ l - 1)) (α : R' →ₐ[R] R') {q : ℕ}
    (hα : α ζ = ζ ^ q) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of (Localization.Away t)))
    (hx : ∀ Y : Cover _, Finite (Fiber x Y)) (γ : FundamentalGroup x hx)
    (hγ : ∀ ψ : Fiber x (coverU t R'), γ • ψ = ψ) :
    ∃ (σ : FundamentalGroup x hx) (p : Fiber x (coverX t R' n hn0 hn)),
      ((γ ^ q)⁻¹ * (σ * γ * σ⁻¹)) • p = p := by
  have : IsDomain (Loc t R') := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (M := Submonoid.powers (algebraMap R R' t)) (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have : ConnectedSpace (coverU t R').obj.left :=
    (inferInstance : ConnectedSpace (Spec (.of (Loc t R'))))
  obtain ⟨p⟩ := nonempty_fiber t R' hn0 hn hinj ht x
  let P := proj t R' n hn0 hn
  obtain ⟨c, hc⟩ := exists_eq_comp_K t R' hn0 hn hζn hζ p (γ • p) (by
    rw [← smul_naturality, hγ])
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_connectedSpace x hx (coverU t R') (p ≫ P.hom)
    (p ≫ P.hom ≫ (AU t R' α).hom)
  obtain ⟨d, hd⟩ := exists_eq_comp_K t R' hn0 hn hζn hζ (p ≫ (AX t R' n hn0 hn α).hom) (σ • p)
    (by
      rw [← smul_naturality, hσ, ← Category.assoc, fib_comp, fib_comp, AX_comp_proj])
  have hpow (m : ℕ) : (γ ^ m) • p = p ≫ (K t R' hn0 hn hζn (m * c)).hom := by
    induction m with
    | zero =>
      rw [pow_zero, one_smul, zero_mul, K_zero, ObjectProperty.FullSubcategory.id_hom,
        Category.comp_id]
    | succ m ih =>
      rw [pow_succ, mul_smul, hc, smul_naturality, ih, fib_comp, K_comp_K, add_mul, one_mul]
  have hrel : AX t R' n hn0 hn α ≫ K t R' hn0 hn hζn d ≫ K t R' hn0 hn hζn c =
      K t R' hn0 hn hζn (q * c) ≫ AX t R' n hn0 hn α ≫ K t R' hn0 hn hζn d := by
    rw [K_comp_K, ← Category.assoc, ← AX_comp_K t R' hn0 hn hζn α hα c, Category.assoc,
      K_comp_K, add_comm]
  refine ⟨σ, σ • p, ?_⟩
  rw [mul_smul, inv_smul_eq_iff, mul_smul, mul_smul, inv_smul_smul, hc, smul_naturality, hd,
    smul_naturality, smul_naturality, hpow, fib_comp, fib_comp, fib_comp, fib_comp, hrel]

end TameConjugation

open TameConjugation in
/-- **Tame conjugation along a regular local divisor.** Let `R` be a Henselian regular local
domain, `t ∈ 𝔪 \ 𝔪²` with `R/(t)` regular, and `ℓ` a prime invertible in `R`. Let `R → W` be a
local homomorphism to a strictly Henselian discrete valuation ring sending `t` to a uniformizer,
`L` the fraction field of `W`, `j : Spec L ⟶ Spec R[1/t]` the induced morphism and `s` a
geometric point of `Spec L`. Let `q` satisfy `CyclotomicPowerCondition (ResidueField R) ℓ q`
and let `ρ` be a continuous homomorphism from `π₁(Spec R[1/t], s ≫ j)` to a finite discrete
`ℓ`-group. Then for every `g ∈ π₁(Spec L, s)`, with image `jg` in `π₁(Spec R[1/t], s ≫ j)`,
some `σ ∈ π₁(Spec R[1/t], s ≫ j)` satisfies `ρ (σ * jg * σ⁻¹) = ρ jg ^ q`. -/
theorem regularDivisorTameConjugation : RegularDivisorTameConjugationStatement.{u, v} := by
  intro R _ _ _ _ t _ htm2 hreg ℓ _ hℓ W L _ _ _ _ _ _ _ _ _ _ ht Ω _ _ s q hq H _ _ _ _ hH j ρ
    hρ g jg
  classical
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact htm2 (Ideal.zero_mem _)
  have : IsDomain (Localization.Away t) := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (M := Submonoid.powers t) (powers_le_nonZeroDivisors_of_noZeroDivisors ht0)
  have : ConnectedSpace (Spec (.of (Localization.Away t))) := inferInstance
  have : IsLocallyNoetherian (Spec (.of (Localization.Away t))) := inferInstance
  obtain ⟨G, _, _, WA, hcard, hfix⟩ :=
    TameGaloisRealization.exists_galoisCover (s ≫ j) (geometricFiberFinite (s ≫ j)) ρ hρ
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hH
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : ℓ.Prime)).mp (hm ▸ hcard)
  have hn0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hn : IsUnit (Nat.card G : R) := by
    rw [hk, Nat.cast_pow]
    exact hℓ.pow k
  have := hreg
  obtain ⟨S, a, z, ha, hz, sB, hsB⟩ := TameRootSection.exists_root_section t ht0 G hn WA
  obtain ⟨φ, hφ⟩ := hq.2 k
  have hφ' : ∀ ζ : SeparableClosure (ResidueField R), ζ ^ Nat.card G = 1 → φ ζ = ζ ^ q :=
    fun ζ h => hφ ζ (hk ▸ h)
  let : Algebra R S := a.hom.toAlgebra
  have : Algebra.Etale R S :=
    RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp ha)
  have hz' : z.asIdeal.comap (algebraMap R S) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hz
  obtain ⟨R', _, _, _, hfinR', hetR', hinj, ζ, α, b, hζn, hζ, hαζ⟩ :=
    CommutativeAlgebra.HenselianCyclotomicExtension.exists_extension (Nat.card G) hn q φ hφ' S z.asIdeal hz'
  have ht' : algebraMap R R' t ≠ 0 := fun h => ht0 (hinj (h.trans (map_zero _).symm))
  obtain ⟨τ⟩ := exists_coverX_hom t WA (Nat.card G) hn0 hn S a _ rfl sB hsB R' (b : S →+* R')
    b.comp_algebraMap
  obtain ⟨σ, p, hp⟩ := exists_conj_fixed t R' hinj ht' hn0 hn hζn hζ α hαζ (s ≫ j)
    (geometricFiberFinite _) jg (smul_coverU_eq t ht.ne_zero s R' g)
  refine ⟨σ, ?_⟩
  have h1 := hfix ((jg ^ q)⁻¹ * (σ * jg * σ⁻¹)) (p ≫ τ.hom) (by rw [smul_naturality, hp])
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [← h1, map_pow]

end Langlands.AlgebraicGeometry.FiniteEtale

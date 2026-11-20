import Langlands.Geometry.FormalGroup.RationalHeightStatement
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyInverseAssembly
import Langlands.Geometry.FormalGroup.RationalHeightFieldRank
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.BaseChange

/-! # Existence and denominator independence of rational height -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower

section

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {π : O} {q : ℕ}

private theorem nontrivial_sections {U : Opens (PrimeSpectrum R)}
    {x : PrimeSpectrum R} (hx : x ∈ U) :
    Nontrivial ((coefficientStructurePresheaf R).obj (op U)) := by
  let : Nontrivial ((Spec.structureSheaf R).presheaf.stalk x) :=
    (StructureSheaf.stalkIso R x).injective.nontrivial
  exact ((Spec.structureSheaf R).presheaf.germ U x hx).hom.domain_nontrivial

private theorem integral_eq_of_rational_eq (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) {f g : Hom M N}
    (h : RationalHom.ofHom (F := F) f = RationalHom.ofHom g) : f = g := by
  let : IsLocalizedModule (nonZeroDivisors O)
      (RationalHom.ofHom (F := F) (M := M) (N := N)) :=
    IsLocalization.tensorProduct_isLocalizedModule _ F
  obtain ⟨a, ha⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) h
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.coe_ne_zero a) hπ
  change (a : O) • f = (a : O) • g at ha
  simp only [hu, mul_smul] at ha
  have hh := u.isUnit.smul_left_cancel.mp ha
  apply (hM.scalarPower_locallySurjective k).comp_right_cancel
  simpa only [scalarHom, Hom.comp_smul, Hom.comp_id] using hh

private theorem locally_integral_eq_of_section_eq (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) {U : Opens (PrimeSpectrum R)}
    {f g : OpenIntegralHom M N U}
    (h : RationalSection.ofIntegral U f = (RationalSection.ofIntegral U g :
        RationalSection F M N U)) (x : U) :
    ∃ (V : Opens (PrimeSpectrum R)) (_ : (x : PrimeSpectrum R) ∈ V) (i : V ⟶ U),
      Hom.algebraMapLinear ((coefficientStructurePresheaf R).map i.op) f =
        Hom.algebraMapLinear ((coefficientStructurePresheaf R).map i.op) g := by
  let a := RationalHom.ofHom (F := F) f
  let b := RationalHom.ofHom (F := F) g
  have heq : (rationalHomTypeUnit F M N).app (op U) a =
      (rationalHomTypeUnit F M N).app (op U) b := h
  have hc := Presheaf.equalizerSieve_mem
    (Opens.grothendieckTopology (PrimeSpectrum.Top R)) (rationalHomTypeUnit F M N) a b heq
  obtain ⟨V, i, hi, hxV⟩ := hc x.1 x.2
  let φ := (coefficientStructurePresheaf R).map i.op
  change RationalHom.algebraMapLinear φ a = RationalHom.algebraMapLinear φ b at hi
  dsimp only [a, b] at hi
  rw [RationalHom.algebraMapLinear_ofHom, RationalHom.algebraMapLinear_ofHom] at hi
  exact ⟨V, hxV, i, integral_eq_of_rational_eq hπ
    (hM.map (IsScalarTower.toAlgHom O R _)) hi⟩

private theorem heightPresentation_index_eq (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hq : 2 ≤ q) {U : Opens (PrimeSpectrum R)}
    {z : RationalSection F M N U} (P Q : RationalSection.HeightPresentation π q z)
    (x : U) : P.index = Q.index := by
  have heq : RationalSection.ofIntegral U (π ^ Q.exponent • P.representative) =
      (RationalSection.ofIntegral U (π ^ P.exponent • Q.representative) :
        RationalSection F M N U) := by
    rw [RationalSection.ofIntegral_smul, RationalSection.ofIntegral_smul,
      ← P.represents, ← Q.represents, map_pow, map_pow, smul_smul, smul_smul, mul_comm]
  obtain ⟨V, hxV, i, hi⟩ := locally_integral_eq_of_section_eq hπ hM heq x
  let := nontrivial_sections hxV
  let P' := P.restrict i
  let Q' := Q.restrict i
  let A := (coefficientStructurePresheaf R).obj (op V)
  simp only [map_smul] at hi
  have hcomp : P'.representative.comp ((M.overAlgebra A).scalarHom (π ^ Q'.exponent)) =
      Q'.representative.comp ((M.overAlgebra A).scalarHom (π ^ P'.exponent)) := by
    dsimp only [P', Q', RationalSection.HeightPresentation.restrict, A]
    simpa only [scalarHom, Hom.comp_smul, Hom.comp_id] using hi
  have hP := P'.numerator.comp_of_finiteKernelComposition
    (Hom.finiteKernelCompositionStatement _ _ _) Q'.denominator
  have hQ := Q'.numerator.comp_of_finiteKernelComposition
    (Hom.finiteKernelCompositionStatement _ _ _) P'.denominator
  rw [hcomp] at hP
  have hsum := hP.unique hq hQ
  change Q.denominatorHeight + P.numeratorHeight =
    P.denominatorHeight + Q.numeratorHeight at hsum
  unfold RationalSection.HeightPresentation.index
  omega

private theorem heightPresentation_index_eq_on_overlap (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hq : 2 ≤ q) {U V W : Opens (PrimeSpectrum R)}
    {z : RationalSection F M N U} {i : V ⟶ U} {j : W ⟶ U}
    (P : RationalSection.HeightPresentation π q (RationalSection.restrict i z))
    (Q : RationalSection.HeightPresentation π q (RationalSection.restrict j z))
    {x : PrimeSpectrum R} (hxV : x ∈ V) (hxW : x ∈ W) : P.index = Q.index := by
  let a : V ⊓ W ⟶ V := homOfLE inf_le_left
  let b : V ⊓ W ⟶ W := homOfLE inf_le_right
  have heq : RationalSection.restrict b (RationalSection.restrict j z) =
      RationalSection.restrict a (RationalSection.restrict i z) := by
    rw [← RationalSection.restrict_comp, ← RationalSection.restrict_comp]
    rw [Subsingleton.elim (b ≫ j) (a ≫ i)]
  simpa only [RationalSection.HeightPresentation.index_cast,
    RationalSection.HeightPresentation.index_restrict] using
    heightPresentation_index_eq hπ hM hq (P.restrict a) (heq ▸ Q.restrict b) ⟨x, hxV, hxW⟩

private theorem existsUnique_heightFunction_of_presentations (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hq : 2 ≤ q) {U : Opens (PrimeSpectrum R)}
    {z : RationalSection F M N U}
    (hloc : ∀ x : U, ∃ (V : Opens (PrimeSpectrum R)) (_ : (x : PrimeSpectrum R) ∈ V)
      (i : V ⟶ U), Nonempty (RationalSection.HeightPresentation π q
        (RationalSection.restrict i z))) :
    ∃! h : U → ℤ, RationalSection.HasHeightFunction π q z h := by
  classical
  choose V hx i P using hloc
  let h : U → ℤ := fun x => (Classical.choice (P x)).index
  refine ⟨h, ?_, ?_⟩
  · intro x
    refine ⟨V x, hx x, i x, Classical.choice (P x), ?_⟩
    intro y
    exact heightPresentation_index_eq_on_overlap hπ hM hq
      (Classical.choice (P ⟨y, leOfHom (i x) y.property⟩)) (Classical.choice (P x))
      (hx _) y.property
  · intro h' hh'
    funext x
    obtain ⟨W, hxW, j, Q, hQ⟩ := hh' x
    exact (hQ ⟨x, hxW⟩).trans (heightPresentation_index_eq_on_overlap hπ hM hq
      Q (Classical.choice (P x)) hxW (hx x))

variable [Finite (IsLocalRing.ResidueField O)]

private theorem rank_eq_pow_at_prime (hπ : Irreducible π) {d e : ℕ}
    (hM : M.HasPiHeight π (Nat.card (IsLocalRing.ResidueField O)) d)
    (hN : N.HasPiHeight π (Nat.card (IsLocalRing.ResidueField O)) e)
    {f : Hom M N} (hf : f.IsIsogeny) (K : Hom.FiniteKernelModel f)
    (p : PrimeSpectrum R) :
    ∃ h : ℕ, K.rank p = (Nat.card (IsLocalRing.ResidueField O)) ^ h := by
  let k := p.asIdeal.ResidueField
  let : Algebra O k := ((algebraMap R k).comp (algebraMap O R)).toAlgebra
  let : IsScalarTower O R k := IsScalarTower.of_algebraMap_eq' rfl
  let φ : R →ₐ[O] k := IsScalarTower.toAlgHom O R k
  let p₀ : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : p₀.comap φ.toRingHom = p := by
    apply PrimeSpectrum.ext
    exact Ideal.ker_algebraMap_residueField p.asIdeal
  obtain ⟨h, hh⟩ := Hom.finrank_finiteKernel_eq_pow_residueCard hπ
    (hM.map φ) (hN.map φ).1 (hf.map φ) (K.baseChange φ)
  refine ⟨h, ?_⟩
  rw [← hp, ← K.rank_baseChange φ p₀, ← hh]
  exact congrFun Module.rankAtStalk_eq_finrank_of_free p₀

omit [IsFractionRing O F] in
private theorem local_height_presentations (hπ : Irreducible π) {d e : ℕ}
    (hM : M.HasPiHeight π (Nat.card (IsLocalRing.ResidueField O)) d)
    (hN : N.HasPiHeight π (Nat.card (IsLocalRing.ResidueField O)) e)
    {U : Opens (PrimeSpectrum R)} (z : LocalQuasiIsogeny F π M N U) (x : U) :
    ∃ (V : Opens (PrimeSpectrum R)) (_ : (x : PrimeSpectrum R) ∈ V)
      (i : V ⟶ U), Nonempty (RationalSection.HeightPresentation π
        (Nat.card (IsLocalRing.ResidueField O)) (RationalSection.restrict i z.val)) := by
  obtain ⟨W, hxW, i, n, f, hf, heq⟩ := z.isLocal x x.property
  obtain ⟨_, ⟨r, rfl⟩, hxr, hrW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxW W.isOpen
  let a : PrimeSpectrum.basicOpen r ⟶ W := homOfLE hrW
  let A := (coefficientStructurePresheaf R).obj (op (PrimeSpectrum.basicOpen r))
  let : IsLocalization.Away r A := StructureSheaf.IsLocalization.to_basicOpen R r
  let g := Hom.algebraMapLinear ((coefficientStructurePresheaf R).map a.op) f
  have hg : g.IsIsogeny := hf.algebraMapLinear _
  obtain ⟨K⟩ := hg.2
  let ι := PrimeSpectrum.comap (algebraMap R A)
  have hι := PrimeSpectrum.localization_away_isOpenEmbedding A r
  obtain ⟨p, hp⟩ : x.val ∈ Set.range ι := by
    rw [PrimeSpectrum.localization_away_comap_range A r]
    exact hxr
  obtain ⟨h, hh⟩ := rank_eq_pow_at_prime hπ
    (hM.map (IsScalarTower.toAlgHom O R A)) (hN.map (IsScalarTower.toAlgHom O R A))
    hg K p
  let L : Set (PrimeSpectrum A) := {p' | K.rank p' = K.rank p}
  have hL : IsOpen (ι '' L) := hι.isOpenMap _ (K.isLocallyConstant_rank.isOpen_fiber _)
  have hxL : x.val ∈ ι '' L := ⟨p, rfl, hp⟩
  obtain ⟨_, ⟨s, rfl⟩, hxs, hsL⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxL hL
  let V := PrimeSpectrum.basicOpen s
  have hs : V ≤ PrimeSpectrum.basicOpen r := by
    intro y hy
    change y ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))
    rw [← PrimeSpectrum.localization_away_comap_range A r]
    obtain ⟨p', _, hp'⟩ := hsL hy
    exact ⟨p', hp'⟩
  let b : V ⟶ PrimeSpectrum.basicOpen r := homOfLE hs
  let B := (coefficientStructurePresheaf R).obj (op V)
  let : IsLocalization.Away s B := StructureSheaf.IsLocalization.to_basicOpen R s
  let ψ : A ⟶ B := (coefficientStructurePresheaf R).map b.op
  have hψ : g.map (coefficientAlgHom ψ) |>.HasKernelRank
      ((Nat.card (IsLocalRing.ResidueField O)) ^ h) := by
    refine ⟨K.baseChange (coefficientAlgHom ψ), fun p' => ?_⟩
    rw [K.rank_baseChange, ← hh]
    have hp' : PrimeSpectrum.comap (algebraMap R B) p' ∈ V := by
      change _ ∈ (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum R))
      rw [← PrimeSpectrum.localization_away_comap_range B s]
      exact ⟨p', rfl⟩
    obtain ⟨p'', hp'', hpp⟩ := hsL hp'
    have he : p'.comap (coefficientAlgHom (O := O) ψ).toRingHom = p'' := by
      apply hι.injective
      change ι _ = ι _
      unfold ι at hpp ⊢
      rw [hpp, ← PrimeSpectrum.comap_comp_apply]
      exact congrArg (fun φ : R →+* B => PrimeSpectrum.comap φ p') ψ.hom.comp_algebraMap
    change K.rank p'' = K.rank p at hp''
    simpa only [he] using hp''
  let g' := Hom.algebraMapLinear ψ g
  have hg' : g'.HasHeight (Nat.card (IsLocalRing.ResidueField O)) h := by
    refine ⟨hg.algebraMapLinear ψ, ?_⟩
    apply (Hom.hasKernelRank_iff_of_kernelSetIso _ g'
      (Hom.kernelSetIsoOfIsoSquare _ g' (M.overAlgebraIso ψ) (N.overAlgebraIso ψ) ?_) _).mp hψ
    change ((N.overAlgebraIso ψ).hom.comp
      ((g.map (coefficientAlgHom ψ)).comp (M.overAlgebraIso ψ).inv)).comp
      (M.overAlgebraIso ψ).hom = _
    rw [Hom.comp_assoc, Hom.comp_assoc, Iso.inv_hom, Hom.comp_id]
  refine ⟨V, hxs, b ≫ a ≫ i, ⟨{
    exponent := n
    representative := g'
    numeratorHeight := h
    denominatorHeight := n * d
    numerator := hg'
    denominator := (hM.map (IsScalarTower.toAlgHom O R B)).scalarPower_height n
    represents := ?_ }⟩⟩
  have hrestrict := congrArg (RationalSection.restrict b ∘ RationalSection.restrict a) heq
  simpa only [Function.comp_apply, map_smul, RationalSection.restrict_ofIntegral,
    ← RationalSection.restrict_comp, Category.assoc] using hrestrict

end

/-- A local quasi-isogeny has a unique function locally given by the difference
of its integral numerator height and its scalar denominator height. -/
theorem rationalHeightExistenceUniqueness
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    (F : Type v) [Field F] [Algebra O F] [IsFractionRing O F]
    (R : Type v) [CommRing R] [Algebra O R] :
    RationalHeightExistenceUniquenessStatement O F R := by
  intro π hπ σ τ _ _ M N d e hM hN U z
  exact existsUnique_heightFunction_of_presentations hπ hM.1 Finite.one_lt_card
    (local_height_presentations hπ hM hN z)

end Langlands.FormalGroup.ModuleLaw

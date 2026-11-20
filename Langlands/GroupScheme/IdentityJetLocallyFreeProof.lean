import Langlands.GroupScheme.IdentityJetAffineChart
import Langlands.GroupScheme.IdentityJetLocallyFreeStatement
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Localization.BaseChange

/-! # Identity jets of smooth separated groups are locally finite free -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdentityJet

section Localization

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
  [IsSeparated G.X.hom] [Smooth G.X.hom] (n : ℕ) (V : G.X.left.affineOpens)
  (hV : G.identitySection ⁻¹ᵁ V.1 = ⊤)

include hV in
/-- After inverting one element outside a given prime, the jet of the base-changed group is
the spectrum of a finite free algebra. -/
theorem exists_free_jet_localization (t : PrimeSpectrum R) :
    ∃ r : R, r ∉ t.asIdeal ∧
      ∃ (P' : CommAlgCat.{u} (Localization.Away r))
        (e' : scheme ((GroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj G) n ≅
          Spec (CommRingCat.of P')),
        e'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away r) P')) =
          projection ((GroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj G) n ∧
        ∃ m : ℕ, Nonempty (Module.Basis (Fin m) (Localization.Away r) P') := by
  obtain ⟨hfin, hproj⟩ := chartJetAlgebra_finite_projective G n V hV
  let P := chartJetAlgebra G n V
  have : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  have hloc : Module.Free (Localization.AtPrime t.asIdeal)
      (LocalizedModule t.asIdeal.primeCompl P) := by
    have h := (Module.freeLocus_eq_univ_iff (R := R) (M := P)).mpr hproj
    have ht : t ∈ Module.freeLocus R P := h ▸ Set.mem_univ t
    exact Module.mem_freeLocus.mp ht
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    t.asIdeal.primeCompl (LocalizedModule.mkLinearMap t.asIdeal.primeCompl P)
    (Localization.AtPrime t.asIdeal)
  refine ⟨r, hr, ?_⟩
  let Rr := Localization.Away r
  have : Nontrivial Rr :=
    (show Localization (Submonoid.powers r) →+* Localization.AtPrime t.asIdeal from
      IsLocalization.map (M := .powers r) (T := t.asIdeal.primeCompl) _
        (RingHom.id _) (Submonoid.powers_le.mpr hr)).domain_nontrivial
  let j : Spec (CommRingCat.of Rr) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R Rr))
  let G' := (GroupScheme.baseChange j).obj G
  have h₁ : IsPullback (jetBaseChangeMap G j n) (projection G' n) (projection G n) j :=
    (jetBaseChange_isPullback G j n).flip.paste_vert (IsPullback.of_hasPullback G.X.hom j)
  have h₂ : IsPullback (chartJetIso G n V hV).hom (projection G n)
      (Spec.map (CommRingCat.ofHom (algebraMap R P))) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, chartJetIso_projection]⟩
  have h₃ := h₁.paste_horiz h₂
  rw [Category.comp_id] at h₃
  let P' : CommAlgCat.{u} Rr := CommAlgCat.of Rr (Rr ⊗[R] P)
  let e' : scheme G' n ≅ Spec (CommRingCat.of P') :=
    h₃.flip.isoPullback ≪≫ pullbackSpecIso R Rr P
  refine ⟨P', e', ?_, ?_⟩
  · change (h₃.flip.isoPullback.hom ≫ (pullbackSpecIso R Rr P).hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Rr (Rr ⊗[R] P))) = _
    rw [Category.assoc, pullbackSpecIso_hom_fst', IsPullback.isoPullback_hom_fst]
  · have hP : Module.Free Rr (Rr ⊗[R] P) :=
      Module.Free.of_equiv (LocalizedModule.isBaseChange (Submonoid.powers r) P).equiv.symm
    exact ⟨_, ⟨Module.finBasis Rr (Rr ⊗[R] P)⟩⟩

end Localization

section Iso

variable {T : Scheme.{u}} {H H' : GroupScheme T}

theorem ideal_comap_le_of_hom (f : H ⟶ H') (n : ℕ) :
    (ideal H' n).comap f.hom.hom.left ≤ ideal H n := by
  have h₁ : H'.identitySection.ker.comap f.hom.hom.left ≤ H.identitySection.ker := by
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker,
      identitySection_naturality]
  change (H'.identitySection.ker ^ (n + 1)).comap f.hom.hom.left ≤
    H.identitySection.ker ^ (n + 1)
  rw [idealSheaf_comap_pow]
  exact pow_le_pow_left₀ zero_le h₁ (n + 1)

/-- The map of identity jets induced by a homomorphism of group schemes. -/
def homJetMap (f : H ⟶ H') (n : ℕ) : scheme H n ⟶ scheme H' n :=
  Scheme.IdealSheafData.subschemeMap (ideal H n) (ideal H' n) f.hom.hom.left
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr (ideal_comap_le_of_hom f n))

@[reassoc (attr := simp)]
theorem homJetMap_inclusion (f : H ⟶ H') (n : ℕ) :
    homJetMap f n ≫ inclusion H' n = inclusion H n ≫ f.hom.hom.left :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

theorem homJetMap_projection (f : H ⟶ H') (n : ℕ) :
    homJetMap f n ≫ projection H' n = projection H n := by
  change homJetMap f n ≫ inclusion H' n ≫ H'.X.hom = inclusion H n ≫ H.X.hom
  rw [← Category.assoc, homJetMap_inclusion, Category.assoc, Over.w f.hom.hom]

/-- Isomorphic group schemes have isomorphic identity jets. -/
def jetIsoOfIso (φ : H ≅ H') (n : ℕ) : scheme H n ≅ scheme H' n where
  hom := homJetMap φ.hom n
  inv := homJetMap φ.inv n
  hom_inv_id := by
    rw [← cancel_mono (inclusion H n), Category.assoc, homJetMap_inclusion,
      homJetMap_inclusion_assoc, Category.id_comp, ← Over.comp_left, ← Grp.comp_hom_hom,
      φ.hom_inv_id]
    rfl
  inv_hom_id := by
    rw [← cancel_mono (inclusion H' n), Category.assoc, homJetMap_inclusion,
      homJetMap_inclusion_assoc, Category.id_comp, ← Over.comp_left, ← Grp.comp_hom_hom,
      φ.inv_hom_id]
    rfl

end Iso

section Affine

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
  [IsSeparated G.X.hom] [Smooth G.X.hom] (n : ℕ)

/-- Over an affine base, every point has an affine open neighbourhood over which the jet of
the base-changed group is the spectrum of a finite free algebra. -/
theorem exists_free_jet_affine (t : PrimeSpectrum R) :
    ∃ (R' : CommRingCat.{u}) (k : Spec R' ⟶ Spec (CommRingCat.of R)),
      IsOpenImmersion k ∧ t ∈ Set.range k.base ∧
      ∃ (P' : CommAlgCat.{u} R')
        (e' : scheme ((GroupScheme.baseChange k).obj G) n ≅ Spec (CommRingCat.of P')),
        e'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R' P')) =
          projection ((GroupScheme.baseChange k).obj G) n ∧
        ∃ m : ℕ, Nonempty (Module.Basis (Fin m) R' P') := by
  obtain ⟨V, hV, heV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show G.identitySection t ∈ (⊤ : G.X.left.Opens) from trivial)
  obtain ⟨_, ⟨f, rfl⟩, htf, hfV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := t) (u := (↑(G.identitySection ⁻¹ᵁ V) : Set ↥(Spec (CommRingCat.of R)))) heV
      (G.identitySection ⁻¹ᵁ V).isOpen
  let Rf := Localization.Away f
  let j₁ : Spec (CommRingCat.of Rf) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R Rf))
  let G₂ := (GroupScheme.baseChange j₁).obj G
  have : IsSeparated G₂.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom j₁))
  have : Smooth G₂.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom j₁))
  have hrange₁ : Set.range j₁.base = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
    rw [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of R) f]
  have : IsAffineHom (pullback.fst G.X.hom j₁) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  let V₂ : G₂.X.left.affineOpens := ⟨pullback.fst G.X.hom j₁ ⁻¹ᵁ V, hV.preimage _⟩
  have hV₂ : G₂.identitySection ⁻¹ᵁ V₂.1 = ⊤ := by
    change G₂.identitySection ⁻¹ᵁ (pullback.fst G.X.hom j₁ ⁻¹ᵁ V) = ⊤
    rw [← Scheme.Hom.comp_preimage, identitySection_baseChange_fst, Scheme.Hom.comp_preimage]
    apply top_le_iff.mp
    intro x _
    have hx : j₁.base x ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
      hrange₁ ▸ Set.mem_range_self x
    exact hfV hx
  obtain ⟨t₂, ht₂⟩ : t ∈ Set.range j₁.base := hrange₁ ▸ htf
  obtain ⟨r, hr, P', e', he', hb⟩ := exists_free_jet_localization G₂ n V₂ hV₂ t₂
  let j₂ : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec (CommRingCat.of Rf) :=
    Spec.map (CommRingCat.ofHom (algebraMap Rf (Localization.Away r)))
  let k := j₂ ≫ j₁
  let c := Descent.pullbackComparison j₁ j₂ k rfl G
  refine ⟨CommRingCat.of (Localization.Away r), k, inferInstance, ?_, P',
    (jetIsoOfIso c n).symm ≪≫ e', ?_, hb⟩
  · have hrange₂ : Set.range j₂.base =
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Rf)) := by
      rw [← Scheme.Hom.coe_opensRange,
        Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of Rf) r]
    obtain ⟨t₃, ht₃⟩ : t₂ ∈ Set.range j₂.base := hrange₂ ▸ hr
    exact ⟨t₃, by rw [Scheme.Hom.comp_apply, ht₃, ht₂]⟩
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, he']
    exact homJetMap_projection c.inv n

end Affine

end Langlands.GroupScheme.IdentityJet

namespace Langlands.GroupScheme

open IdentityJet

/-- **Identity jets of smooth separated groups are locally finite free.** -/
theorem identityJetLocallyFree : IdentityJetLocallyFreeStatement.{u} := by
  intro S G hsm hsep n s W hsW
  have : Smooth G.X.hom := hsm
  have : IsSeparated G.X.hom := hsep
  obtain ⟨R₁, i₁, hi₁, hs₁, hW₁⟩ := Scheme.exists_affine_mem_range_and_range_subset hsW
  let G₁ := (GroupScheme.baseChange i₁).obj G
  have : IsSeparated G₁.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom i₁))
  have : Smooth G₁.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom i₁))
  obtain ⟨t, ht⟩ := hs₁
  obtain ⟨R', k, hk, htk, P', e', he', hb⟩ := exists_free_jet_affine (R := R₁) G₁ n t
  let i := k ≫ i₁
  let c := Descent.pullbackComparison i₁ k i rfl G
  refine ⟨R', i, inferInstance, ?_, ?_, P', (jetIsoOfIso c n).symm ≪≫ e', ?_, hb⟩
  · obtain ⟨t', ht'⟩ := htk
    exact ⟨t', by rw [Scheme.Hom.comp_apply, ht', ht]⟩
  · rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hW₁ ⟨k.base x, rfl⟩
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, he']
    exact homJetMap_projection c.inv n

end Langlands.GroupScheme

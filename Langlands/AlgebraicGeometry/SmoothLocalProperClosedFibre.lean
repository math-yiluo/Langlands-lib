import Langlands.AlgebraicGeometry.ClosedFibreOpenIntegrality
import Langlands.AlgebraicGeometry.GeometricallyIntegralConnected
import Langlands.AlgebraicGeometry.Picard.GenericSectionSchematicClosure
import Langlands.AlgebraicGeometry.ProperOfFibres.LocalZariski
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange

/-! # Properness of a smooth local family from its proper closed fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Langlands.AlgebraicGeometry

open ProperOfFibres

section LocalProper

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A proper surjective model with integral total space and geometrically
integral generic fibre has constant global functions over a normal local domain. -/
private theorem bijective_appTop_of_geometricallyIntegral_generic
    [IsDomain R] [IsIntegrallyClosed R]
    {P : Scheme.{u}} [IsIntegral P] (q : P ⟶ Spec (CommRingCat.of R))
    [IsProper q] [Surjective q]
    [GeometricallyIntegral (pullback.snd q (Spec.algebraMap R (FractionRing R)))] :
    Function.Bijective q.appTop := by
  let K := FractionRing R
  let j := Spec.algebraMap R K
  let gen := pullback.fst q j
  let qK := pullback.snd q j
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨x, hx⟩ := q.surjective η
  have hspecializes := ((genericPoint_spec P).specializes (Set.mem_univ x)).map q.continuous
  rw [hx] at hspecializes
  have hη : q (genericPoint P) = η := by
    apply PrimeSpectrum.ext
    exact le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ _).mpr hspecializes)
  have hmem : genericPoint P ∈ Set.range gen := by
    change genericPoint P ∈ Set.range (pullback.fst q j)
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hη]
    exact bot_mem_range_SpecMap_algebraMap K
  let : IsDominant gen := ⟨(dense_iff_closure_eq.mpr (genericPoint_closure P)).mono
    (Set.singleton_subset_iff.mpr hmem)⟩
  let : IsSchemeTheoreticallyDominant gen := IsSchemeTheoreticallyDominant.of_isDominant gen
  let : GeometricallyConnected qK :=
    Langlands.AbelianScheme.TranslationOfSmoothFamily.geometricallyConnected_of_geometricallyIntegral qK
  have hK : Function.Bijective qK.appTop :=
    AlgebraicGeometry.bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected qK
  let eR := Scheme.ΓSpecIso (CommRingCat.of R)
  let eK := Scheme.ΓSpecIso (CommRingCat.of K)
  let γ := RingEquiv.ofBijective qK.appTop.hom hK
  let restrict : Γ(P, ⊤) →+* K := eK.hom.hom.comp (γ.symm.toRingHom.comp gen.appTop.hom)
  have hrestrict : Function.Injective restrict :=
    (ConcreteCategory.bijective_of_isIso eK.hom).1.comp
      (γ.symm.injective.comp (gen.app_injective ⊤))
  have halgebra : ∀ v, restrict (q.appTop v) = algebraMap R K (eR.hom v) := by
    intro v
    have hcomp : q.appTop ≫ gen.appTop = j.appTop ≫ qK.appTop := by
      rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop]
    have h₁ : gen.appTop (q.appTop v) = qK.appTop (j.appTop v) := by
      simpa using congrArg (fun a => a.hom v) hcomp
    have h₂ : eK.hom (j.appTop v) = algebraMap R K (eR.hom v) :=
      congrArg (fun a => a.hom v)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R K)))
    change eK.hom (γ.symm (gen.appTop (q.appTop v))) = _
    rw [h₁, show γ.symm (qK.appTop (j.appTop v)) = j.appTop v from γ.symm_apply_apply _, h₂]
  constructor
  · intro a b hab
    have h := congrArg restrict hab
    rw [halgebra, halgebra] at h
    exact (ConcreteCategory.bijective_of_isIso eR.hom).1 ((IsFractionRing.injective R K) h)
  · intro z
    have hz := (isIntegral_appTop_of_universallyClosed q z).map restrict
    have hcomp : restrict.comp q.appTop.hom = (algebraMap R K).comp eR.hom.hom := RingHom.ext halgebra
    obtain ⟨p, hp, he⟩ := hz
    rw [hcomp] at he
    have hintegral : IsIntegral R (restrict z) :=
      ⟨p.map eR.hom.hom, hp.map _, by rw [Polynomial.eval₂_map]; exact he⟩
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintegral
    refine ⟨eR.inv v, hrestrict ?_⟩
    rw [halgebra, ← hv]
    congr 1
    exact congrArg (fun a => a.hom v) eR.inv_hom_id

/-- A proper closed fibre fills a connected closed fibre of a proper ambient
scheme when the open meets that fibre. -/
private theorem proper_open_of_connected_closedFibre {Y P : Scheme.{u}}
    (a : Y ⟶ P) [IsOpenImmersion a] (q : P ⟶ Spec (CommRingCat.of R))
    [IsProper q] [Surjective (a ≫ q)]
    (hconn : _root_.IsPreconnected (q ⁻¹' {IsLocalRing.closedPoint R}))
    (hproper : IsProper (pullback.snd (a ≫ q) (Spec.algebraMap R (IsLocalRing.ResidueField R)))) :
    IsProper (a ≫ q) := by
  let s := IsLocalRing.closedPoint R
  let sp := Spec.algebraMap R (IsLocalRing.ResidueField R)
  let e := pullback.fst (a ≫ q) sp ≫ a
  let : IsClosedImmersion sp := IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  let : IsProper (pullback.snd (a ≫ q) sp) := hproper
  have heq : e ≫ q = pullback.snd (a ≫ q) sp ≫ sp := by
    rw [Category.assoc, pullback.condition]
  let : IsProper (e ≫ q) := by rw [heq]; infer_instance
  let : IsProper e := IsProper.of_comp e q
  have hcl : IsClosed (Set.range e) := e.isClosedMap.isClosed_range
  have hsub : Set.range e ⊆ Set.range a := by
    rintro _ ⟨w, rfl⟩
    exact ⟨pullback.fst (a ≫ q) sp w, rfl⟩
  have hmem : ∀ y : Y, (a ≫ q) y = s → a y ∈ Set.range e := by
    intro y hy
    have hrange : y ∈ Set.range (pullback.fst (a ≫ q) sp) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hy]
      change s ∈ Set.range (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
      rw [range_SpecMap_residue]
      rfl
    obtain ⟨w, rfl⟩ := hrange
    exact ⟨w, rfl⟩
  have hcover : q ⁻¹' {s} ⊆ Set.range e ∪ (Set.range a)ᶜ := by
    intro z hz
    by_cases ha : z ∈ Set.range a
    · obtain ⟨y, rfl⟩ := ha
      exact Or.inl (hmem y hz)
    · exact Or.inr ha
  have hdisj : q ⁻¹' {s} ∩ (Set.range e ∩ (Set.range a)ᶜ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨_, h₁, h₂⟩
    exact h₂ (hsub h₁)
  have hs : q ⁻¹' {s} ⊆ Set.range e := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hconn) _ _ hcl
        a.isOpenEmbedding.isOpen_range.isClosed_compl hcover hdisj with h | h
    · exact h
    · obtain ⟨y, hy⟩ := (a ≫ q).surjective s
      exact False.elim (h hy ⟨y, rfl⟩)
  have htop : a.opensRange = ⊤ :=
    open_eq_top_of_contains_closedFibre q a.opensRange (fun x hx => hsub (hs hx))
  let : Surjective a := ⟨fun x => by
    change x ∈ Set.range a
    have hx : x ∈ a.opensRange := htop.symm ▸ Set.mem_univ x
    exact hx⟩
  let : IsIso a := (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  infer_instance

end LocalProper

open P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint
open scoped P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint
open scoped P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData

/-- A smooth, separated, quasi-compact scheme with geometrically connected fibres over a
noetherian normal local domain is proper if its closed fibre is proper. -/
theorem isProper_of_smooth_of_proper_closedFibre
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    [Smooth p] [IsSeparated p] [QuasiCompact p] [GeometricallyConnected p]
    (hclosed : IsProper (pullback.snd p (Spec.algebraMap R (IsLocalRing.ResidueField R)))) :
    IsProper p := by
  let K := FractionRing R
  let j := Spec.algebraMap R K
  let : Flat j := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_geometricallyConnected p
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨D⟩ := nonempty_chartData p
  let π := D.π
  let P := D.ιι.image
  let a := D.ιι.toImage
  let q := D.ιι.imageι ≫ D.prπ
  let d := D.ψ' ≫ a
  have hfac : a ≫ q = π ≫ p := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, ← D.π_comp_f]
  have hd : d ≫ q = D.Uo.ι ≫ p := by
    rw [Category.assoc, hfac, ← Category.assoc, D.ψ'_π]
  let : IsProper q := inferInstance
  let : IsProper π := inferInstance
  let : Surjective π := inferInstance
  let : Surjective (a ≫ q) := hfac.symm ▸ inferInstanceAs (Surjective (π ≫ p))
  let : Surjective q := ⟨fun x => by
    obtain ⟨y, hy⟩ := (a ≫ q).surjective x
    exact ⟨a y, hy⟩⟩
  let : IsSchemeTheoreticallyDominant D.ψ' := toImage_schemeTheoreticallyDominant D.ψ
  let : IsSchemeTheoreticallyDominant a := toImage_schemeTheoreticallyDominant D.ιι
  let : IsSchemeTheoreticallyDominant d := inferInstance
  let : QuasiCompact d := inferInstance
  let : IsIntegral P := isIntegral_schematicImage D.ιι
  let : GeometricallyIntegral (pullback.snd q j) := by
    refine ⟨?_⟩
    intro L _ b Z fst snd h
    let O := Over.mk (D.Uo.ι ≫ p)
    let Q := Over.mk q
    let lift : O ⟶ Q := Over.homMk d hd
    let : IsSchemeTheoreticallyDominant lift.left := inferInstanceAs (IsSchemeTheoreticallyDominant d)
    let : QuasiCompact lift.left := inferInstanceAs (QuasiCompact d)
    let b' := b ≫ j
    let l := (Over.pullback b').map lift
    let : Flat b' := inferInstanceAs (Flat (b ≫ j))
    let hpb := Langlands.GroupScheme.RelativeIdentityComponent.overPullback_isPullback b' lift
    let : IsSchemeTheoreticallyDominant l.left :=
      IsSchemeTheoreticallyDominant.of_isPullback hpb.flip
    let : QuasiCompact l.left :=
      MorphismProperty.overPullbackMap (P := @QuasiCompact) b' lift inferInstance
    let : Nonempty ↥((Over.pullback b').obj Q).left := by
      obtain ⟨x, _⟩ := (pullback.snd q b').surjective
        (Nonempty.some (inferInstance : Nonempty ↥(Spec (CommRingCat.of L))))
      exact ⟨x⟩
    let : Nonempty ((Over.pullback b').obj O).left := l.left.denseRange.nonempty
    let : IsIntegral (pullback p b') := pullback_of_geometrically
      (GeometricallyIntegral.geometrically_isIntegral (f := p)) L b'
    let e := pullbackRightPullbackFstIso p b' D.Uo.ι
    have : Nonempty ↥(pullback D.Uo.ι (pullback.fst p b')) :=
      ‹Nonempty ((Over.pullback b').obj O).left›.map (fun z => e.inv z)
    let : IsIntegral (pullback D.Uo.ι (pullback.fst p b')) :=
      isIntegral_of_isOpenImmersion (pullback.snd D.Uo.ι (pullback.fst p b'))
    let : IsIntegral ((Over.pullback b').obj O).left := isIntegral_of_isOpenImmersion e.inv
    let : IsReduced (pullback q b') := IsSchemeTheoreticallyDominant.isReduced l.left
    let : IrreducibleSpace ↥(pullback q b') := by
      apply (irreducibleSpace_def ↥(pullback q b')).mpr
      change IsIrreducible (Set.univ : Set ↥(pullback q b'))
      rw [← l.left.denseRange.closure_range, ← Set.image_univ]
      exact ((IrreducibleSpace.isIrreducible_univ _).image _ l.left.continuous.continuousOn).closure
    let : IsIntegral (pullback q b') := isIntegral_of_irreducibleSpace_of_isReduced _
    let iso := h.isoPullback ≪≫ pullbackLeftPullbackSndIso q j b
    let : Nonempty Z := (inferInstance : Nonempty ↥(pullback q b')).map (fun z => iso.inv z)
    exact isIntegral_of_isOpenImmersion iso.hom
  have hΓ := bijective_appTop_of_geometricallyIntegral_generic q
  have hc := isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop q hΓ
  let sp := Spec.algebraMap R (IsLocalRing.ResidueField R)
  have hYsp : IsProper (pullback.snd (a ≫ q) sp) := by
    rw [hfac]
    let : IsProper (pullback.snd p sp) := hclosed
    let lift : Over.mk (π ≫ p) ⟶ Over.mk p := Over.homMk π rfl
    let l := (Over.pullback sp).map lift
    let : IsProper l.left :=
      MorphismProperty.overPullbackMap (P := @IsProper) sp lift
        (inferInstanceAs (IsProper π))
    rw [show pullback.snd (π ≫ p) sp = l.left ≫ pullback.snd p sp from (Over.w l).symm]
    infer_instance
  let : IsProper (a ≫ q) := proper_open_of_connected_closedFibre a q hc hYsp
  let : UniversallyClosed (π ≫ p) := hfac ▸ inferInstanceAs (UniversallyClosed (a ≫ q))
  let : UniversallyClosed p := UniversallyClosed.of_comp_surjective π p
  exact {}

end Langlands.AlgebraicGeometry

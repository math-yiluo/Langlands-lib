import Langlands.AlgebraicGeometry.FiniteFreeSchemeActionQuotient
import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationQuotientProof
import Langlands.AlgebraicGeometry.Morphisms.FiniteCoproduct
import Langlands.AlgebraicGeometry.OrbitSaturatedAffineOpen
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Quasi-affine quotients of finite free actions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

namespace FiniteLocallyFreeQuotient

/-- Affineness descends along a finite locally free surjection. -/
theorem isAffine_of_finite_flat_surjective {X Y : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Y) [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p] :
    IsAffine Y := by
  have hj : ∀ {T : Scheme.{u}} (a b : T ⟶ pullback p p),
      a ≫ pullback.fst p p = b ≫ pullback.fst p p →
      a ≫ pullback.snd p p = b ≫ pullback.snd p p → a = b := by
    intro T a b h₁ h₂
    exact pullback.hom_ext h₁ h₂
  have he : ∀ T : Scheme.{u}, _root_.Equivalence
      (fun x y : T ⟶ X => ∃ r : T ⟶ pullback p p,
        r ≫ pullback.fst p p = x ∧ r ≫ pullback.snd p p = y) := by
    intro T
    have hiff : ∀ x y : T ⟶ X,
        (∃ r : T ⟶ pullback p p,
          r ≫ pullback.fst p p = x ∧ r ≫ pullback.snd p p = y) ↔ x ≫ p = y ≫ p := by
      intro x y
      constructor
      · rintro ⟨r, rfl, rfl⟩
        simpa only [Category.assoc] using
          congrArg (fun k => r ≫ k) (pullback.condition (f := p) (g := p))
      · intro h
        exact ⟨pullback.lift x y h, by simp, by simp⟩
    exact ⟨fun x => (hiff x x).mpr rfl,
      fun h => (hiff _ _).mpr ((hiff _ _).mp h).symm,
      fun h h' => (hiff _ _).mpr (((hiff _ _).mp h).trans ((hiff _ _).mp h'))⟩
  obtain ⟨Z, hZ, q, w, _, _, _, _, _, ⟨hc⟩⟩ :=
    existsAffineQuotient (pullback.fst p p) (pullback.snd p p) hj he
  have hk : IsKernelPair p (pullback.fst p p) (pullback.snd p p) :=
    IsPullback.of_hasPullback p p
  let hc' : IsColimit (Cofork.ofπ p (pullback.condition (f := p) (g := p))) :=
    hk.toCoequalizer (regularEpiOfEffectiveEpi p)
  let e : Y ≅ Z := hc'.coconePointUniqueUpToIso hc
  let : IsAffine Z := hZ
  exact isAffine_of_isAffineHom e.hom

end FiniteLocallyFreeQuotient

namespace FiniteFreeSchemeAction

variable {G : Type u} [Group G] {X : Scheme.{u}} (A : FiniteFreeSchemeAction G X)

/-- Finiteness of the action projections does not require an affine source. -/
theorem source_isFinite_of_finite [Finite G] : IsFinite A.source := by
  let : IsProper A.source :=
    FiniteCoproduct.isProper_sigmaDesc (fun _ : G => X) (fun _ => 𝟙 X)
      (fun _ => inferInstance)
  let : LocallyQuasiFinite A.source :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyQuasiFinite) (fun _ => inferInstance)
  exact IsFinite.of_isProper_of_locallyQuasiFinite A.source

theorem target_isFinite_of_finite [Finite G] : IsFinite A.target := by
  let : IsProper A.target :=
    FiniteCoproduct.isProper_sigmaDesc (fun _ : G => X) (fun g => (A.act g).hom)
      (fun _ => inferInstance)
  let : LocallyQuasiFinite A.target :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyQuasiFinite) (fun _ => inferInstance)
  exact IsFinite.of_isProper_of_locallyQuasiFinite A.target

/-- Every finite set lies in an invariant affine principal open. -/
theorem exists_invariant_affineBasicOpen [Finite G] [X.IsQuasiAffine]
    {E : Set X} (hE : E.Finite) :
    ∃ s : Γ(X, ⊤), E ⊆ X.basicOpen s ∧ IsAffineOpen (X.basicOpen s) ∧
      ∀ g : G, (A.act g).hom.appTop s = s := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let σ : G → (X ⟶ X) := fun g => (A.act g).hom
  let F : Set X := ⋃ g, σ g '' E
  have hF : F.Finite := Set.finite_iUnion fun g => hE.image _
  obtain ⟨r, hr, haff⟩ :=
    OrbitSaturatedAffineOpen.exists_basicOpen_isAffineOpen_of_finite X hF
  let s := OrbitSaturatedAffineOpen.norm σ r
  have hmem (x : X) : x ∈ X.basicOpen s ↔ ∀ g, σ g x ∈ X.basicOpen r :=
    OrbitSaturatedAffineOpen.mem_basicOpen_norm σ r x
  have hle : X.basicOpen s ≤ X.basicOpen r := by
    intro x hx
    have := (hmem x).mp hx 1
    simpa [σ, A.one] using this
  refine ⟨s, ?_, ?_, ?_⟩
  · intro x hx
    exact (hmem x).mpr fun g => hr (Set.mem_iUnion.mpr ⟨g, x, hx, rfl⟩)
  · have h := haff.basicOpen (X.presheaf.map (homOfLE le_top).op s)
    rwa [Scheme.basicOpen_res, inf_eq_right.mpr hle] at h
  · exact fun g => OrbitSaturatedAffineOpen.appTop_norm σ A.mul g r

/-- An effective scheme quotient of the complete action relation. -/
structure EffectiveQuotient where
  scheme : Scheme.{u}
  map : X ⟶ scheme
  condition : A.target ≫ map = A.source ≫ map
  finite : IsFinite map
  etale : Etale map
  surjective : Surjective map
  isPullback : IsPullback A.target A.source map map
  isColimit : IsColimit (Cofork.ofπ map condition)

attribute [instance] EffectiveQuotient.finite EffectiveQuotient.etale
  EffectiveQuotient.surjective

theorem nonempty_effectiveQuotient [Finite G] [X.IsQuasiAffine] :
    Nonempty A.EffectiveQuotient := by
  let : IsFinite A.source := A.source_isFinite_of_finite
  let : IsFinite A.target := A.target_isFinite_of_finite
  have hj : ∀ {T : Scheme.{u}} (a b : T ⟶ A.relationScheme),
      a ≫ A.target = b ≫ A.target → a ≫ A.source = b ≫ A.source → a = b := by
    intro T a b ht hs
    apply (cancel_mono (prod.lift A.target A.source)).mp
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst] using ht
    · simpa only [Category.assoc, prod.lift_snd] using hs
  have he : ∀ T : Scheme.{u}, _root_.Equivalence
      (fun x y : T ⟶ X => ∃ r : T ⟶ A.relationScheme,
        r ≫ A.target = x ∧ r ≫ A.source = y) := by
    intro T
    refine ⟨A.reflexive T, ?_, ?_⟩
    · rintro x y ⟨r, hx, hy⟩
      obtain ⟨r', h1, h2⟩ := A.symmetric T r
      exact ⟨r', h1.trans hy, h2.trans hx⟩
    · rintro x y z ⟨r, hx, hy⟩ ⟨r', hy', hz⟩
      obtain ⟨r'', h1, h2⟩ := A.transitive T r r' (hy.trans hy'.symm)
      exact ⟨r'', h1.trans hx, h2.trans hz⟩
  have haff : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧
      ∀ r : A.relationScheme, A.target r = x → A.source r ∈ U := by
    intro x
    obtain ⟨s, hs, ha, hinv⟩ := A.exists_invariant_affineBasicOpen (Set.finite_singleton x)
    have hx : x ∈ X.basicOpen s := hs (Set.mem_singleton x)
    refine ⟨X.basicOpen s, ha, ?_⟩
    intro r hr
    obtain ⟨g, z, rfl⟩ := (sigmaOpenCover (fun _ : G => X)).exists_eq r
    change G at g
    change X at z
    change A.target ((Sigma.ι (fun _ : G => X) g) z) = x at hr
    change A.source ((Sigma.ι (fun _ : G => X) g) z) ∈ X.basicOpen s
    have ht : A.target (Sigma.ι (fun _ : G => X) g z) = (A.act g).hom z := by
      exact congrArg (fun f : X ⟶ X => f z) (A.ι_target g)
    have hsource : A.source (Sigma.ι (fun _ : G => X) g z) = z := by
      exact congrArg (fun f : X ⟶ X => f z) (A.ι_source g)
    rw [hsource]
    have hz : (A.act g).hom z ∈ X.basicOpen s := by rwa [← ht, hr]
    have hp : (A.act g).hom ⁻¹ᵁ X.basicOpen s = X.basicOpen s := by
      rw [Scheme.preimage_basicOpen_top, hinv]
    exact hp ▸ hz
  obtain ⟨Y, q, w, hfin, hflat, hlfp, hsurj, hpb, ⟨hc⟩⟩ :=
    Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      A.target A.source hj he haff
  let : IsFinite q := hfin
  let : Flat q := hflat
  let : Surjective q := hsurj
  have hq : Etale q := by
    apply MorphismProperty.of_isPullback_of_descendsAlong
      (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb
    · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    · infer_instance
  exact ⟨⟨Y, q, w, hfin, hq, hsurj, hpb, hc⟩⟩

namespace EffectiveQuotient

variable {A} (Q : A.EffectiveQuotient)

@[reassoc (attr := simp)] theorem invariant (g : G) :
    (A.act g).hom ≫ Q.map = Q.map := by
  simpa using congrArg (fun f => Sigma.ι (fun _ : G => X) g ≫ f) Q.condition

/-- Descent of any invariant morphism to a scheme. -/
def desc {Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ g : G, (A.act g).hom ≫ f = f) : Q.scheme ⟶ Y :=
  Q.isColimit.desc (Cofork.ofπ f (AffineQuotient.equalizes f hf))

@[reassoc (attr := simp)] theorem map_desc {Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ g : G, (A.act g).hom ≫ f = f) :
    Q.map ≫ Q.desc f hf = f :=
  Cofork.IsColimit.π_desc Q.isColimit

theorem hom_ext {Y : Scheme.{u}} (f g : Q.scheme ⟶ Y)
    (h : Q.map ≫ f = Q.map ≫ g) : f = g :=
  Cofork.IsColimit.hom_ext Q.isColimit h

/-- An invariant global function descends to a global function on the quotient. -/
theorem exists_desc_invariant_function (s : Γ(X, ⊤))
    (hs : ∀ g : G, (A.act g).hom.appTop s = s) :
    ∃ t : Γ(Q.scheme, ⊤), Q.map.appTop t = s := by
  let e : X ⟶ _ :=
    (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).symm (fun _ => s)
  have he : ∀ g : G, (A.act g).hom ≫ e = e := by
    intro g
    apply (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).injective
    funext i
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp]
    simp only [e, Equiv.apply_symm_apply]
    exact hs g
  refine ⟨AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1} (Q.desc e he) PUnit.unit, ?_⟩
  rw [← AffineSpace.toSpecMvPolyIntEquiv_comp, Q.map_desc]
  simp only [e, Equiv.apply_symm_apply]

/-- Invariant affine principal neighborhoods descend to affine principal neighborhoods. -/
theorem isQuasiAffine [Finite G] [X.IsQuasiAffine] : Q.scheme.IsQuasiAffine := by
  let : CompactSpace Q.scheme :=
    Function.Surjective.compactSpace Q.map.continuous Q.map.surjective
  apply Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen
  intro y
  obtain ⟨x, rfl⟩ := Q.map.surjective y
  obtain ⟨s, hs, haff, hinv⟩ :=
    A.exists_invariant_affineBasicOpen (Set.finite_singleton x)
  obtain ⟨t, ht⟩ := Q.exists_desc_invariant_function s hinv
  have hpre : Q.map ⁻¹ᵁ Q.scheme.basicOpen t = X.basicOpen s := by
    rw [Scheme.preimage_basicOpen_top, ht]
  have hsource : IsAffine (Q.map ⁻¹ᵁ Q.scheme.basicOpen t).toScheme := by
    change IsAffineOpen (Q.map ⁻¹ᵁ Q.scheme.basicOpen t)
    rw [hpre]
    exact haff
  let : IsAffine (Q.map ⁻¹ᵁ Q.scheme.basicOpen t).toScheme := hsource
  let : Surjective (Q.map ∣_ Q.scheme.basicOpen t) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) Q.surjective _
  refine ⟨t, FiniteLocallyFreeQuotient.isAffine_of_finite_flat_surjective
    (Q.map ∣_ Q.scheme.basicOpen t), ?_⟩
  change x ∈ Q.map ⁻¹ᵁ Q.scheme.basicOpen t
  rw [hpre]
  exact hs (Set.mem_singleton x)

end EffectiveQuotient

/-- A chosen effective finite étale quotient, retaining quasi-affineness. -/
def quasiAffineQuotient [Finite G] [X.IsQuasiAffine] :
    {Q : A.EffectiveQuotient // Q.scheme.IsQuasiAffine} :=
  let Q := Classical.choice A.nonempty_effectiveQuotient
  ⟨Q, Q.isQuasiAffine⟩

end FiniteFreeSchemeAction
end Langlands.AlgebraicGeometry

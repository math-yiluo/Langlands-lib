import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalReduction
import Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates

/-! # Separatedness from discrete valuation rings

Tools for Step 2a of Murre's induction (Bourbaki exp. 294): a specialization of points of a
noetherian affine scheme is realized by a discrete valuation ring, and a scheme locally of
finite type over a noetherian affine base whose morphisms from spectra of discrete valuation
rings are determined by their generic points is separated. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompleteLocal

/-- A noetherian local domain that is not a field is dominated by a discrete valuation ring:
there is an injective ring map `D → V` under which the maximal ideal of `V` pulls back to the
maximal ideal of `D`. -/
theorem exists_dvr_dominates {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [IsLocalRing D] (hD : ¬ IsField D) :
    ∃ (V : Type u) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (ι : D →+* V), Function.Injective ι ∧ (maximalIdeal V).comap ι = maximalIdeal D := by
  obtain ⟨V, hV, hVint, hVdom⟩ :=
    IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates hD (FractionRing D)
  let ι : D →+* V := (algebraMap D (FractionRing D)).codRestrict V.toSubring hVint
  refine ⟨V, inferInstance, inferInstance, hV, ι, fun x y hxy ↦ ?_, ?_⟩
  · have := congrArg Subtype.val hxy
    exact IsFractionRing.injective D (FractionRing D) this
  · ext x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff,
      ← ValuationSubring.mem_nonunits_iff, hVdom]
    rfl

/-- A strict inclusion `a < b` of primes of a noetherian ring is realized by a discrete
valuation ring: there is `φ : C → V` with kernel `a` and with `b` the preimage of the maximal
ideal. -/
theorem exists_dvr_of_lt {C : Type u} [CommRing C] [IsNoetherianRing C] {a b : Ideal C}
    [ha : a.IsPrime] [hb : b.IsPrime] (hab : a < b) :
    ∃ (V : Type u) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (φ : C →+* V), RingHom.ker φ = a ∧ (maximalIdeal V).comap φ = b := by
  let b' : Ideal (C ⧸ a) := b.map (Ideal.Quotient.mk a)
  have hb' : b'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hab.le)
  have hinj : Function.Injective (algebraMap (C ⧸ a) (Localization.AtPrime b')) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors b')
  have : IsDomain (Localization.AtPrime b') :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors b')
  have hD : ¬ IsField (Localization.AtPrime b') := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    obtain ⟨x, hxb, hxa⟩ := SetLike.exists_of_lt hab
    intro h
    have hx : algebraMap (C ⧸ a) (Localization.AtPrime b') (Ideal.Quotient.mk a x) ∈
        maximalIdeal (Localization.AtPrime b') := by
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ b']
      exact Ideal.mem_map_of_mem _ hxb
    rw [h, Ideal.mem_bot, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact hxa hx
  obtain ⟨V, _, _, hV, ι, hι, hιm⟩ := exists_dvr_dominates hD
  refine ⟨V, inferInstance, inferInstance, hV,
    (ι.comp (algebraMap (C ⧸ a) (Localization.AtPrime b'))).comp (Ideal.Quotient.mk a), ?_, ?_⟩
  · ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply, map_eq_zero_iff _ hι,
      map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
  · ext x
    rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply, ← Ideal.mem_comap, hιm,
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ b']
    exact Ideal.mem_quotient_iff_mem hab.le

section Points

/-- `Spec` of a ring map out of a field is flat. -/
lemma flat_specMap_of_isField {A B : CommRingCat.{u}} (hA : IsField A) (d : A ⟶ B) :
    Flat (Spec.map d) := by
  rw [Flat.SpecMap_iff]
  let := hA.toField
  let := d.hom.toAlgebra
  show Module.Flat A B
  infer_instance

/-- `Spec` of a ring map between fields is surjective. -/
lemma surjective_specMap_of_isField {A B : CommRingCat.{u}} (hA : IsField A) (hB : IsField B)
    (d : A ⟶ B) : Surjective (Spec.map d) := by
  let := hA.toField
  let := hB.toField
  refine ⟨fun x ↦ ⟨closedPoint B, ?_⟩⟩
  exact Subsingleton.elim (α := PrimeSpectrum A) _ _

/-- `Spec` of a ring map between fields is an epimorphism of schemes (it is flat and
surjective). -/
lemma epi_specMap_of_isField {A B : CommRingCat.{u}} (hA : IsField A) (hB : IsField B)
    (d : A ⟶ B) : Epi (Spec.map d) := by
  have := flat_specMap_of_isField hA d
  have := surjective_specMap_of_isField hA hB d
  exact Flat.epi_of_flat_of_surjective _

/-- Two morphisms that agree after a morphism from the spectrum of a field `K` agree after
`Spec κ(x) ⟶ X`, `x` the image point. -/
lemma fromSpecResidueField_comp_eq {X Y : Scheme.{u}} {g₁ g₂ : X ⟶ Y} {K : Type u} [Field K]
    (α : Spec (CommRingCat.of K) ⟶ X) (h : α ≫ g₁ = α ≫ g₂) :
    X.fromSpecResidueField (α (closedPoint K)) ≫ g₁ =
      X.fromSpecResidueField (α (closedPoint K)) ≫ g₂ := by
  have e := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X α
  rw [← e, Category.assoc, Category.assoc] at h
  have : Epi (Spec.map (X.descResidueField (Scheme.stalkClosedPointTo α))) :=
    epi_specMap_of_isField (Field.toIsField _) (Field.toIsField K) _
  exact (cancel_epi _).1 h

/-- Conversely, agreement after `Spec κ(x) ⟶ X` gives agreement after every morphism from the
spectrum of a field with image `x`. -/
lemma comp_eq_of_fromSpecResidueField {X Y : Scheme.{u}} {g₁ g₂ : X ⟶ Y} {x : X}
    (h : X.fromSpecResidueField x ≫ g₁ = X.fromSpecResidueField x ≫ g₂) {L : Type u} [Field L]
    (β : Spec (CommRingCat.of L) ⟶ X) (hβ : β (closedPoint L) = x) : β ≫ g₁ = β ≫ g₂ := by
  subst hβ
  rw [← Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L X β,
    Category.assoc, Category.assoc, h]

/-- A specialization `a ⤳ b`, `a ≠ b`, of points of an affine scheme with noetherian ring of
global sections is realized by a morphism from the spectrum of a discrete valuation ring `V`
sending the closed point to `b` and the generic point to `a`. -/
theorem exists_dvr_spec {P : Scheme.{u}} [IsAffine P] [IsNoetherianRing Γ(P, ⊤)] {a b : P}
    (hab : a ⤳ b) (hne : a ≠ b) :
    ∃ (V : Type u) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (n : Spec (CommRingCat.of V) ⟶ P), n (closedPoint V) = b ∧
        (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ n)
          (closedPoint (FractionRing V)) = a := by
  let e := P.isoSpec
  have hinv : ∀ z : P, e.inv (e.hom z) = z := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl
  have h1 : (e.hom a).asIdeal < (e.hom b).asIdeal := by
    refine lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes _ _).2
      (hab.map e.hom.continuous)) fun h ↦ hne ?_
    rw [← hinv a, ← hinv b, PrimeSpectrum.ext h]
  have := (e.hom a).isPrime
  have := (e.hom b).isPrime
  obtain ⟨V, _, _, hV, φ, hker, hm⟩ := exists_dvr_of_lt h1
  refine ⟨V, inferInstance, inferInstance, hV, Spec.map (CommRingCat.ofHom φ) ≫ e.inv, ?_, ?_⟩
  · have : Spec.map (CommRingCat.ofHom φ) (closedPoint V) = e.hom b := PrimeSpectrum.ext hm
    show e.inv (Spec.map (CommRingCat.ofHom φ) (closedPoint V)) = b
    rw [this, hinv]
  · have : (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫
        Spec.map (CommRingCat.ofHom φ)) (closedPoint (FractionRing V)) = e.hom a := by
      apply PrimeSpectrum.ext
      change Ideal.comap φ (Ideal.comap (algebraMap V (FractionRing V))
        (maximalIdeal (FractionRing V))) = _
      rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V)),
        ← RingHom.ker_eq_comap_bot, hker]
    show e.inv ((Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫
        Spec.map (CommRingCat.ofHom φ)) (closedPoint (FractionRing V))) = a
    rw [this, hinv]

end Points

section Separated

variable {R : CommRingCat.{u}} [IsNoetherianRing R] {Y : Scheme.{u}} (q : Y ⟶ Spec R)

/-- Every point of the spectrum of a local ring specializes to the closed point, so a morphism
from it whose closed point lands in an open `U` has range in `U`. -/
lemma range_subset_of_closedPoint_mem {W : Type u} [CommRing W] [IsLocalRing W]
    (l : Spec (CommRingCat.of W) ⟶ Y) (U : Y.Opens) (hU : l (closedPoint W) ∈ U) :
    Set.range l ⊆ (U : Set Y) := by
  rintro _ ⟨z, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint z).map l.continuous).mem_open U.isOpen hU

variable [LocallyOfFiniteType q]

/-- The uniqueness part of the valuative criterion, for `q` locally of finite type over a
noetherian affine base, from its discrete valuation ring case. -/
lemma eq_of_dvr
    (h : ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      (l₁ l₂ : Spec (CommRingCat.of V) ⟶ Y), l₁ ≫ q = l₂ ≫ q →
      Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ l₁ =
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ l₂ → l₁ = l₂)
    {W : Type u} [CommRing W] [IsDomain W] [ValuationRing W] {K : Type u} [Field K]
    [Algebra W K] [IsFractionRing W K] (l₁ l₂ : Spec (CommRingCat.of W) ⟶ Y)
    (hq : l₁ ≫ q = l₂ ≫ q)
    (hK : Spec.map (CommRingCat.ofHom (algebraMap W K)) ≫ l₁ =
      Spec.map (CommRingCat.ofHom (algebraMap W K)) ≫ l₂) : l₁ = l₂ := by
  have := LocallyOfFiniteType.isLocallyNoetherian q
  let c := closedPoint W
  let γ := Spec.map (CommRingCat.ofHom (algebraMap W K))
  obtain ⟨U₁, hU₁, hy₁, -⟩ := exists_isAffineOpen_mem_and_subset (x := l₁ c) (U := ⊤) trivial
  obtain ⟨U₂, hU₂, hy₂, -⟩ := exists_isAffineOpen_mem_and_subset (x := l₂ c) (U := ⊤) trivial
  have : IsAffine U₁ := hU₁
  have : IsAffine U₂ := hU₂
  let l₁' := IsOpenImmersion.lift U₁.ι l₁
    (by rw [Scheme.Opens.range_ι]; exact range_subset_of_closedPoint_mem l₁ U₁ hy₁)
  have hl₁' : l₁' ≫ U₁.ι = l₁ := IsOpenImmersion.lift_fac _ _ _
  let l₂'' := IsOpenImmersion.lift U₂.ι l₂
    (by rw [Scheme.Opens.range_ι]; exact range_subset_of_closedPoint_mem l₂ U₂ hy₂)
  have hl₂'' : l₂'' ≫ U₂.ι = l₂ := IsOpenImmersion.lift_fac _ _ _
  -- the two closed points agree
  have key : l₁ c = l₂ c := by
    let P := pullback (U₁.ι ≫ q) (U₂.ι ≫ q)
    have : IsLocallyNoetherian P :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (U₁.ι ≫ q) (U₂.ι ≫ q) ≫ U₁.ι ≫ q)
    have : IsNoetherianRing Γ(P, ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top P⟩
    let m : Spec (CommRingCat.of W) ⟶ P := pullback.lift l₁' l₂'' (by
      rw [← Category.assoc, hl₁', ← Category.assoc, hl₂'', hq])
    let g₁ : P ⟶ Y := pullback.fst _ _ ≫ U₁.ι
    let g₂ : P ⟶ Y := pullback.snd _ _ ≫ U₂.ι
    have hm₁ : m ≫ g₁ = l₁ := by simp only [m, g₁, pullback.lift_fst_assoc, hl₁']
    have hm₂ : m ≫ g₂ = l₂ := by simp only [m, g₂, pullback.lift_snd_assoc, hl₂'']
    have hg : g₁ ≫ q = g₂ ≫ q := by simpa [g₁, g₂] using pullback.condition
    let a := (γ ≫ m) (closedPoint K)
    let b := m c
    have hab : a ⤳ b := by
      change m (γ (closedPoint K)) ⤳ m c
      exact (IsLocalRing.specializes_closedPoint _).map m.continuous
    have hι : P.fromSpecResidueField a ≫ g₁ = P.fromSpecResidueField a ≫ g₂ :=
      fromSpecResidueField_comp_eq (γ ≫ m) (by
        rw [Category.assoc, Category.assoc, hm₁, hm₂]; exact hK)
    have hb : g₁ b = g₂ b := by
      by_cases hne : a = b
      · rw [← hne]
        have := congrArg (fun f : Spec (P.residueField a) ⟶ Y ↦ f (closedPoint _)) hι
        have h2 : P.fromSpecResidueField a (closedPoint (P.residueField a)) = a :=
          Scheme.fromSpecResidueField_apply _ _
        calc g₁ a = g₁ (P.fromSpecResidueField a (closedPoint (P.residueField a))) := by rw [h2]
          _ = g₂ (P.fromSpecResidueField a (closedPoint (P.residueField a))) := this
          _ = g₂ a := by rw [h2]
      · obtain ⟨V, _, _, _, n, hnc, hng⟩ := exists_dvr_spec hab hne
        have hn : n ≫ g₁ = n ≫ g₂ := by
          apply h V
          · simp only [Category.assoc, hg]
          · rw [← Category.assoc, ← Category.assoc]
            exact comp_eq_of_fromSpecResidueField hι _ hng
        have := congrArg (fun f : Spec (CommRingCat.of V) ⟶ Y ↦ f (closedPoint V)) hn
        have h3 : g₁ (n (closedPoint V)) = g₂ (n (closedPoint V)) := this
        rwa [hnc] at h3
    rw [← hm₁, ← hm₂]
    exact hb
  -- both morphisms factor through the affine open `U₁`
  let l₂' := IsOpenImmersion.lift U₁.ι l₂
    (by rw [Scheme.Opens.range_ι]; exact range_subset_of_closedPoint_mem l₂ U₁ (key ▸ hy₁))
  have hl₂' : l₂' ≫ U₁.ι = l₂ := IsOpenImmersion.lift_fac _ _ _
  have hsep : IsSeparated (U₁.ι ≫ q) := IsSeparated.of_isAffineHom _
  let S : ValuativeCommSq (U₁.ι ≫ q) := ⟨W, K, γ ≫ l₁', l₁ ≫ q, ⟨by
    rw [Category.assoc, ← Category.assoc l₁', hl₁']⟩⟩
  have hsub : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion _ S
  have := hsub.elim ⟨l₁', rfl, by rw [← Category.assoc, hl₁']⟩
    ⟨l₂', by
      rw [← cancel_mono U₁.ι]
      change γ ≫ l₂' ≫ U₁.ι = γ ≫ l₁' ≫ U₁.ι
      rw [hl₁', hl₂']; exact hK.symm,
     by rw [← Category.assoc, hl₂']; exact hq.symm⟩
  have h' : l₁' = l₂' := congrArg CommSq.LiftStruct.l this
  rw [← hl₁', ← hl₂', h']

/-- A scheme locally of finite type over a noetherian affine base is separated as soon as
morphisms from spectra of discrete valuation rings are determined by their restrictions to the
generic point. -/
theorem isSeparated_of_dvr
    (h : ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      (l₁ l₂ : Spec (CommRingCat.of V) ⟶ Y), l₁ ≫ q = l₂ ≫ q →
      Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ l₁ =
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ l₂ → l₁ = l₂) :
    IsSeparated q := by
  have := LocallyOfFiniteType.isLocallyNoetherian q
  apply IsSeparated.of_valuativeCriterion
  intro S
  constructor
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩
  have := eq_of_dvr q h (K := S.K) l₁ l₂ (hl₁'.trans hl₂'.symm) (hl₁.trans hl₂.symm)
  subst this
  rfl

/-- A presheaf satisfying (F6) that is represented by a scheme locally of finite type over a
noetherian affine base is represented by a separated scheme. -/
theorem isSeparated_of_representableBy {F : (Over (Spec R))ᵒᵖ ⥤ Type v}
    (hF : ValuativeSeparation F) (e : F.RepresentableBy (Over.mk q)) : IsSeparated q := by
  apply isSeparated_of_dvr q
  intro V _ _ _ l₁ l₂ hq hK
  let m₁ : Over.mk (l₁ ≫ q) ⟶ Over.mk q := Over.homMk l₁ rfl
  let m₂ : Over.mk (l₁ ≫ q) ⟶ Over.mk q := Over.homMk l₂ hq.symm
  have hx : e.homEquiv m₁ = e.homEquiv m₂ := by
    apply hF V (l₁ ≫ q)
    rw [← e.homEquiv_comp, ← e.homEquiv_comp]
    congr 1
    ext
    simpa [algebraOverBase, m₁, m₂] using hK
  have := congrArg CommaMorphism.left (e.homEquiv.injective hx)
  simpa [m₁, m₂] using this

end Separated

end CompleteLocal

end Langlands.AlgebraicGeometry.UnramifiedFunctor

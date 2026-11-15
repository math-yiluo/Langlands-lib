import Langlands.GroupScheme.Reductive.LocalSplitPositiveCell

/-! # Products of positive root points over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

section Localizations

/-- A global function on `Spec B` whose restrictions to the spectra of all localizations of `B`
at maximal ideals vanish is zero. -/
theorem eq_zero_of_specLocalization {B : Type u} [CommRing B]
    (a : Γ(Spec (CommRingCat.of B), ⊤))
    (h : ∀ (p : Ideal B) [p.IsMaximal],
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime p)))).appTop a = 0) :
    a = 0 := by
  obtain ⟨b, rfl⟩ : ∃ b, (Scheme.ΓSpecIso (CommRingCat.of B)).inv b = a :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom a, Iso.hom_inv_id_apply _ _⟩
  have hb : b = 0 := by
    refine eq_zero_of_localization b fun p hp => ?_
    have h' := h p
    rw [specMap_appTop_ΓSpecIso_inv] at h'
    have h'' := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime p))).hom h'
    rwa [Iso.inv_hom_id_apply, map_zero] at h''
  rw [hb, map_zero]

/-- The closed point of the localization at a prime maps to that prime. -/
theorem specMap_algebraMap_closedPoint {B : Type u} [CommRing B] (x : PrimeSpectrum B) :
    Spec.map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime x.asIdeal)))
      (IsLocalRing.closedPoint (Localization.AtPrime x.asIdeal)) = x := by
  rw [Spec.map_apply]
  refine PrimeSpectrum.ext ?_
  exact Localization.AtPrime.under_maximalIdeal

end Localizations

section RingPoints

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}
  {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}

/-- A product of positive cell factors is the cell point with zero negative coordinates and
trivial torus coordinate. -/
theorem mkCellPoint_zero_one_comp_cellMap (neg : Fin m → J) (pos : Fin n → J)
    (Z : Over (Spec (CommRingCat.of R))) (z : Fin n → Γ(Z.left, ⊤)) :
    mkCellPoint Z 0 1 z ≫ cellMap i u neg pos = orderedProduct u pos Z z := by
  have ht : torusCoord (mkCellPoint (I := I) Z (0 : Fin m → Γ(Z.left, ⊤)) 1 z) = 1 :=
    (splitTorus.pointsEquiv I Z).injective (by rw [torusCoord_mkCellPoint, map_one])
  rw [comp_cellMap, cellPoint, negCoord_mkCellPoint, posCoord_mkCellPoint, ht,
    orderedProduct_zero, MonObj.one_comp, one_mul, one_mul]

/-- The coordinates of a product of positive cell factors are unique. -/
theorem orderedProduct_pos_injective [IsOpenImmersion (cellMap i u neg pos).left]
    (Z : Over (Spec (CommRingCat.of R))) :
    Function.Injective (orderedProduct u pos Z) := by
  have : Mono (cellMap i u neg pos) := Over.mono_of_mono_left _
  intro z z' h
  rw [← mkCellPoint_zero_one_comp_cellMap (i := i) neg pos,
    ← mkCellPoint_zero_one_comp_cellMap (i := i) neg pos] at h
  have h' := (cancel_mono (cellMap i u neg pos)).mp h
  have h'' := congrArg posCoord h'
  rwa [posCoord_mkCellPoint, posCoord_mkCellPoint] at h''

/-- **Products of positive root points over arbitrary rings.** The hypotheses are those of
`exists_orderedProduct_eq_pos`, but the test ring `B` is an arbitrary commutative ring. -/
theorem exists_orderedProduct_eq_pos_of_ring [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    {r : ℕ} (e : Fin r → J) (he : ∀ k, 0 < coPairing (ch (e k)) ν)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (c : Fin r → Γ((Over.mk s).left, ⊤)) :
    ∃ z : Fin n → Γ((Over.mk s).left, ⊤),
      orderedProduct u e (Over.mk s) c = orderedProduct u pos (Over.mk s) z := by
  classical
  have : Mono (cellMap i u neg pos) := Over.mono_of_mono_left _
  set g := orderedProduct u e (Over.mk s) c with hg
  -- the localizations of `B` at its primes
  have hloc : ∀ x : PrimeSpectrum B, ∃ z : Fin n → Γ(Spec (CommRingCat.of
      (Localization.AtPrime x.asIdeal)), ⊤),
      specHom (algebraMap B (Localization.AtPrime x.asIdeal)) rfl ≫ g =
        mkCellPoint (Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap B (Localization.AtPrime x.asIdeal))) ≫ s)) 0 1 z ≫
          cellMap i u neg pos := by
    intro x
    obtain ⟨z, hz⟩ := exists_orderedProduct_eq_pos (pos := pos) hu ν hneg e he
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime x.asIdeal))) ≫ s)
      (fun k => (specHom (algebraMap B (Localization.AtPrime x.asIdeal)) rfl).left.appTop (c k))
    refine ⟨z, ?_⟩
    rw [mkCellPoint_zero_one_comp_cellMap, ← hz, hg, comp_orderedProduct]
  choose zl hzl using hloc
  -- the product lies in the open cell
  have hrange : Set.range g.left ⊆ Set.range (cellMap i u neg pos).left := by
    rintro _ ⟨x, rfl⟩
    rw [← specMap_algebraMap_closedPoint x]
    change (specHom (algebraMap B (Localization.AtPrime x.asIdeal)) rfl ≫ g).left _ ∈ _
    rw [hzl x]
    exact ⟨_, rfl⟩
  let y : Over.mk s ⟶ cellObj R I m n :=
    Over.homMk (IsOpenImmersion.lift (cellMap i u neg pos).left g.left hrange) (by
      rw [← Over.w (cellMap i u neg pos), ← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w g)
  have hy : y ≫ cellMap i u neg pos = g := by
    ext1
    exact IsOpenImmersion.lift_fac _ _ _
  have hyl : ∀ x : PrimeSpectrum B,
      specHom (algebraMap B (Localization.AtPrime x.asIdeal)) rfl ≫ y =
        mkCellPoint _ 0 1 (zl x) := by
    intro x
    apply (cancel_mono (cellMap i u neg pos)).mp
    rw [Category.assoc, hy, hzl x]
  -- the negative coordinates vanish
  have hneg0 : negCoord y = 0 := by
    funext k
    refine eq_zero_of_specLocalization _ fun p hp => ?_
    have h := congrArg (fun w => negCoord w k) (hyl ⟨p, hp.isPrime⟩)
    simp only [negCoord_comp, negCoord_mkCellPoint] at h
    exact h
  -- the torus coordinate is trivial
  have htor : torusCoord y = 1 := by
    apply (splitTorus.pointsEquiv I _).injective
    rw [map_one]
    funext j
    apply Units.ext
    rw [Pi.one_apply, Units.val_one, ← sub_eq_zero]
    refine eq_zero_of_specLocalization _ fun p hp => ?_
    have h := congrArg (fun w => splitTorus.pointsEquiv I _ (torusCoord w) j)
      (hyl ⟨p, hp.isPrime⟩)
    simp only [torusCoord_comp, splitTorus.pointsEquiv_naturality, torusCoord_mkCellPoint,
      Pi.one_apply] at h
    have h2 := congrArg Units.val h
    rw [map_sub, map_one, sub_eq_zero]
    exact h2
  refine ⟨posCoord y, ?_⟩
  rw [← hy, comp_cellMap, cellPoint, hneg0, htor, orderedProduct_zero, MonObj.one_comp,
    one_mul, one_mul]

/-- Existence and uniqueness of the positive cell coordinates of a product of positive root
points over an arbitrary ring. -/
theorem existsUnique_orderedProduct_eq_pos_of_ring [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    {r : ℕ} (e : Fin r → J) (he : ∀ k, 0 < coPairing (ch (e k)) ν)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (c : Fin r → Γ((Over.mk s).left, ⊤)) :
    ∃! z : Fin n → Γ((Over.mk s).left, ⊤),
      orderedProduct u e (Over.mk s) c = orderedProduct u pos (Over.mk s) z := by
  obtain ⟨z, hz⟩ := exists_orderedProduct_eq_pos_of_ring (pos := pos) hu ν hneg e he s c
  exact ⟨z, hz, fun z' hz' => orderedProduct_pos_injective (i := i) (neg := neg) _
    (hz'.symm.trans hz)⟩

end RingPoints

section RootFamilies

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- **Products of positive root points over arbitrary rings, for root families.** -/
theorem existsUnique_orderedProduct_eq_pos_of_isPos (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base) {u : J → (Ga R ⟶ G)}
    (hu : ∀ α, IsRootParametrization i (P.root α) (u α)) {m n : ℕ}
    (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    {r : ℕ} (e : Fin r → J) (he : ∀ k, b.IsPos (e k)) (c : Fin r → Γ((Over.mk s).left, ⊤)) :
    ∃! z : Fin n → Γ((Over.mk s).left, ⊤),
      orderedProduct u e (Over.mk s) c =
        orderedProduct u (fun k => (pos k : J)) (Over.mk s) z := by
  have := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b u hu neg pos
  obtain ⟨ν, hνpos, hνneg⟩ := exists_cocharacter_of_base P b
  exact existsUnique_orderedProduct_eq_pos_of_ring (ch := fun α => P.root α)
    (neg := fun k => (neg k : J)) (fun α Z t c => (hu α).equivariant Z t c) ν
    (fun k => hνneg _ (neg k).2) e (fun k => hνpos _ (he k)) s c

end RootFamilies

end LocalSplitCell

open LocalSplitCell in
/-- **Products of positive root points over arbitrary rings.** Let `G` be reductive over a
commutative ring `R`, with a fibrewise maximal coordinate split torus `i`, a fibrewise root
datum `P`, a base `b` and actual root parametrizations `u` of all roots. Enumerate the
non-positive and the positive roots by `neg` and `pos`. Then for every commutative ring `B`
with a morphism `Spec B ⟶ Spec R` and every finite list of positive roots with coordinates in
`B`, the product of the corresponding root points equals `∏ₖ u_{pos k}(z k)` for exactly one
coordinate vector `z`. -/
def LocalSplitPositiveProductRingStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type u) [Fintype I] (J : Type u)
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom], IsReductive G →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      ∀ (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
      ∀ (b : P.Base) (u : J → (Ga R ⟶ G)), (∀ α, IsRootParametrization i (P.root α) (u α)) →
      ∀ (m n : ℕ) (_neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
        (B : Type u) [CommRing B]
        (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (r : ℕ) (e : Fin r → J),
        (∀ k, b.IsPos (e k)) → ∀ c : Fin r → Γ((Over.mk s).left, ⊤),
        ∃! z : Fin n → Γ((Over.mk s).left, ⊤),
          orderedProduct u e (Over.mk s) c =
            orderedProduct u (fun k => (pos k : J)) (Over.mk s) z

/-- Products of positive root points have unique positive cell coordinates over every ring. -/
theorem localSplitPositiveProductRing : LocalSplitPositiveProductRingStatement.{u} := by
  intro R _ I _ J G _ hG i hmax P hP b u hu m n neg pos B _ s r e he c
  exact LocalSplitCell.existsUnique_orderedProduct_eq_pos_of_isPos hG hmax hP b hu neg pos s e
    he c

end Langlands.GroupScheme

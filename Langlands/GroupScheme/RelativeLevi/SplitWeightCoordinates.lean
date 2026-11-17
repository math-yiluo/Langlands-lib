import Langlands.GroupScheme.Reductive.SplitBorelPositiveCoordinates

/-! # Positive-weight coordinates of actual contracting points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}
  {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}

open Polynomial GenericLine in
/-- Contracting points over local test rings have cell coordinates supported on strictly positive weights. -/
theorem exists_orderedProduct_supported_of_mem_unipotent
    [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ)
    (hneg : ∀ k, coPairing (ch (neg k)) ν ≤ 0)
    {B : Type u} [CommRing B] [IsLocalRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (g : Over.mk s ⟶ G.X)
    (hg : g ∈ (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).carrier _) :
    ∃ z : Fin n → Γ((Over.mk s).left, ⊤),
      g = orderedProduct u pos (Over.mk s) z ∧
      ∀ k, coPairing (ch (pos k)) ν ≤ 0 → z k = 0 := by
  classical
  have : Mono (cellMap i u neg pos) := Over.mono_of_mono_left _
  obtain ⟨E, hE, hE0⟩ := hg
  let S : ∀ {W : Over (Spec (CommRingCat.of R))}, (W ⟶ Over.mk s) → Γ(W.left, ⊤) →
      (W ⟶ G.X) := fun f t => lift f ((AffineLine.homEquiv _).symm t) ≫ E
  have hS_comp : ∀ {W W' : Over (Spec (CommRingCat.of R))} (k : W' ⟶ W)
      (f : W ⟶ Over.mk s) (t : Γ(W.left, ⊤)),
      k ≫ S f t = S (k ≫ f) (k.left.appTop t) := by
    intro W W' k f t
    dsimp only [S]
    rw [← Category.assoc, comp_lift]
    congr 2
    apply AffineLine.hom_ext
    rw [AffineLine.homEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hS_zero : ∀ {W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Over.mk s), S f 0 = 1 := by
    intro W f
    have hz : (AffineLine.homEquiv W).symm 0 =
        toUnit W ≫ AffineLine.zeroSection _ := by
      apply AffineLine.hom_ext
      rw [Equiv.apply_symm_apply, AffineLine.homEquiv_comp_zeroSection]
    dsimp only [S]
    rw [hz]
    have hl : lift f (toUnit W ≫ AffineLine.zeroSection _) =
        f ≫ lift (𝟙 _) (toUnit _ ≫ AffineLine.zeroSection _) := by
      ext <;> simp
    rw [hl, Category.assoc, ← Dynamic.evalZero, hE0, MonObj.comp_one]
  have hS_unit : ∀ {W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Over.mk s)
      (t : (Γ(W.left, ⊤))ˣ), S f t =
        (cocharPoint ν W t ≫ i.hom.hom) * (f ≫ g) *
          (cocharPoint ν W t ≫ i.hom.hom)⁻¹ := by
    intro W f t
    let a := (Gm.pointsEquiv _ W).symm t
    have ht : (AffineLine.homEquiv W).symm (t : Γ(W.left, ⊤)) =
        a ≫ AffineLine.unitInclusion _ := by
      apply AffineLine.hom_ext
      rw [Equiv.apply_symm_apply, AffineLine.homEquiv_comp_unitInclusion]
      simp only [a, MulEquiv.apply_symm_apply]
    have hl : lift f (a ≫ AffineLine.unitInclusion _) =
        lift f a ≫ (Over.mk s ◁ AffineLine.unitInclusion _) := by
      ext <;> simp
    dsimp only [S]
    rw [ht, hl, Category.assoc, hE]
    simp only [Dynamic.orbit, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc,
      lift_fst_assoc, AffineRegularBorel.cocharacter, Grp.comp_hom_hom]
    rw [cocharPoint_eq_comp, Category.assoc]
  -- the local ring of the line at `X = 0`
  let ι₀ : B →+* AtPoint B 0 := (algebraMap B[X] (AtPoint B 0)).comp C
  let s₀ := Spec.map (CommRingCat.ofHom ι₀) ≫ s
  let f₀ : Over.mk s₀ ⟶ Over.mk s := specHom ι₀ rfl
  let t₀ : Γ((Over.mk s₀).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (AtPoint B 0))).inv (algebraMap B[X] (AtPoint B 0) X)
  let E₀ := S f₀ t₀
  let Ev : Over.mk s ⟶ Over.mk s₀ := specHom (evalAt 0) (specMap_evalAt_comp 0 s)
  have hEv : Ev ≫ f₀ = 𝟙 _ :=
    (specHom_comp_eq (by rw [← RingHom.comp_assoc, evalAt_comp_C]) _ _).trans (specHom_id _)
  have hEvt : Ev.left.appTop t₀ = 0 := by
    change (Spec.map (CommRingCat.ofHom (evalAt (0 : B)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (AtPoint B 0))).inv _) = 0
    rw [specMap_appTop_ΓSpecIso_inv, evalAt_algebraMap, Polynomial.eval_X, map_zero]
  have hEvE : Ev ≫ E₀ = 1 := by
    rw [hS_comp, hEv, hEvt, hS_zero]
  have hk₀ : E₀.left (IsLocalRing.closedPoint (AtPoint B 0)) ∈
      Set.range (cellMap i u neg pos).left := by
    have hcl : Ev.left (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint (AtPoint B 0) :=
      IsLocalRing.comap_closedPoint (evalAt (0 : B))
    rw [← hcl]
    change (Ev ≫ E₀).left (IsLocalRing.closedPoint B) ∈ _
    rw [hEvE, ← mkCellPoint_one_comp_cellMap (i := i) (u := u) neg pos]
    exact ⟨_, rfl⟩
  obtain ⟨Y₀, hY₀⟩ := exists_lift_of_localPoint_closedPoint_mem (cellMap i u neg pos) E₀ hk₀
  have hEvY : Ev ≫ Y₀ = mkCellPoint _ 0 1 0 := by
    apply (cancel_mono (cellMap i u neg pos)).mp
    rw [Category.assoc, hY₀, hEvE, mkCellPoint_one_comp_cellMap]
  -- the generic point of the closed fibre
  let κ : AtPoint B 0 →+* Generic B := toGeneric 0
  let sG := Spec.map (CommRingCat.ofHom κ) ≫ s₀
  let fG : Over.mk sG ⟶ Over.mk s₀ := specHom κ rfl
  have hX : IsUnit (κ (algebraMap B[X] (AtPoint B 0) X)) := by
    rw [toGeneric_algebraMap]
    exact IsLocalization.map_units (Generic B)
      (⟨X, X_notMem_genericIdeal B⟩ : (genericIdeal B).primeCompl)
  let uG : (Γ((Over.mk sG).left, ⊤))ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of (Generic B))).inv.hom.toMonoidHom hX.unit
  have huG : (uG : Γ((Over.mk sG).left, ⊤)) = fG.left.appTop t₀ := by
    change (Scheme.ΓSpecIso (CommRingCat.of (Generic B))).inv (κ _) =
      (Spec.map (CommRingCat.ofHom κ)).appTop ((Scheme.ΓSpecIso (CommRingCat.of _)).inv _)
    rw [specMap_appTop_ΓSpecIso_inv]
  let Y' := mkCellPoint (Over.mk sG)
    (fun k => Ring.inverse (torusChar (ch (neg k)) _ (cocharPoint ν (Over.mk sG) uG)) *
      negCoord (fG ≫ Y₀) k)
    (splitTorus.pointsEquiv I _ (torusCoord (fG ≫ Y₀)))
    (fun k => Ring.inverse (torusChar (ch (pos k)) _ (cocharPoint ν (Over.mk sG) uG)) *
      posCoord (fG ≫ Y₀) k)
  have hG : (fG ≫ f₀) ≫ g = Y' ≫ cellMap i u neg pos := by
    have h1 : fG ≫ E₀ = (cocharPoint ν (Over.mk sG) uG ≫ i.hom.hom) * ((fG ≫ f₀) ≫ g) *
        (cocharPoint ν (Over.mk sG) uG ≫ i.hom.hom)⁻¹ := by
      rw [hS_comp, ← huG, hS_unit]
    rw [← hY₀, ← Category.assoc] at h1
    rw [← torus_inv_mul_cellMap_mul hu neg pos (fG ≫ Y₀), h1]
    group
  -- the product lies in the cell
  have hloc := isLocalHom_algebraMap_generic_comp_C B
  have hfG : (fG ≫ f₀).left = Spec.map (CommRingCat.ofHom ((algebraMap B[X] (Generic B)).comp C)) := by
    rw [Over.comp_left, specHom_left, specHom_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    rw [← RingHom.comp_assoc, toGeneric_comp]
  have hkB : g.left (IsLocalRing.closedPoint B) ∈ Set.range (cellMap i u neg pos).left := by
    have hcl : (fG ≫ f₀).left (IsLocalRing.closedPoint (Generic B)) =
        IsLocalRing.closedPoint B := by
      rw [hfG]
      exact IsLocalRing.comap_closedPoint ((algebraMap B[X] (Generic B)).comp C)
    rw [← hcl]
    change ((fG ≫ f₀) ≫ g).left (IsLocalRing.closedPoint (Generic B)) ∈ _
    rw [hG]
    exact ⟨_, rfl⟩
  obtain ⟨y, hy⟩ := exists_lift_of_localPoint_closedPoint_mem (cellMap i u neg pos) g hkB
  let y₀ := f₀ ≫ y
  have hy₀ : fG ≫ y₀ = Y' := by
    apply (cancel_mono (cellMap i u neg pos)).mp
    rw [Category.assoc, Category.assoc, hy, ← Category.assoc, hG]
  have hEvy : Ev ≫ y₀ = y := by
    rw [← Category.assoc, hEv, Category.id_comp]
  have hinj := specMap_appTop_injective κ (toGeneric_injective 0)
  -- the negative coordinates vanish
  have hneg0 : negCoord y = 0 := by
    funext k
    obtain ⟨q, hq⟩ : ∃ q : ℕ, coPairing (ch (neg k)) ν = -q :=
      ⟨(-coPairing (ch (neg k)) ν).toNat, by have := hneg k; omega⟩
    have h1 : negCoord (fG ≫ y₀) k = negCoord Y' k := by rw [hy₀]
    simp only [Y', negCoord_comp, negCoord_mkCellPoint] at h1
    rw [inverse_torusChar_cocharPoint_of_eq hq, huG, ← map_pow, ← map_mul] at h1
    have h2 : negCoord y₀ k = t₀ ^ q * negCoord Y₀ k := hinj h1
    have h3 := congrArg Ev.left.appTop h2
    have hz : Ev.left.appTop (negCoord Y₀ k) = 0 := by
      have h := congrArg (fun y => negCoord y k) hEvY
      simpa only [negCoord_comp, negCoord_mkCellPoint, Pi.zero_apply] using h
    rw [map_mul, hz, mul_zero] at h3
    have h4 : negCoord (Ev ≫ y₀) k = 0 := by rw [negCoord_comp]; exact h3
    rw [hEvy] at h4
    exact h4
  -- nonpositive positive-list coordinates also vanish
  have hpos0 (k : Fin n) (hk : coPairing (ch (pos k)) ν ≤ 0) :
      posCoord y k = 0 := by
    obtain ⟨q, hq⟩ : ∃ q : ℕ, coPairing (ch (pos k)) ν = -q :=
      ⟨(-coPairing (ch (pos k)) ν).toNat, by omega⟩
    have h1 : posCoord (fG ≫ y₀) k = posCoord Y' k := by rw [hy₀]
    simp only [Y', posCoord_comp, posCoord_mkCellPoint] at h1
    rw [inverse_torusChar_cocharPoint_of_eq hq, huG, ← map_pow, ← map_mul] at h1
    have h2 : posCoord y₀ k = t₀ ^ q * posCoord Y₀ k := hinj h1
    have h3 := congrArg Ev.left.appTop h2
    have hz : Ev.left.appTop (posCoord Y₀ k) = 0 := by
      have h := congrArg (fun y => posCoord y k) hEvY
      simpa only [posCoord_comp, posCoord_mkCellPoint, Pi.zero_apply] using h
    rw [map_mul, hz, mul_zero] at h3
    have h4 : posCoord (Ev ≫ y₀) k = 0 := by rw [posCoord_comp]; exact h3
    rw [hEvy] at h4
    exact h4
  -- the torus coordinate is trivial
  have htor : torusCoord y = 1 := by
    apply (splitTorus.pointsEquiv I _).injective
    have hunits : Function.Injective (splitTorus.unitsRestrict I fG) := by
      intro a b hab
      funext j
      apply Units.ext
      exact hinj (congrArg (fun w => ((w j : (Γ((Over.mk sG).left, ⊤))ˣ) : Γ((Over.mk sG).left, ⊤))) hab)
    have h1 : splitTorus.pointsEquiv I _ (torusCoord y₀) =
        splitTorus.pointsEquiv I _ (torusCoord Y₀) := by
      apply hunits
      rw [← splitTorus.pointsEquiv_naturality, ← splitTorus.pointsEquiv_naturality,
        ← torusCoord_comp, ← torusCoord_comp, hy₀]
      simp only [Y', torusCoord_mkCellPoint]
    rw [← hEvy, torusCoord_comp, splitTorus.pointsEquiv_naturality, h1,
      ← splitTorus.pointsEquiv_naturality, ← torusCoord_comp, hEvY, torusCoord_mkCellPoint,
      map_one]
  refine ⟨posCoord y, ?_, hpos0⟩
  rw [← hy, comp_cellMap, cellPoint, hneg0, htor, orderedProduct_zero, MonObj.one_comp,
    one_mul, one_mul]

/-- Contracting points over arbitrary test rings have cell coordinates supported on strictly positive weights. -/
theorem exists_orderedProduct_supported_of_mem_unipotent_of_ring
    [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ)
    (hneg : ∀ k, coPairing (ch (neg k)) ν ≤ 0)
    {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (g : Over.mk s ⟶ G.X)
    (hg : g ∈ (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).carrier _) :
    ∃ z : Fin n → Γ((Over.mk s).left, ⊤),
      g = orderedProduct u pos (Over.mk s) z ∧
      ∀ k, coPairing (ch (pos k)) ν ≤ 0 → z k = 0 := by
  classical
  have : Mono (cellMap i u neg pos) := Over.mono_of_mono_left _
  -- the localizations of `B` at its primes
  have hloc : ∀ x : PrimeSpectrum B, ∃ z : Fin n → Γ(Spec (CommRingCat.of
      (Localization.AtPrime x.asIdeal)), ⊤),
      specHom (algebraMap B (Localization.AtPrime x.asIdeal)) rfl ≫ g =
        mkCellPoint (Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap B (Localization.AtPrime x.asIdeal))) ≫ s)) 0 1 z ≫
          cellMap i u neg pos ∧
      (∀ k, coPairing (ch (pos k)) ν ≤ 0 → z k = 0) := by
    intro x
    obtain ⟨z, hz, hsupport⟩ := exists_orderedProduct_supported_of_mem_unipotent (pos := pos) hu ν hneg
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime x.asIdeal))) ≫ s)
      (specHom (algebraMap B (Localization.AtPrime x.asIdeal)) rfl ≫ g)
      ((Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).comp_mem _ hg)
    refine ⟨z, ?_, hsupport⟩
    rw [mkCellPoint_zero_one_comp_cellMap, hz]
  choose zl hzl hsupport using hloc
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
  have hpos0 (k : Fin n) (hk : coPairing (ch (pos k)) ν ≤ 0) :
      posCoord y k = 0 := by
    refine eq_zero_of_specLocalization _ fun p hp => ?_
    have h := congrArg (fun w => posCoord w k) (hyl ⟨p, hp.isPrime⟩)
    simp only [posCoord_comp, posCoord_mkCellPoint] at h
    exact h.trans (hsupport ⟨p, hp.isPrime⟩ k hk)
  refine ⟨posCoord y, ?_, hpos0⟩
  rw [← hy, comp_cellMap, cellPoint, hneg0, htor, orderedProduct_zero, MonObj.one_comp,
    one_mul, one_mul]

/-- The positive-weight coordinates of a contracting point over an affine test scheme. -/
def positiveWeightCoordinates [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ)
    (hneg : ∀ k, coPairing (ch (neg k)) ν ≤ 0)
    {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (g : Over.mk s ⟶ G.X)
    (hg : g ∈ (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).carrier _) :
    Fin n → Γ((Over.mk s).left, ⊤) :=
  (exists_orderedProduct_supported_of_mem_unipotent_of_ring (pos := pos) hu ν hneg s g hg).choose

/-- The selected positive coordinates recover the given contracting point. -/
theorem orderedProduct_positiveWeightCoordinates [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ)
    (hneg : ∀ k, coPairing (ch (neg k)) ν ≤ 0)
    {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (g : Over.mk s ⟶ G.X)
    (hg : g ∈ (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).carrier _) :
    orderedProduct u pos (Over.mk s) (positiveWeightCoordinates (pos := pos) hu ν hneg s g hg) = g :=
  (exists_orderedProduct_supported_of_mem_unipotent_of_ring (pos := pos) hu ν hneg s g hg).choose_spec.1.symm

/-- The selected supported coordinates are unique among all positive-list coordinates. -/
theorem positiveWeightCoordinates_eq [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ)
    (hneg : ∀ k, coPairing (ch (neg k)) ν ≤ 0)
    {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (g : Over.mk s ⟶ G.X)
    (hg : g ∈ (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).carrier _)
    (z : Fin n → Γ((Over.mk s).left, ⊤)) (hz : orderedProduct u pos (Over.mk s) z = g) :
    positiveWeightCoordinates (pos := pos) hu ν hneg s g hg = z := by
  apply orderedProduct_pos_injective (i := i) (u := u) (neg := neg) (pos := pos) _
  exact (orderedProduct_positiveWeightCoordinates (pos := pos) hu ν hneg s g hg).trans hz.symm

/-- Nonpositive weights have zero selected coordinate. -/
theorem positiveWeightCoordinates_vanish
    [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ)
    (hneg : ∀ k, coPairing (ch (neg k)) ν ≤ 0)
    {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (g : Over.mk s ⟶ G.X)
    (hg : g ∈ (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).carrier _)
    (k : Fin n) (hk : coPairing (ch (pos k)) ν ≤ 0) :
    positiveWeightCoordinates (pos := pos) hu ν hneg s g hg k = 0 :=
  (exists_orderedProduct_supported_of_mem_unipotent_of_ring
    (pos := pos) hu ν hneg s g hg).choose_spec.2 k hk

end Langlands.GroupScheme.LocalSplitCell

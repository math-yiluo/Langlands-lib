import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocus.BundleAgreement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocus.CubicLaws
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocus.DegreeLocus
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocus.EmbeddingAmple
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocus.MultipleLocus
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocus.PolarizationCriterion

/-! # The cubic polarization locus from geometric polarization division -/

noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (P : Prerequisites.{u}) {S T U : Scheme.{u}} (A : AbelianScheme S)

private lemma pullbackMap_nsmul (W : DualWitness A) (b : T ⟶ S)
    (W' : DualWitness ((baseChange b).obj A)) (n : ℕ) (f : A ⟶ W.dual P) :
    W.pullbackMap P b W' (n • f) = n • W.pullbackMap P b W' f := by
  unfold DualWitness.pullbackMap
  rw [Functor.map_nsmul, Preadditive.nsmul_comp]

private lemma lineBundleMumford_eq_of_cubic [IsLocallyNoetherian S] (W : DualWitness A)
    (L : LineBundle A.X.left) (lam : A ⟶ W.dual P) (hpol : W.IsPolarization P lam)
    (hL : ∃ N : LineBundle S, Nonempty (L ≅ LineBundle.tensor P.preservation
      (cubicDiagonalBundle P W lam) ((LineBundle.pullback A.X.hom).obj N))) :
    lineBundleMumford P A W L = 6 • lam :=
  (lineBundleMumford_eq_of_normalizedClass P A W
    ((normalizedBundleClass_eq_iff P A _ _).mpr hL)).trans
    (lineBundleMumford_cubicDiagonal P W lam hpol)

private lemma exists_cubicLocus_over_polarization [IsLocallyNoetherian S] (W : DualWitness A)
    (L : LineBundle A.X.left) (lam : A ⟶ W.dual P) (hpol : W.IsPolarization P lam)
    (hL : lineBundleMumford P A W L = 6 • lam) (d : ℕ) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ S), IsImmersion j ∧
      ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (t : T ⟶ S),
        (∃ t' : T ⟶ Z, t' ≫ j = t) ↔ ExistsCubicPolarization P d ((baseChange t).obj A)
          ((LineBundle.pullback (pullback.fst A.X.hom t)).obj L) := by
  obtain ⟨Y, k, hk, hY⟩ := exists_normalizedBundle_agreementLocus P A L
    (cubicDiagonalBundle P W lam)
  obtain ⟨O, hO⟩ := exists_degreeSquare_locus lam hpol.1 d
  let := hk
  refine ⟨pullback k O.ι, pullback.fst k O.ι ≫ k, inferInstance, fun T _ t ↦ ?_⟩
  let A' := (baseChange t).obj A
  let W' := W.pullback P t
  let lam' := W.pullbackMap P t W' lam
  let L' := (LineBundle.pullback (pullback.fst A.X.hom t)).obj L
  have hpol' : W'.IsPolarization P lam' :=
    P.polarizationBaseChange P.preservation P.square P.universality P.stability P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.compatibility S T t A W.hasDual
      W.geometry W.inverseBundle W.evaluation W'.hasDual W'.geometry W'.inverseBundle W'.evaluation
      lam hpol
  have hL' : lineBundleMumford P A' W' L' = 6 • lam' := by
    rw [← lineBundleMumford_pullback P A W L t W', hL, pullbackMap_nsmul]
  have hfactors : (∃ t' : T ⟶ pullback k O.ι, t' ≫ (pullback.fst k O.ι ≫ k) = t) ↔
      (∃ v : T ⟶ Y, v ≫ k = t) ∧ (∃ w : T ⟶ O.toScheme, w ≫ O.ι = t) := by
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨⟨v ≫ pullback.fst k O.ι, by rwa [Category.assoc]⟩,
        ⟨v ≫ pullback.snd k O.ι, by rwa [Category.assoc, ← pullback.condition]⟩⟩
    · rintro ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
      exact ⟨pullback.lift v w (hv.trans hw.symm), by simp [hv]⟩
  rw [hfactors, hY, hO]
  have hd : HasDegreeSquare ((baseChange t).map lam) d ↔ HasDegreeSquare lam' d := by
    let e := W.baseChangeIso P t W'
    constructor
    · intro h
      exact h.post_iso (hpol.1.baseChange t) e
    · intro h
      have hp := h.post_iso hpol'.1 e.symm
      change HasDegreeSquare (((baseChange t).map lam ≫ e.hom) ≫ e.inv) d at hp
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hp
  rw [hd]
  let e := cubicDiagonalBundlePullbackIso P W lam t W'
  constructor
  · rintro ⟨⟨N, ⟨hN⟩⟩, hd⟩
    exact ⟨W', lam', hpol', hd, N, ⟨hN ≪≫ LineBundle.tensorIso P.preservation e.symm (Iso.refl _)⟩⟩
  · intro h
    obtain ⟨lam₀, hpol₀, hd₀, hC⟩ := existsCubicPolarization_atWitness P W' d L' h
    have heq : lam₀ = lam' :=
      nsmul_hom_injective (by decide : 0 < 6)
        ((lineBundleMumford_eq_of_cubic P A' W' L' lam₀ hpol₀ hC).symm.trans hL')
    obtain ⟨N, ⟨hN⟩⟩ := heq ▸ hC
    exact ⟨⟨N, ⟨hN ≪≫ LineBundle.tensorIso P.preservation e (Iso.refl _)⟩⟩, heq ▸ hd₀⟩

private def successivePullbackBundleIso (b : T ⟶ S) (c : U ⟶ T) (L : LineBundle A.X.left) :
    (LineBundle.pullback (pullback.fst A.X.hom (c ≫ b))).obj L ≅
      (LineBundle.pullback (hom (baseChangeCompIso b c A).hom)).obj
        ((LineBundle.pullback (pullback.fst ((baseChange b).obj A).X.hom c)).obj
          ((LineBundle.pullback (pullback.fst A.X.hom b)).obj L)) := by
  let e := baseChangeCompIso b c A
  let p := pullback.fst A.X.hom b
  let q := pullback.fst ((baseChange b).obj A).X.hom c
  have h : (hom e.hom ≫ q) ≫ p = pullback.fst A.X.hom (c ≫ b) := by
    have hinv : hom e.inv ≫ pullback.fst A.X.hom (c ≫ b) = q ≫ p :=
      GroupScheme.baseChangeCompIso_inv_fst b c A.toGrp
    rw [Category.assoc, ← hinv, ← Category.assoc, ← hom_comp, e.hom_inv_id, hom_id,
      Category.id_comp]
  exact (LineBundle.pullbackCompEqIso (hom e.hom ≫ q) p h L).symm ≪≫
    ((LineBundle.pullbackComp (hom e.hom) q).app ((LineBundle.pullback p).obj L)).symm

private def directPullbackBundleIso (b : T ⟶ S) (c : U ⟶ T) (L : LineBundle A.X.left) :
    (LineBundle.pullback (hom (baseChangeCompIso b c A).inv)).obj
      ((LineBundle.pullback (pullback.fst A.X.hom (c ≫ b))).obj L) ≅
    (LineBundle.pullback (pullback.fst ((baseChange b).obj A).X.hom c)).obj
      ((LineBundle.pullback (pullback.fst A.X.hom b)).obj L) := by
  let e := underlyingSchemeIso (baseChangeCompIso b c A)
  exact (LineBundle.pullback e.inv).mapIso (successivePullbackBundleIso A b c L) ≪≫
    LineBundle.pullbackCompEqIso e.inv e.hom e.inv_hom_id _ ≪≫ (LineBundle.pullbackId _).app _

private lemma geometricallyAmpleBundle_pullback (L : LineBundle A.X.left)
    (hL : GeometricallyAmpleBundle A L) (b : T ⟶ S) :
    GeometricallyAmpleBundle ((baseChange b).obj A)
      ((LineBundle.pullback (pullback.fst A.X.hom b)).obj L) := by
  intro K _ _ s
  let e := underlyingSchemeIso (baseChangeCompIso b s A)
  have he : IsClosedImmersion e.inv := inferInstance
  have h := closedImmersionPullbackAmple _ _ e.inv
    ((LineBundle.pullback (pullback.fst A.X.hom (s ≫ b))).obj L) he (hL K (s ≫ b))
  exact h.of_iso ((LineBundle.forget _).mapIso (directPullbackBundleIso A b s L))

private lemma existsCubicPolarization_comp_iff [QuasiSeparatedSpace U] (b : T ⟶ S) (c : U ⟶ T)
    (L : LineBundle A.X.left) (d : ℕ) :
    ExistsCubicPolarization P d ((baseChange (c ≫ b)).obj A)
      ((LineBundle.pullback (pullback.fst A.X.hom (c ≫ b))).obj L) ↔
    ExistsCubicPolarization P d ((baseChange c).obj ((baseChange b).obj A))
      ((LineBundle.pullback (pullback.fst ((baseChange b).obj A).X.hom c)).obj
        ((LineBundle.pullback (pullback.fst A.X.hom b)).obj L)) :=
  ⟨existsCubicPolarization_of_iso P (baseChangeCompIso b c A).symm d
    (directPullbackBundleIso A b c L).symm,
    existsCubicPolarization_of_iso P (baseChangeCompIso b c A) d (successivePullbackBundleIso A b c L)⟩

private lemma exists_cubicLocus_of_geometricallyAmple [IsLocallyNoetherian S]
    (division : AlgebraicallyClosedFieldPolarizationDivisionStatement.{u})
    (L : LineBundle A.X.left)
    (hL : GeometricallyAmpleBundle A L) (d : ℕ) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ S), IsImmersion j ∧
      ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (t : T ⟶ S),
        (∃ t' : T ⟶ Z, t' ≫ j = t) ↔ ExistsCubicPolarization P d ((baseChange t).obj A)
          ((LineBundle.pullback (pullback.fst A.X.hom t)).obj L) := by
  let W := DualWitness.ofQuasiSeparated A
  let f := lineBundleMumford P A W L
  obtain ⟨Y, j, hj, hY⟩ := exists_homMultiple_locus f 6 (by decide)
  let := hj
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian j
  obtain ⟨lam₀, hlam₀⟩ := (hY Y j).mp ⟨𝟙 _, Category.id_comp _⟩
  let A₁ := (baseChange j).obj A
  let W₁ := W.pullback P j
  let L₁ := (LineBundle.pullback (pullback.fst A.X.hom j)).obj L
  let lam := lam₀ ≫ (W.baseChangeIso P j W₁).hom
  have hlam : 6 • lam = lineBundleMumford P A₁ W₁ L₁ := by
    change 6 • (lam₀ ≫ (W.baseChangeIso P j W₁).hom) = _
    rw [← Preadditive.nsmul_comp, hlam₀]
    exact lineBundleMumford_pullback P A W L j W₁
  have hpol : W₁.IsPolarization P lam := isPolarization_of_nsmul_mumford P A₁ division W₁ lam
    6 (by decide) L₁ (geometricallyAmpleBundle_pullback A L hL j) hlam
  obtain ⟨Z, k, hk, hZ⟩ := exists_cubicLocus_over_polarization P A₁ W₁ L₁ lam hpol hlam.symm d
  let := hk
  refine ⟨Z, k ≫ j, inferInstance, fun T _ t ↦ ?_⟩
  constructor
  · rintro ⟨a, rfl⟩
    rw [← Category.assoc, existsCubicPolarization_comp_iff P A j (a ≫ k) L d]
    exact (hZ T (a ≫ k)).mp ⟨a, rfl⟩
  · intro ht
    let W' := W.pullback P t
    let L' := (LineBundle.pullback (pullback.fst A.X.hom t)).obj L
    obtain ⟨f', hpol', _, hC⟩ := existsCubicPolarization_atWitness P W' d L' ht
    let e := W.baseChangeIso P t W'
    have hf' : 6 • f' = (baseChange t).map f ≫ e.hom := by
      exact (lineBundleMumford_eq_of_cubic P _ W' L' f' hpol' hC).symm.trans
        (lineBundleMumford_pullback P A W L t W').symm
    have hdivide : 6 • (f' ≫ e.inv) = (baseChange t).map f := by
      rw [← Preadditive.nsmul_comp, hf', Category.assoc, Iso.hom_inv_id, Category.comp_id]
    obtain ⟨b, hb⟩ := (hY T t).mpr ⟨f' ≫ e.inv, hdivide⟩
    have h := (existsCubicPolarization_comp_iff P A j b L d).mp (hb.symm ▸ ht)
    obtain ⟨a, ha⟩ := (hZ T b).mpr h
    exact ⟨a, by rw [← Category.assoc, ha, hb]⟩

/-- The closed divisibility and normalized bundle equations, followed by the open
    degree condition, give the cubic polarization locus. -/
theorem cubicPolarizationLocus_of_fieldDivision
    (division : AlgebraicallyClosedFieldPolarizationDivisionStatement.{u}) :
    CubicPolarizationLocusStatement.{u} := by
  intro P S _ A m d _ i hi hiS
  let := hi
  let L := (LineBundle.pullback i).obj (RelativeProjectiveSpace.twistOne S m)
  have hL : GeometricallyAmpleBundle A L := by
    intro K _ _ t
    have h := RelativeProjectiveSpace.isAmple_pullback_embedding A.X.hom m i hiS t
    exact h.of_iso ((LineBundle.forget _).mapIso
      ((LineBundle.pullbackComp (pullback.fst A.X.hom t) i).app
        (RelativeProjectiveSpace.twistOne S m)).symm)
  obtain ⟨Z, j, hj, hZ⟩ := exists_cubicLocus_of_geometricallyAmple P A division L hL d
  refine ⟨Z, j, hj, fun T _ t ↦ (hZ T t).trans ?_⟩
  let e := (LineBundle.pullbackComp (pullback.fst A.X.hom t) i).app
    (RelativeProjectiveSpace.twistOne S m)
  constructor
  · rintro ⟨W, lam, hpol, hd, N, ⟨hN⟩⟩
    exact ⟨W, lam, hpol, hd, N, ⟨e.symm ≪≫ hN⟩⟩
  · rintro ⟨W, lam, hpol, hd, N, ⟨hN⟩⟩
    exact ⟨W, lam, hpol, hd, N, ⟨e ≪≫ hN⟩⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel

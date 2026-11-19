import Langlands.AlgebraicGeometry.EtaleLocalSystemIsotrivialSpreadingStatement
import Langlands.AlgebraicGeometry.EtaleLocalSystemAffineLimit
import Langlands.AlgebraicGeometry.LocalEtaleLimit
import Langlands.AlgebraicGeometry.SchemeFilteredModelExistenceProof
import Langlands.AlgebraicGeometry.SchemeLimitRelativeFiniteProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationLimitModelLevels
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedSurjectivityLimitDescent

/-! # Spreading isotriviality from the spectrum of a stalk -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open EtaleLocalSystem AffineLimit EtaleEquivalenceRelation.LimitModel
open EtaleEquivalenceRelation.Action

set_option backward.isDefEq.respectTransparency false

private theorem property_baseChangeMap_id (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S X T : Scheme.{u}} (a : X ⟶ S) (q : T ⟶ S) :
    P (baseChangeMap a (𝟙 S) a (Category.comp_id a) q) ↔ P (pullback.fst q a) := by
  rw [← baseChangeMap_fst a (𝟙 S) a (Category.comp_id a) q]
  exact (MorphismProperty.cancel_right_of_respectsIso P _ _).symm

private theorem exists_finite_etale_surjective_level
    {I : Type u} [SmallCategory I] [IsCofiltered I] {S X : Scheme.{u}} [IsAffine S]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (a : X ⟶ S) [LocallyOfFinitePresentation a] [QuasiCompact a] [QuasiSeparated a]
    (hfinite : IsFinite (pullback.fst p a)) (hetale : Etale (pullback.fst p a))
    (hsurj : Surjective (pullback.fst p a)) :
    ∃ i, IsFinite (pullback.fst (t.app i) a) ∧ Etale (pullback.fst (t.app i) a) ∧
      Surjective (pullback.fst (t.app i) a) := by
  let m {T : Scheme.{u}} (b : T ⟶ S) := baseChangeMap a (𝟙 S) a (Category.comp_id a) b
  have hF : ∃ i, IsFinite (m (t.app i)) :=
    (relativeFiniteDescent D t a (𝟙 S) a (Category.comp_id a) c hc p hp).mp
      ((property_baseChangeMap_id @IsFinite a p).mpr hfinite)
  have hE : ∃ i, Etale (m (t.app i)) :=
    etale_descend (𝟙 S) a a (Category.comp_id a) D t c hc p hp
      ((property_baseChangeMap_id @Etale a p).mpr hetale)
  have hS : ∃ i, Surjective (m (t.app i)) :=
    (AlgebraicSpace.surjective_schemeStructuralPropertyDescent D t a (𝟙 S) a
      (Category.comp_id a) c hc p hp).mp
        ((property_baseChangeMap_id @Surjective a p).mpr hsurj)
  have hlevel (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      {i j : I} (r : i ⟶ j) (h : P (m (t.app j))) : P (m (t.app i)) :=
    baseChangeMap_level D t a (𝟙 S) a (Category.comp_id a) r h
  obtain ⟨i, hiF, hiE, hiS⟩ := exists_and_of_mono
    (hlevel @IsFinite) (fun r h => ⟨hlevel @Etale r h.1, hlevel @Surjective r h.2⟩)
    hF (exists_and_of_mono (hlevel @Etale) (hlevel @Surjective) hE hS)
  exact ⟨i, (property_baseChangeMap_id @IsFinite a _).mp hiF,
    (property_baseChangeMap_id @Etale a _).mp hiE,
    (property_baseChangeMap_id @Surjective a _).mp hiS⟩

/-- Spread a cover and its trivialization over an affine limit of open subschemes,
given a finitely presented model of the cover over the affine base. -/
private theorem exists_open_trivializing_cover
    {I : Type u} [SmallCategory I] [IsCofiltered I] {S X Y : Scheme.{u}} [IsAffine S]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj S) [∀ i, IsOpenImmersion (t.app i)]
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (g : X ⟶ c.pt) [IsFinite g] [Etale g] [Surjective g]
    (a : Y ⟶ S) [LocallyOfFinitePresentation a] [QuasiCompact a] [QuasiSeparated a]
    (π : X ⟶ Y) (hpb : IsPullback π g a p)
    {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}} (hF : IsFinitelyGeneratedLocallyConstant F)
    {M : AddCommGrpCat.{u}} (e : restrict (g ≫ p) F ≅ constant X M) :
    ∃ (V : Scheme.{u}) (b : V ⟶ S) (l : c.pt ⟶ V), IsOpenImmersion b ∧ l ≫ b = p ∧
      ∃ (Z : Scheme.{u}) (f : Z ⟶ V), IsFinite f ∧ Etale f ∧ Surjective f ∧
        Nonempty (restrict (f ≫ b) F ≅ constant Z M) := by
  have hproperty (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (hg : P g) :
      P (pullback.fst p a) := by
    let k := hpb.flip.isoPullback.hom
    apply (MorphismProperty.cancel_left_of_respectsIso P k (pullback.fst p a)).mp
    exact hpb.flip.isoPullback_hom_fst.symm ▸ hg
  obtain ⟨i, hiF, hiE, hiS⟩ := exists_finite_etale_surjective_level D t c hc p hp a
    (hproperty @IsFinite inferInstance) (hproperty @Etale inferInstance)
    (hproperty @Surjective inferInstance)
  let fᵢ := pullback.fst (t.app i) a
  let aᵢ := fᵢ ≫ t.app i
  have : IsAffine (pullback (t.app i) a) := isAffine_of_isAffineHom fᵢ
  have houter : IsPullback π g a (c.π.app i ≫ t.app i) := (hp i).symm ▸ hpb
  have hleft := houter.of_right' (IsPullback.of_hasPullback (t.app i) a).flip
  have hbase : IsPullback (c.π.app i) (𝟙 _) (t.app i) p :=
    IsPullback.of_vert_isIso_mono ⟨(hp i).trans (Category.id_comp _).symm⟩
  have hmodel := (Category.comp_id g ▸ hleft.paste_vert hbase).flip
  let D' := TargetLimit.diagram D t aᵢ
  let t' : D' ⟶ (Functor.const I).obj S := TargetLimit.projection D t aᵢ ≫ t
  let c' := TargetLimit.coneOfPullback D t aᵢ c p hp hmodel
  have hc' : IsLimit c' := TargetLimit.isLimitConeOfPullback D t aᵢ c p hp hmodel hc
  have hp' (j : I) : c'.π.app j ≫ t'.app j = g ≫ p := by
    simp only [c', t', NatTrans.comp_app, TargetLimit.projection,
      TargetLimit.coneOfPullback_π_fst_assoc, hp]
  obtain ⟨j, ⟨ej⟩⟩ := exists_level_trivialization D' t' c' hc' (g ≫ p) hp' e hF
  let b := pullback.fst (t.app j) (t.app i) ≫ t.app j
  let l := pullback.lift (c.π.app j) (c.π.app i) ((hp j).trans (hp i).symm)
  have hl : l ≫ b = p := by simp only [l, b, pullback.lift_fst_assoc, hp]
  let f := baseChangeMap aᵢ (t.app i) fᵢ rfl (t.app j)
  have hf := (baseChangeMap_isPullback aᵢ (t.app i) fᵢ rfl (t.app j)).flip
  have hfbase : f ≫ b = t'.app j := by
    simp only [f, b, baseChangeMap_fst_assoc, t', NatTrans.comp_app, TargetLimit.projection]
  exact ⟨_, b, l, inferInstance, hl, _, f,
    MorphismProperty.of_isPullback hf hiF, MorphismProperty.of_isPullback hf hiE,
    MorphismProperty.of_isPullback hf hiS, ⟨restrictCongrIso hfbase F ≪≫ ej⟩⟩

section Localization

open UnramifiedFunctor.Charts

variable (R : Type u) [CommRing R] (x : PrimeSpectrum R)

private theorem localization_stage_isOpenImmersion
    (i : (LocalEtaleLimit.ofLocalization R x).index) :
    IsOpenImmersion ((LocalEtaleLimit.ofLocalization R x).structural.app i) := by
  change IsOpenImmersion (Spec.algebraMap R (Localization.Away i.unop.val))
  infer_instance

/-- A finitely presented scheme over the prime localization has a model over the fixed
affine base, obtained by composing its model over one basic open with the open immersion. -/
private theorem exists_localization_model {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of (Localization.AtPrime x.asIdeal)))
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g] :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ Spec (CommRingCat.of R)) (π : X ⟶ Y),
      LocallyOfFinitePresentation a ∧ QuasiCompact a ∧ QuasiSeparated a ∧
        IsPullback π g a (Spec.algebraMap R (Localization.AtPrime x.asIdeal)) := by
  let J := DivIndex x.asIdeal.primeCompl
  let G : J ⥤ CommRingCat.{u} :=
    awayDiagram x.asIdeal.primeCompl ⋙ Under.forget (CommRingCat.of R)
  let c : Cocone G := (Under.forget (CommRingCat.of R)).mapCocone
    (awayCocone x.asIdeal.primeCompl (Localization.AtPrime x.asIdeal))
  let hc : IsColimit c := isColimitOfPreserves (Under.forget (CommRingCat.of R))
    (awayCoconeIsColimit x.asIdeal.primeCompl (Localization.AtPrime x.asIdeal))
  obtain ⟨j, Y, a, π, ha, hqc, hqs, hpb⟩ :=
    SchemeLimitModel.schemeFilteredModelExistence J G c hc X g
  let L := LocalEtaleLimit.ofLocalization R x
  let b : Spec (G.obj j) ⟶ Spec (CommRingCat.of R) := L.structural.app (op j)
  let : IsOpenImmersion b := localization_stage_isOpenImmersion R x (op j)
  let : QuasiCompact b := inferInstance
  let l : Spec (CommRingCat.of (Localization.AtPrime x.asIdeal)) ⟶ Spec (G.obj j) :=
    Spec.map (c.ι.app j)
  have hl : l ≫ b = Spec.algebraMap R (Localization.AtPrime x.asIdeal) :=
    L.compatible (op j)
  have hright : IsPullback l (𝟙 _) b (Spec.algebraMap R (Localization.AtPrime x.asIdeal)) :=
    IsPullback.of_vert_isIso_mono ⟨hl.trans (Category.id_comp _).symm⟩
  refine ⟨Y, a ≫ b, π, inferInstance, inferInstance, inferInstance, ?_⟩
  exact Category.comp_id g ▸ hpb.paste_vert hright

end Localization

/-- A finite étale trivialization at the spectrum of a stalk spreads to an open
neighbourhood of the point. -/
theorem etaleLocalSystemIsotrivialSpreading :
    EtaleLocalSystemIsotrivialSpreadingStatement.{u} := by
  intro S F hF s hs
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, _⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ s) isOpen_univ
  let R := Γ(S, U)
  let z : Spec R ⟶ S := hU.fromSpec
  have hs' : s ∈ Set.range z := by
    change s ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]
    exact hsU
  obtain ⟨x, rfl⟩ := hs'
  obtain ⟨X, q, hqF, hqE, hqS, M, hM, ⟨e⟩⟩ := hs
  let L := LocalEtaleLimit.ofLocalization R x
  let k : Spec (CommRingCat.of L.ring) ⟶ Spec (S.presheaf.stalk (z x)) :=
    Spec.map (z.stalkMap x ≫ (Spec.stalkIso R x).hom)
  have : IsIso k := by
    dsimp only [k]
    infer_instance
  have hk : k ≫ S.fromSpecStalk (z x) = L.baseMap ≫ z := by
    change _ = Spec.algebraMap R (Localization.AtPrime x.asIdeal) ≫ z
    dsimp only [k]
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Spec.fromSpecStalk_eq, ← Spec.map_comp_assoc, ← Spec.algebraMap_stalkIso_inv (R := R) x,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let g := q ≫ inv k
  have : IsFinite g := inferInstance
  have : Etale g := inferInstance
  have : Surjective g := inferInstance
  have hg : (g ≫ L.baseMap) ≫ z = q ≫ S.fromSpecStalk (z x) := by
    dsimp only [g]
    rw [Category.assoc, ← hk, Category.assoc, IsIso.inv_hom_id_assoc]
  have hF₀ := isFinitelyGeneratedLocallyConstant_restrict z hF
  have e₀ : restrict (g ≫ L.baseMap) (restrict z F) ≅ constant X M :=
    (restrictCompIso z (g ≫ L.baseMap) F).symm ≪≫ restrictCongrIso hg F ≪≫ e
  obtain ⟨Y, a, π, ha, hqc, hqs, hpb⟩ := exists_localization_model R x g
  have : ∀ i, IsOpenImmersion (L.structural.app i) := localization_stage_isOpenImmersion R x
  obtain ⟨V, b, l, hb, hl, Z, f, hfF, hfE, hfS, ⟨ef⟩⟩ :=
    exists_open_trivializing_cover L.diagram L.structural _ L.isLimit L.baseMap L.compatible
      g a π hpb hF₀ e₀
  let w := b ≫ z
  have : IsOpenImmersion w := inferInstance
  have hx : z x ∈ w.opensRange := by
    refine ⟨l (IsLocalRing.closedPoint L.ring), ?_⟩
    change z ((l ≫ b) (IsLocalRing.closedPoint L.ring)) = z x
    rw [hl, L.closedPoint_image]
  let f' := f ≫ w.isoOpensRange.hom
  have hf' : f' ≫ w.opensRange.ι = (f ≫ b) ≫ z := by
    simp only [f', Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, w]
  exact ⟨w.opensRange, hx, Z, f', inferInstance, inferInstance, inferInstance,
    M, hM, ⟨restrictCongrIso hf' F ≪≫ restrictCompIso z (f ≫ b) F ≪≫ ef⟩⟩

end Langlands.AlgebraicGeometry

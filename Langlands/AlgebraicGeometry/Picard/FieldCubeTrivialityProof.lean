import Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialitySmoothThirdStatement
import Langlands.AlgebraicGeometry.Picard.LocalTwoAxisTrivialityProof
import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof
import Langlands.AlgebraicGeometry.Picard.RelativeCubeAssembly
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianOfSeesawProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedGeneral
import Langlands.AlgebraicGeometry.Picard.RigidifiedRelativeIsoUniqueness
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof

/-! # The geometric theorem of the cube with a smooth third factor over arbitrary fields -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace FieldCubeTrivialityProof

open RelativeCubeAssembly

set_option backward.isDefEq.respectTransparency false

private theorem factor_residue {D T : Scheme.{u}} (ι : D ⟶ T)
    [IsClosedImmersion ι] (t : T) (ht : t ∈ Set.range ι) :
    ∃ g : Spec (T.residueField t) ⟶ D, g ≫ ι = T.fromSpecResidueField t := by
  have : Surjective (pullback.snd ι (T.fromSpecResidueField t)) := by
    constructor
    intro s
    obtain ⟨d, hd⟩ := ht
    obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback ι (T.fromSpecResidueField t)) d s (by
        rw [hd, Scheme.fromSpecResidueField_apply])
    exact ⟨w, hw⟩
  have : IsIso (pullback.snd ι (T.fromSpecResidueField t)) :=
    isIso_of_isClosedImmersion_of_surjective _
  refine ⟨inv (pullback.snd ι (T.fromSpecResidueField t)) ≫
    pullback.fst ι (T.fromSpecResidueField t), ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

private theorem iso_of_locallyIsoOver_field
    {k : Type u} [Field k] {P : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) {M N : P.Modules}
    (h : LocallyIsoOver p M N) : Nonempty (M ≅ N) := by
  obtain ⟨U, ht, ⟨e⟩⟩ := h default
  exact nonempty_pullback_iso_of_restrict_iso (p ⁻¹ᵁ U) e
    (𝟙 P) (fun x => by
      change p x ∈ U
      rwa [Subsingleton.elim (p x) default])
    |>.map (fun e =>
      ((Scheme.Modules.pullbackId P).app M).symm ≪≫ e ≪≫
        (Scheme.Modules.pullbackId P).app N)

private theorem relative_trivial_of_locallyIsoOver
    {S A : Scheme.{u}} (c : A ⟶ S) (ε : S ⟶ A)
    (hε : ε ≫ c = 𝟙 S)
    (hO : ∀ (T : Over S) (V : T.left.Opens),
      IsIso (((relativeProjection c).app T).app V))
    (T : Over S) (L : RigidifiedLineBundle.relative c ε hε T)
    (h : LocallyIsoOver ((relativeProjection c).app T) L.obj.carrier
      (Langlands.Scheme.Modules.structureSheaf ((relativeSpace c).obj T))) :
    Nonempty (L ≅ RigidifiedLineBundle.trivial ((relativeSection c ε hε).app T)) := by
  choose V hV e using h
  have hcover : TopologicalSpace.IsOpenCover V := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun t _ => ?_)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, hV t⟩
  let 𝒰 := T.left.openCoverOfIsOpenCover V hcover
  apply @Quotient.exact _ (isIsomorphicSetoid _) L
    (RigidifiedLineBundle.trivial ((relativeSection c ε hε).app T))
  apply RigidifiedLineBundle.classes_zariskiSeparated_of_unique c ε hε
    (RigidifiedLineBundle.relative_iso_subsingleton c ε hε hO) T 𝒰
    (⟦L⟧ : RigidifiedLineBundle.Classes c ε hε T)
    ⟦RigidifiedLineBundle.trivial ((relativeSection c ε hε).app T)⟧
  intro t
  let a : Over.mk ((V t).ι ≫ T.hom) ⟶ T := Over.homMk (V t).ι
  have ha : ∀ x, (relativeSpace c).map a x ∈
      (relativeProjection c).app T ⁻¹ᵁ V t := by
    intro x
    show ((relativeSpace c).map a ≫ (relativeProjection c).app T) x ∈ V t
    rw [(relativeProjection c).naturality a]
    exact ((relativeProjection c).app _ x).2
  obtain ⟨E⟩ := nonempty_pullback_iso_of_restrict_iso _ (e t).some
    ((relativeSpace c).map a) ha
  exact Quotient.sound (RigidifiedLineBundle.nonempty_iso_of_forget_iso
    Langlands.Scheme.Modules.pullbackTensorComparisonIsIso
    ((relativeProjection c).app _) (relativeSection_projection c ε hε _)
    (ObjectProperty.isoMk _ E))

private theorem relative_trivial_along_of_fac
    {S A W : Scheme.{u}} (c : A ⟶ S) {T T' : Over S} (h : T' ⟶ T)
    (M : ((relativeSpace c).obj T).Modules)
    (j : W ⟶ (relativeSpace c).obj T) (k : W ⟶ T'.left)
    (hj : j ≫ (relativeProjection c).app T = k ≫ h.left)
    (ht : TrivialAlong ((relativeSpace c).map h) M) :
    TrivialAlong j M := by
  let l : W ⟶ (relativeSpace c).obj T' :=
    pullback.lift k (j ≫ pullback.snd T.hom c) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      change k ≫ T'.hom = (j ≫ (relativeProjection c).app T) ≫ T.hom
      rw [hj, Category.assoc, Over.w])
  apply ht.of_fac l
  apply pullback.hom_ext
  · simpa [l, relativeSpace, relativeProjection, Over.pullback] using hj.symm
  · simp [l, relativeSpace, Over.pullback]

section Cube

variable {S : Scheme.{u}} (X Y Z : Over S)

private def cubeIso :
    (relativeSpace (X ⨯ Y).hom).obj Z ≅ (X ⨯ (Y ⨯ Z)).left :=
  relativeSpaceProdIso (X ⨯ Y) Z ≪≫
    (Over.forget S).mapIso (CategoryTheory.Limits.prod.associator X Y Z)

@[reassoc (attr := simp)]
private lemma cubeIso_fst :
    (cubeIso X Y Z).hom ≫ (prod.fst : X ⨯ (Y ⨯ Z) ⟶ X).left =
      pullback.snd Z.hom (X ⨯ Y).hom ≫ (prod.fst : X ⨯ Y ⟶ X).left := by
  simp [cubeIso, CategoryTheory.Limits.prod.associator, Over.comp_left, Category.assoc]

@[reassoc (attr := simp)]
private lemma cubeIso_snd_fst :
    (cubeIso X Y Z).hom ≫ (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z).left ≫
        (prod.fst : Y ⨯ Z ⟶ Y).left =
      pullback.snd Z.hom (X ⨯ Y).hom ≫ (prod.snd : X ⨯ Y ⟶ Y).left := by
  simp [cubeIso, CategoryTheory.Limits.prod.associator, Over.comp_left, Category.assoc]

@[reassoc (attr := simp)]
private lemma cubeIso_thirdProjection :
    (cubeIso X Y Z).hom ≫ thirdProjection X Y Z =
      (relativeProjection (X ⨯ Y).hom).app Z := by
  simp [cubeIso, thirdProjection, CategoryTheory.Limits.prod.associator, Category.assoc]

private lemma cubeIso_inv_projection :
    (cubeIso X Y Z).inv ≫ (relativeProjection (X ⨯ Y).hom).app Z =
      thirdProjection X Y Z := by
  rw [← cubeIso_thirdProjection, Iso.inv_hom_id_assoc]

private lemma section_cubeIso
    (x₀ : Over.mk (𝟙 S) ⟶ X) (y₀ : Over.mk (𝟙 S) ⟶ Y) :
    (relativeSection (X ⨯ Y).hom (prod.lift x₀ y₀).left
      (overSection_comp (X ⨯ Y) (prod.lift x₀ y₀))).app Z ≫
        (cubeIso X Y Z).hom =
      (prod.lift (Over.mkIdTerminal.from Z ≫ y₀) (𝟙 Z)).left ≫
        (CubeFace.first X Y Z x₀).left := by
  apply triple_hom_ext <;>
    simp [CubeFace.first, relativeSection, relativeProjection, Over.comp_left, Category.assoc]

private lemma third_face_cubeIso (z₀ : Over.mk (𝟙 S) ⟶ Z) :
    (relativeSpace (X ⨯ Y).hom).map z₀ ≫ (cubeIso X Y Z).hom =
      pullback.snd (𝟙 S) (X ⨯ Y).hom ≫ (CubeFace.third X Y Z z₀).left := by
  apply triple_hom_ext <;>
    simp [CubeFace.third, relativeSpace, relativeProjection, Over.pullback,
      Over.comp_left, Category.assoc]
  rw [← pullback.condition_assoc, Category.id_comp]

private lemma local_triviality_of_fibre
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
    (x₀ : Over.mk (𝟙 S) ⟶ X) (y₀ : Over.mk (𝟙 S) ⟶ Y)
    (L : LineBundle (X ⨯ (Y ⨯ Z)).left)
    (h₁ : TrivialAlong (CubeFace.first X Y Z x₀).left L.obj)
    (h₂ : TrivialAlong (CubeFace.second X Y Z y₀).left L.obj)
    (z : Z.left)
    (hf : TrivialAlong ((bc Z.hom X ⨯ bc Z.hom Y).hom.fiberι z ≫
      (productComparison X Y Z).left) L.obj) :
    ∃ U : Z.left.Opens, z ∈ U ∧
      ∀ {W : Scheme.{u}} (j : W ⟶ (X ⨯ (Y ⨯ Z)).left) (k : W ⟶ U),
        j ≫ thirdProjection X Y Z = k ≫ U.ι → TrivialAlong j L.obj := by
  have hXs : Smooth (bc Z.hom X).hom :=
    show Smooth (pullback.snd X.hom Z.hom) from inferInstance
  have hXp : IsProper (bc Z.hom X).hom :=
    show IsProper (pullback.snd X.hom Z.hom) from inferInstance
  have hXc : GeometricallyConnected (bc Z.hom X).hom :=
    show GeometricallyConnected (pullback.snd X.hom Z.hom) from inferInstance
  have hYs : Smooth (bc Z.hom Y).hom :=
    show Smooth (pullback.snd Y.hom Z.hom) from inferInstance
  have hYp : IsProper (bc Z.hom Y).hom :=
    show IsProper (pullback.snd Y.hom Z.hom) from inferInstance
  have hYc : GeometricallyConnected (bc Z.hom Y).hom :=
    show GeometricallyConnected (pullback.snd Y.hom Z.hom) from inferInstance
  obtain ⟨U, hzU, ⟨τ⟩⟩ := localTwoAxisTriviality Z.left
    (bc Z.hom X) (bc Z.hom Y) hXs hXp hXc hYs hYp hYc
    (baseChangeSection Z.hom x₀) (baseChangeSection Z.hom y₀)
    ((LineBundle.pullback (productComparison X Y Z).left).obj L) z
    ((TrivialAlong.pullback_iff _ _ _).2
      (h₂.of_fac _ (axisX_productComparison X Y Z y₀).symm))
    ((TrivialAlong.pullback_iff _ _ _).2
      (h₁.of_fac _ (axisY_productComparison X Y Z x₀).symm))
    ((TrivialAlong.pullback_iff _ _ _).2 hf)
  refine ⟨U, hzU, fun j k hjk => ?_⟩
  have hU : TrivialAlong (pullback.fst (bc Z.hom X ⨯ bc Z.hom Y).hom U.ι ≫
      (productComparison X Y Z).left) L.obj :=
    (TrivialAlong.pullback_iff _ _ _).1 ⟨τ⟩
  refine hU.of_fac (pullback.lift (j ≫ (productSection X Y Z).left) k ?_) ?_
  · rw [Category.assoc, productSection_hom, hjk]
  · rw [pullback.lift_fst_assoc, Category.assoc, productSection_comparison]
    exact Category.comp_id j

end Cube

private theorem cube : FieldCubeTrivialitySmoothThirdStatement.{u} := by
  intro K _ X Y Z hXs hXp hXc hYs hYp hYc hZs hZc x₀ y₀ z₀ L h₁ h₂ h₃
  let := hXs
  let := hXp
  let := hXc
  let := hYs
  let := hYp
  let := hYc
  let := hZs
  let := hZc
  let A := X ⨯ Y
  obtain ⟨hAs, hAp, hAc⟩ := product_geometry X Y
  let : Smooth A.hom := hAs
  let : IsProper A.hom := hAp
  let : GeometricallyConnected A.hom := hAc
  let : GeometricallyIntegral A.hom :=
    Langlands.AbelianScheme.smoothGeometricIntegrality K A.left A.hom hAs hAc
  let : GeometricallyIntegral Z.hom :=
    Langlands.AbelianScheme.smoothGeometricIntegrality K Z.left Z.hom hZs hZc
  let : IsIntegral Z.left := GeometricallyIntegral.isIntegral_of_subsingleton Z.hom
  let : ConnectedSpace Z.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton Z.hom
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let E := cubeIso X Y Z
  let M : ((relativeSpace A.hom).obj Z).Modules := (Scheme.Modules.pullback E.hom).obj L.obj
  let N := Langlands.Scheme.Modules.structureSheaf ((relativeSpace A.hom).obj Z)
  have hM : IsLocallyFreeRankOne M := L.property.pullback E.hom
  have hN : IsLocallyFreeRankOne N := (LineBundle.trivial _).property
  have hH0 : ∀ (B : Type u) [CommRing B] [Algebra K B],
      Function.Bijective
        (pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap K B)))).appTop := by
    intro B _ _
    have := Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions _ _
      (pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap K B))))
      inferInstance inferInstance inferInstance ⊤
    exact ConcreteCategory.bijective_of_isIso
      ((pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap K B)))).app ⊤)
  -- Seesaw represents local triviality by a closed subscheme of the third factor.
  obtain ⟨D, ι, hι, hD⟩ := noetherianLineBundleSeesaw A.hom hH0 Z.hom
    ((Scheme.Modules.pullback (pullbackSymmetry A.hom Z.hom).hom).obj M)
    ((Scheme.Modules.pullback (pullbackSymmetry A.hom Z.hom).hom).obj N)
    (hM.pullback _) (hN.pullback _)
  let := hι
  have locus {T : Over (Spec (CommRingCat.of K))} (h : T ⟶ Z) :
      (∃ g : T.left ⟶ D, g ≫ ι = h.left) ↔
        LocallyIsoOver ((relativeProjection A.hom).app T)
          ((Scheme.Modules.pullback ((relativeSpace A.hom).map h)).obj M)
          ((Scheme.Modules.pullback ((relativeSpace A.hom).map h)).obj N) :=
    (hD h.left).trans (locallyIsoOver_seesaw_iff A.hom h M N)
  have zero : TrivialAlong ((relativeSpace A.hom).map z₀) M :=
    (TrivialAlong.pullback_iff _ _ _).2
      (TrivialAlong.of_fac h₃ _ (third_face_cubeIso X Y Z z₀).symm)
  obtain ⟨g₀, hg₀⟩ := (locus z₀).2 (LocallyIsoOver.of_iso _
    (zero.some ≪≫ (Langlands.Scheme.Modules.pullbackUnitIso _).symm))
  have hnonempty : (Set.range ι).Nonempty := by
    refine ⟨z₀.left (IsLocalRing.closedPoint K), g₀ (IsLocalRing.closedPoint K), ?_⟩
    change (g₀ ≫ ι) (IsLocalRing.closedPoint K) = z₀.left (IsLocalRing.closedPoint K)
    rw [hg₀]
  -- At each point of the locus, two-axis detection spreads fibre triviality.
  have hopen : IsOpen (Set.range ι) := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨g, hg⟩ := factor_residue ι z hz
    let T : Over (Spec (CommRingCat.of K)) := Over.mk (residueBase Z z)
    let r : T ⟶ Z := Over.homMk (Z.left.fromSpecResidueField z) rfl
    obtain ⟨er⟩ := iso_of_locallyIsoOver_field
      ((relativeProjection A.hom).app T) ((locus r).1 ⟨g, hg⟩)
    have hr : TrivialAlong ((relativeSpace A.hom).map r) M :=
      ⟨er ≪≫ Langlands.Scheme.Modules.pullbackUnitIso _⟩
    let F := (bc Z.hom X ⨯ bc Z.hom Y).hom
    let j := F.fiberι z ≫ (productComparison X Y Z).left
    have hf : TrivialAlong j L.obj := by
      have hm : TrivialAlong (j ≫ E.inv) M :=
        relative_trivial_along_of_fac A.hom r M (j ≫ E.inv)
          (F.fiberToSpecResidueField z) (by
            rw [Category.assoc, cubeIso_inv_projection]
            dsimp only [j, thirdProjection]
            rw [Category.assoc, productComparison_snd_snd]
            exact F.fiber_fac z) hr
      have hc := (TrivialAlong.pullback_iff _ _ _).1 hm
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hc
    obtain ⟨U, hzU, hU⟩ :=
      local_triviality_of_fibre X Y Z x₀ y₀ L h₁ h₂ z hf
    let V : Over (Spec (CommRingCat.of K)) := Over.mk (U.ι ≫ Z.hom)
    let u : V ⟶ Z := Over.homMk U.ι rfl
    have hu : TrivialAlong ((relativeSpace A.hom).map u) M :=
      (TrivialAlong.pullback_iff _ _ _).2
        (hU (((relativeSpace A.hom).map u) ≫ E.hom)
          ((relativeProjection A.hom).app V) (by
            rw [Category.assoc, cubeIso_thirdProjection]
            exact (relativeProjection A.hom).naturality u))
    obtain ⟨gu, hgu⟩ := (locus u).2 (LocallyIsoOver.of_iso _
      (hu.some ≪≫ (Langlands.Scheme.Modules.pullbackUnitIso _).symm))
    refine ⟨U, ?_, U.isOpen, hzU⟩
    intro t ht
    refine ⟨gu ⟨t, ht⟩, ?_⟩
    change (gu ≫ ι) ⟨t, ht⟩ = t
    rw [hgu]
    rfl
  have hfull : Set.range ι = Set.univ :=
    IsClopen.eq_univ ⟨ι.isClosedEmbedding.isClosed_range, hopen⟩ hnonempty
  let : Surjective ι := ⟨fun z => by
    have hz : z ∈ Set.range ι := by rw [hfull]; trivial
    exact hz⟩
  let : IsIso ι := isIso_of_isClosedImmersion_of_surjective ι
  have hloc : LocallyIsoOver ((relativeProjection A.hom).app Z) M N := by
    have h := (locus (𝟙 Z)).1 ⟨inv ι, IsIso.inv_hom_id ι⟩
    let eM : (Scheme.Modules.pullback ((relativeSpace A.hom).map (𝟙 Z))).obj M ≅ M :=
      (Scheme.Modules.pullbackCongr ((relativeSpace A.hom).map_id Z)).app M ≪≫
        (Scheme.Modules.pullbackId _).app M
    let eN : (Scheme.Modules.pullback ((relativeSpace A.hom).map (𝟙 Z))).obj N ≅ N :=
      (Scheme.Modules.pullbackCongr ((relativeSpace A.hom).map_id Z)).app N ≪≫
        (Scheme.Modules.pullbackId _).app N
    intro z
    obtain ⟨U, hzU, ⟨e⟩⟩ := h z
    exact ⟨U, hzU, ⟨(Scheme.Modules.restrictFunctor _).mapIso eM.symm ≪≫ e ≪≫
      (Scheme.Modules.restrictFunctor _).mapIso eN⟩⟩
  -- The first face rigidifies the bundle, so normalized local isomorphisms glue.
  let ε := (prod.lift x₀ y₀).left
  have hε : ε ≫ A.hom = 𝟙 _ := overSection_comp A (prod.lift x₀ y₀)
  have hs : TrivialAlong ((relativeSection A.hom ε hε).app Z) M :=
    (TrivialAlong.pullback_iff _ _ _).2
      (TrivialAlong.of_fac h₁ _ (section_cubeIso X Y Z x₀ y₀).symm)
  let R : RigidifiedLineBundle.relative A.hom ε hε Z :=
    RigidifiedLineBundle.ofLineBundle ⟨M, hM⟩ hs.some.symm
  have hO (T : Over (Spec (CommRingCat.of K))) (V : T.left.Opens) :
      IsIso (((relativeProjection A.hom).app T).app V) := by
    change IsIso ((pullback.fst T.hom A.hom).app V)
    exact Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions _ _
      (pullback.fst T.hom A.hom) inferInstance inferInstance inferInstance V
  obtain ⟨eR⟩ := relative_trivial_of_locallyIsoOver A.hom ε hε hO Z R hloc
  exact ⟨CubeRelativeTransport.recoverTrivialization E L.obj
    ((RigidifiedLineBundle.forget _ ⋙ LineBundle.forget _).mapIso eR)⟩

end FieldCubeTrivialityProof

/-- The geometric theorem of the cube over every field, with smooth proper
geometrically connected first two factors and a smooth geometrically connected third factor. -/
theorem fieldCubeTrivialitySmoothThird : FieldCubeTrivialitySmoothThirdStatement.{u} :=
  FieldCubeTrivialityProof.cube

/-- The geometric theorem of the cube for smooth proper geometrically connected
pointed schemes over every field. -/
theorem fieldCubeTriviality : FieldCubeTrivialityStatement.{u} := by
  intro K _ X Y Z hXs hXp hXc hYs hYp hYc hZs _hZp hZc
  exact fieldCubeTrivialitySmoothThird K X Y Z hXs hXp hXc hYs hYp hYc hZs hZc

end Langlands.AlgebraicGeometry.Picard

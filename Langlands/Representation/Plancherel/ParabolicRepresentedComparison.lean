import Langlands.Representation.Plancherel.ParabolicJacquetUnitaryRestriction
import Langlands.Representation.Plancherel.ParabolicRadicalUnimodularity
import Langlands.Representation.Exponents.LeviSelectedWeights
import Langlands.Representation.Filtration.SelectedGluing

/-! # The literal parabolic model and the represented Levi model -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uK uL uA uV uW

open Aubert.General

section Transport

variable {H : Type u} [Group H] [TopologicalSpace H]
  {K : Type uK} [Group K] [TopologicalSpace K]
  {L : Type uL} [Group L] [TopologicalSpace L]

/-- Two successive pullbacks are the pullback along any pointwise equal
composite, by the identity on vectors. -/
def pullbackPullbackIso (e : H ≃ₜ* K) (f : K ≃ₜ* L) (g : H ≃ₜ* L)
    (hg : ∀ x, f (e x) = g x) (X : SmoothRep.{0, uL, uV} ℂ L) :
    SmoothRep.pullback e (SmoothRep.pullback f X) ≅ SmoothRep.pullback g X :=
  SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ X) fun x => by
    change (LinearEquiv.refl ℂ X).toLinearMap ∘ₗ X.representation (f (e x)) =
      X.representation (g x) ∘ₗ (LinearEquiv.refl ℂ X).toLinearMap
    rw [hg x]
    rfl)

/-- Pulling back along the identification of a subgroup with itself changes
no vector and no action. -/
def pullbackSubgroupCongrReflIso {M : Subgroup H} (X : SmoothRep.{0, u, uV} ℂ M) :
    SmoothRep.pullback (RepresentedParabolic.subgroupCongrContinuous (rfl : M = M)).symm X ≅
      X :=
  SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ X) fun _ => rfl)

section Selected

variable [NonarchimedeanGroup H] [WeaklyLocallyCompactSpace H]
  [NonarchimedeanGroup K] [WeaklyLocallyCompactSpace K]
  {T : Type uA} [Group T] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- For a smooth action, selecting generalized weights commutes with changing
the acting group along an isomorphism carrying the central torus maps. -/
theorem selectedWeightPart_comp_toSubmodule (e : H ≃ₜ* K) {ρ : Representation ℂ K V}
    (hρ : IsSmooth ρ) (j : T →* H) (hj : ∀ t, j t ∈ Subgroup.center H)
    (hj' : ∀ t, e.toMonoidHom.comp j t ∈ Subgroup.center K) (P : (T →* ℂˣ) → Prop) :
    (selectedWeightPart (ρ.comp e.toMonoidHom) j hj P).toSubmodule =
      (selectedWeightPart ρ (e.toMonoidHom.comp j) hj' P).toSubmodule := by
  rw [selectedWeightPart_toSubmodule, selectedWeightPart_toSubmodule]
  refine iSup_congr fun χ => iSup_congr fun _ => ?_
  ext v
  change v ∈ generalizedWeightSpace (ρ.comp e.toMonoidHom) j χ hj ↔
    v ∈ generalizedWeightSpace ρ (e.toMonoidHom.comp j) χ hj'
  rw [mem_generalizedWeightSpace_of_isSmooth j χ hj
      (isSmooth_comp e.toMonoidHom e.continuous hρ),
    mem_generalizedWeightSpace_of_isSmooth (e.toMonoidHom.comp j) χ hj' hρ]
  rfl

/-- The identity on vectors identifies the pulled-back selected part with the
selected part of the pulled-back action. -/
def selectedWeightPartCompEquiv (e : H ≃ₜ* K) {ρ : Representation ℂ K V}
    (hρ : IsSmooth ρ) (j : T →* H) (hj : ∀ t, j t ∈ Subgroup.center H)
    (hj' : ∀ t, e.toMonoidHom.comp j t ∈ Subgroup.center K) (P : (T →* ℂˣ) → Prop) :
    Representation.Equiv
      ((selectedWeightPart ρ (e.toMonoidHom.comp j) hj' P).toRepresentation.comp e.toMonoidHom)
      (selectedWeightPart (ρ.comp e.toMonoidHom) j hj P).toRepresentation :=
  Representation.Equiv.mk
    (LinearEquiv.ofEq _ _ (selectedWeightPart_comp_toSubmodule e hρ j hj hj' P).symm)
    (fun _ => by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      rfl)

end Selected

variable [LocallyCompactSpace H] [NonarchimedeanGroup H]

/-- Equal parabolic, Levi and radical subgroups give the same normalized
Jacquet module of normalized induction, after the coefficient identification. -/
def jacquetInductionSubgroupCongrIso {P M U P' M' U' : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (h' : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set H))
    (hM' : M' ≤ Subgroup.normalizer (U' : Set H))
    (eP : P = P') (eM : M = M') (eU : U = U') (σ : SmoothRep.{0, u, uV} ℂ M) :
    (normalizedJacquetFunctor U' M' hU' hM').obj
        ((normalizedInductionFunctor h' hU').obj
          (SmoothRep.pullback (RepresentedParabolic.subgroupCongrContinuous eM).symm σ)) ≅
      SmoothRep.pullback (RepresentedParabolic.subgroupCongrContinuous eM).symm
        ((jacquetFunctor h hU).obj ((normalizedInductionFunctor h hU).obj σ)) := by
  subst eP eM eU
  exact (normalizedJacquetFunctor U M hU' hM').mapIso
      ((normalizedInductionFunctor h' hU').mapIso (pullbackSubgroupCongrReflIso σ)) ≪≫
    (pullbackSubgroupCongrReflIso _).symm

/-- Changing the acting group along a topological group isomorphism identifies
the intertwiner spaces, with the same underlying linear maps. -/
def intertwiningCompLinearEquiv (e : H ≃ₜ* K) {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K V) (τ : Representation ℂ K W) :
    ρ.IntertwiningMap τ ≃ₗ[ℂ]
      Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (τ.comp e.toMonoidHom) where
  toFun := SmoothRep.pullbackMap e
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' k := by
        have hf := f.isIntertwining' (e.symm k)
        change f.toLinearMap ∘ₗ ρ (e (e.symm k)) = τ (e (e.symm k)) ∘ₗ f.toLinearMap at hf
        rwa [e.apply_symm_apply] at hf }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Precomposition with the inverse of a representation equivalence identifies
intertwiner spaces, across carrier universes. -/
def intertwiningPrecompLinearEquiv {V : Type uV} {V' : Type uA} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ K V} {ρ' : Representation ℂ K V'} (E : ρ.Equiv ρ')
    (τ : Representation ℂ K W) :
    ρ.IntertwiningMap τ ≃ₗ[ℂ] ρ'.IntertwiningMap τ where
  toFun f := f.comp E.symm.toIntertwiningMap
  invFun g := g.comp E.toIntertwiningMap
  left_inv f := Representation.IntertwiningMap.ext
    (LinearMap.ext fun v => congrArg f (E.symm_apply_apply v))
  right_inv g := Representation.IntertwiningMap.ext
    (LinearMap.ext fun v => congrArg g (E.apply_symm_apply v))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Transport

section Actual

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} {n : U ⟶ P}
  (pres : ParabolicRootPresentation p l a)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance parabolicRepresentedComparisonTopologicalSpace : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance parabolicRepresentedComparisonTopologicalSpace2 : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
local instance : T2Space F := BruhatTits.localField_t2Space F

include pres in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffine M.X.left] in
/-- A compatible root presentation makes Levi-first multiplication with any
supplied geometric radical an isomorphism. -/
theorem parabolicRadical_isIso_subgroupMultiplication (hG : IsConnectedReductive G)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n) :
    IsIso (subgroupMultiplication l n) := by
  have := hG.smooth
  have hpc := pres.isCompatible.parabolic.isClosedSubgroup
  have hlc := pres.isCompatible.levi.isClosedSubgroup.comp hpc
  have hnc := hn.1.isClosedSubgroup.comp hpc
  let := hpc.mono
  let := hlc.mono
  let := hnc.mono
  exact Dynamic.isIso_subgroupMultiplication
    ⟨Over.mono_of_mono_left _, pres.parabolic_eq_splitComponentCocharacter⟩
    ⟨Over.mono_of_mono_left _, pres.levi_eq_splitComponentCocharacter⟩
    ⟨Over.mono_of_mono_left _, pres.range_comp_radical_eq hn⟩ l n rfl rfl

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (hG : IsConnectedReductive G)
  (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (h : IsSemidirectDecomposition
    ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
    (parabolicLeviPointSubgroup p l)
    ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))))
  (hU : IsClosed (((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))) :
    Set (rationalPoints G)))

/-- The literal normalized Jacquet module of the literal Levi-twisted induction,
pulled back to the Levi's own points, is the represented Jacquet module of the
represented induction of the pulled-back inducing representation. -/
def parabolicRepresentedJacquetInductionIso
    (σ : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    SmoothRep.pullback (parabolicLeviPointHomeomorph pres)
        ((jacquetFunctor h hU).obj
          ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj σ)) ≅
      (RepresentedParabolic.leviJacquetFunctor p l n pres.isCompatible.parabolic hn
          pres.isCompatible.levi (parabolicRadical_isIso_subgroupMultiplication pres hG hn)).obj
        ((RepresentedParabolic.leviInductionFunctor p l n pres.isCompatible.parabolic hn
          pres.isCompatible.levi (parabolicRadical_isIso_subgroupMultiplication pres hG hn)).obj
            (SmoothRep.pullback (parabolicLeviPointHomeomorph pres) σ)) := by
  let hp := pres.isCompatible.parabolic
  let hl := pres.isCompatible.levi
  let hmul := parabolicRadical_isIso_subgroupMultiplication pres hG hn
  let e := parabolicLeviPointHomeomorph pres
  let e' := RepresentedParabolic.leviPointsEquiv p l hp hl
  have eP : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) =
      RepresentedParabolic.pointImage p :=
    (RepresentedParabolic.pointImage_eq_range_carrier p).symm
  have eM : parabolicLeviPointSubgroup p l = RepresentedParabolic.pointImage (l ≫ p) :=
    (RepresentedParabolic.pointImage_eq_range_carrier (l ≫ p)).symm
  have eU : (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)) =
      RepresentedParabolic.pointImage (n ≫ p) :=
    (RepresentedParabolic.pointImage_eq_range_carrier (n ≫ p)).symm
  let c := RepresentedParabolic.subgroupCongrContinuous eM
  let hrep := RepresentedParabolic.isSemidirectDecomposition_pointImage p l n
    hp.isClosedSubgroup hn hmul
  let hR := RepresentedParabolic.isClosed_pointImage_comp p n hp.isClosedSubgroup
    hn.1.isClosedSubgroup
  let J' := normalizedJacquetFunctor.{u, max u uV} (RepresentedParabolic.pointImage (n ≫ p))
    (RepresentedParabolic.pointImage (l ≫ p)) hR
    (RepresentedParabolic.pointImage_le_normalizer p l n hn)
  let I' := normalizedInductionFunctor.{u, uV} hrep hR
  have hδ := parabolicRadical_isUnimodular F G hG A M P U p l a n pres hn hU
  have hce (x : RepresentedParabolic.pointImage (l ≫ p)) : e (e'.symm x) = c.symm x := by
    apply Subtype.ext
    change (rationalPoints.map (l ≫ p) (e'.symm x)) = (x : rationalPoints G)
    exact congrArg Subtype.val (e'.apply_symm_apply x)
  have hec (m : rationalPoints M) : c.symm (e' m) = e m := Subtype.ext rfl
  have ha : SmoothRep.pullback e'.symm (SmoothRep.pullback e σ) ≅
      SmoothRep.pullback c.symm σ :=
    pullbackPullbackIso e'.symm e c.symm hce σ
  refine (pullbackPullbackIso e' c.symm e hec _).symm ≪≫ ?_
  refine (SmoothRep.pullbackFunctor e').mapIso ((SmoothRep.pullbackFunctor c.symm).mapIso
    ((jacquetFunctor h hU).mapIso
      ((DynamicNormalization.normalizedInductionLeviTwistIso h hU hδ).app σ).symm)) ≪≫ ?_
  refine (SmoothRep.pullbackFunctor e').mapIso
    (jacquetInductionSubgroupCongrIso h hU hrep hR
      (RepresentedParabolic.pointImage_le_normalizer p l n hn) eP eM eU σ).symm ≪≫ ?_
  exact (SmoothRep.pullbackFunctor e').mapIso (J'.mapIso (I'.mapIso ha.symm))

/-- The intertwiners from the unitary selected part of the literal Jacquet
module of the literal induction into `τ` correspond, with the same underlying
maps, to the intertwiners from the represented unitary Jacquet module of the
represented induction into the pulled-back `τ`. -/
theorem parabolicSelectedJacquetHom_rank_eq_representedUnitary
    (σ : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (τ : SmoothRep.{0, u, uW} ℂ (parabolicLeviPointSubgroup p l)) :
    Module.rank ℂ ((selectedWeightPart ((jacquetFunctor h hU).obj
        ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj σ)).representation
          (parabolicSplitComponentPointHom pres)
          (fun t => parabolicSplitComponentPointHom_range_le_center pres ⟨t, rfl⟩)
          (fun χ => SplitTorus.normalizedRealPart
            pres.isCompatible.splitComponent.isCentralSplitTorus.1.1 χ = 0)).toRepresentation.IntertwiningMap
              τ.representation) =
      Module.rank ℂ ((RepresentedParabolic.leviUnitaryJacquetModule p l n
          pres.isCompatible.parabolic pres.isCompatible.levi hn
          (parabolicRadical_isIso_subgroupMultiplication pres hG hn)
          pres.isCompatible.splitComponent
          ((RepresentedParabolic.leviInductionFunctor p l n pres.isCompatible.parabolic hn
            pres.isCompatible.levi (parabolicRadical_isIso_subgroupMultiplication pres hG hn)).obj
              (SmoothRep.pullback (parabolicLeviPointHomeomorph pres) σ))).representation.IntertwiningMap
        (SmoothRep.pullback (parabolicLeviPointHomeomorph pres) τ).representation) := by
  let hp := pres.isCompatible.parabolic
  let hl := pres.isCompatible.levi
  let ha := pres.isCompatible.splitComponent
  let hmul := parabolicRadical_isIso_subgroupMultiplication pres hG hn
  let e := parabolicLeviPointHomeomorph pres
  let := (isClosed_parabolicLeviPointSubgroup pres).locallyCompactSpace
  let := RepresentedParabolic.leviPoints_locallyCompactSpace p l hp hl
  let := RepresentedParabolic.leviPoints_nonarchimedeanGroup p l hp hl
  let X := (jacquetFunctor h hU).obj ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj σ)
  let P : (rationalPoints A.toGrp →* ℂˣ) → Prop := fun χ =>
    SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0
  let hj := ha.isCentralSplitTorus.isCentral.map_mem_center
  let Φ := SmoothRep.equivOfIso (parabolicRepresentedJacquetInductionIso pres hG hn h hU σ)
  let S := selectedWeightPart X.representation (parabolicSplitComponentPointHom pres)
    (fun t => parabolicSplitComponentPointHom_range_le_center pres ⟨t, rfl⟩) P
  exact LinearEquiv.rank_eq
    ((intertwiningCompLinearEquiv e S.toRepresentation τ.representation).trans
    ((intertwiningPrecompLinearEquiv (selectedWeightPartCompEquiv e X.isSmooth
      (rationalPoints.map a) hj
      (fun t => parabolicSplitComponentPointHom_range_le_center pres ⟨t, rfl⟩) P) _).trans
    ((intertwiningPrecompLinearEquiv (selectedWeightEquiv (rationalPoints.map a) hj P Φ) _).trans
      (intertwiningPrecompLinearEquiv
        (RepresentedParabolic.selectedLeviJacquetEquivUnitary p l n hp hl hn hmul ha _) _))))

/-- For an admissible literal induction and a target that is square-integrable
modulo the literal split center, the whole literal Jacquet Hom space has rank at
most the represented unitary Jacquet Hom space of the represented induction. -/
theorem parabolicJacquetHom_rank_le_representedUnitary
    (σ : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (hI : ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj σ).IsAdmissible) :
    let C := (parabolicSplitComponentPointHom pres).range
    let hC := parabolicSplitComponentPointHom_range_le_center pres
    letI : C.Normal := C.normal_of_le_center hC
    ∀ [MeasurableSpace (parabolicLeviPointSubgroup p l ⧸ C)]
      (qMeasure : Measure (parabolicLeviPointSubgroup p l ⧸ C)) [IsHaarMeasure qMeasure],
      IsSquareIntegrableModCentralSubgroup C hC σ.representation qMeasure →
      Module.rank ℂ (((jacquetFunctor h hU).obj
          ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj σ)).representation.IntertwiningMap
            σ.representation) ≤
        Module.rank ℂ ((RepresentedParabolic.leviUnitaryJacquetModule p l n
          pres.isCompatible.parabolic pres.isCompatible.levi hn
          (parabolicRadical_isIso_subgroupMultiplication pres hG hn)
          pres.isCompatible.splitComponent
          ((RepresentedParabolic.leviInductionFunctor p l n pres.isCompatible.parabolic hn
            pres.isCompatible.levi (parabolicRadical_isIso_subgroupMultiplication pres hG hn)).obj
              (SmoothRep.pullback (parabolicLeviPointHomeomorph pres) σ))).representation.IntertwiningMap
          (SmoothRep.pullback (parabolicLeviPointHomeomorph pres) σ).representation) := by
  dsimp only
  intro _ qMeasure _ hσ
  exact (parabolicJacquetHom_rank_le_unitaryWeights pres hn h hU hG _ hI σ qMeasure hσ).trans
    (parabolicSelectedJacquetHom_rank_eq_representedUnitary pres hG hn h hU σ σ).le

end Actual

end Langlands.Plancherel

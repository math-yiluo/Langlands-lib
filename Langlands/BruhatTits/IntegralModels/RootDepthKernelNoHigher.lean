import Langlands.BruhatTits.IntegralModels.RootModelPresentationIso
import Langlands.GroupScheme.IntegralModel.RootFieldDepthOfOrbit
import Langlands.Geometry.Building.RootFieldDescentValue
import Langlands.Geometry.Building.MaximalUnramifiedBuildingExistence

/-! # KP Lemma C.5.3 for actual roots without higher multiples -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

namespace RootFiltrationModelData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {S : CommGroupScheme (Spec (CommRingCat.of K))}
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] {ω : Kˣ → ℝ}
  {C : KPApartmentData i ω} {x : C.Apartment} {a : relativeRoots i} {r : ℝ}

/-- The root group of a supplied root-model presentation is affine over the field: it is
isomorphic to the generic fibre of the affine integral model. -/
theorem isAffineHom_rootGroup (U : RootFiltrationModelData R K C x a r) :
    IsAffineHom U.rootGroup.X.hom := by
  have : IsAffineHom
      ((GroupScheme.baseChange (Spec.algebraMap R K)).obj U.model.group).X.hom := by
    change IsAffineHom (Limits.pullback.snd U.model.group.X.hom (Spec.algebraMap R K))
    infer_instance
  have : IsIso U.model.genericIso.inv.hom.hom.left :=
    (inferInstance : IsIso
      ((Over.forget _).mapIso ((Grp.forget _).mapIso U.model.genericIso.symm)).hom)
  rw [← Over.w U.model.genericIso.inv.hom.hom]
  infer_instance

end RootFiltrationModelData

section Core

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    [IsAffine T.toGrp.X.left] [IsAffine S.toGrp.X.left]
    (f : S ⟶ T) (j : T.toGrp ⟶ G)

attribute [local instance] rootsGaloisAction

/-- **Kernels between root-depth models of a root without higher multiples.** Let
`i = f ≫ j` be a maximal split torus of a connected reductive group over a field `k` with a
surjective `ℤ`-valued henselian valuation `v`, where the closed maximal torus `j` represents
the centralizer of `i` and splits over the finite Galois extension `L`. Let `a` be a relative
root with no higher multiples and `β` an absolute root whose Galois orbit is the restriction
fibre of `a`. For every point `y` of an integer apartment class `D` satisfying V 6, any two
supplied smooth connected models of `U_{a,y,r}` and `U_{a,y,s}` with `r ≤ s` over a valuation
ring `O` equal to the valuation ring of `v`, and every model map compatible with the
inclusions into `G`, the special-fibre kernel is smooth, connected and unipotent, provided
smooth model maps extend over `O`. -/
theorem specialFibreKernel_properties_of_rootOrbit
    (v : Valuation k (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v)
    (hH : HenselianLocalRing v.valuationSubring)
    {O : ValuationSubring k} (hO : v.valuationSubring = O)
    (hext : IntegralModel.HasSmoothHomExtension (R := O) (L := k))
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i)
    (hit : CommGroupScheme.groupHom f ≫ j = i) (hjc : IsClosedSubgroup j)
    (hcent : (torusCentralizer i).IsRepresentedBy j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (hjL : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    (D : KPApartmentData i (IntegerValuation.order v)) (C : CentralizerDatum i)
    (hD : IntegerValuation.IsOmegaCompatible v D C) (y : D.Apartment)
    (a : relativeRoots i) (hhigh : RelativeRoot.HasNoHigherRoots i a)
    (β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    (hβ : β ∈ rootRestrictionFiber k L j f a)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    {r s : ℝ} (hrs : r ≤ s)
    (U : RootFiltrationModelData O k D y a r) (V : RootFiltrationModelData O k D y a s)
    (g : V.rootGroup ⟶ U.rootGroup) (hg : g ≫ U.inclusion = V.inclusion)
    (φ : V.model.Hom U.model g) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  subst hO
  subst hit
  classical
  have : IsAffineHom U.rootGroup.X.hom := U.isAffineHom_rootGroup
  let b := Module.finBasis k (rootOrbitField k L j β)
  have hq := U.isRootSubgroup
  let c := rootFieldDepthShift k L f j v hv hH hG hj hS hi hjc hcent hT hjL a.2 hhigh β hβ
    horbit D C hD y
  have hfil : ∀ t : ℝ, D.filtration y a t =
      additiveRootFiltration
        (FieldTheory.henselianSeparableAddValuation v hH (rootOrbitField k L j β))
        (rootFieldCoordinatesOfOrbit k L f j hG hj hS hcent hT a.2 hhigh β hβ horbit).equiv
        (t - c) := fun t =>
    filtration_eq_additiveRootFiltration_rootFieldDepthShift k L f j v hv hH hG hj hS hi hjc
      hcent hT hjL a.2 hhigh β hβ horbit D C hD y t
  let P' : RootFiltrationModelData v.valuationSubring k D y a r :=
    { rootGroup := U.rootGroup
      inclusion := U.inclusion
      isRootSubgroup := U.isRootSubgroup
      model := IntegralModel.rootFieldDepthModelOfOrbit k L f j hG hj hS hT a.2 hhigh β horbit
        hq b v hH hv (r - c)
      smooth := IntegralModel.rootFieldDepthModelOfOrbit_isSmooth k L f j hG hj hS hT a.2
        hhigh β horbit hq b v hH hv (r - c)
      geometricallyConnected :=
        IntegralModel.rootFieldDepthModelOfOrbit_hasGeometricallyConnectedFibres k L f j hG hj
          hS hT a.2 hhigh β horbit hq b v hH hv (r - c)
      integralPoints_eq := by
        rw [IntegralModel.rootFieldDepthModelOfOrbit_integralPoints_map k L f j hG hj hS hT a.2
          hhigh β horbit hq b v hH hv hcent hβ (r - c), hfil r] }
  let Q' : RootFiltrationModelData v.valuationSubring k D y a s :=
    { rootGroup := U.rootGroup
      inclusion := U.inclusion
      isRootSubgroup := U.isRootSubgroup
      model := IntegralModel.rootFieldDepthModelOfOrbit k L f j hG hj hS hT a.2 hhigh β horbit
        hq b v hH hv (s - c)
      smooth := IntegralModel.rootFieldDepthModelOfOrbit_isSmooth k L f j hG hj hS hT a.2
        hhigh β horbit hq b v hH hv (s - c)
      geometricallyConnected :=
        IntegralModel.rootFieldDepthModelOfOrbit_hasGeometricallyConnectedFibres k L f j hG hj
          hS hT a.2 hhigh β horbit hq b v hH hv (s - c)
      integralPoints_eq := by
        rw [IntegralModel.rootFieldDepthModelOfOrbit_integralPoints_map k L f j hG hj hS hT a.2
          hhigh β horbit hq b v hH hv hcent hβ (s - c), hfil s] }
  have hrs' : r - c ≤ s - c := by linarith
  let ψ : Q'.model.Hom P'.model (𝟙 _) :=
    IntegralModel.rootFieldDepthTransitionOfOrbit k L f j hG hj hS hT a.2 hhigh β horbit hq b
      v hH hv (r - c) (s - c) hrs'
  have hψ := IntegralModel.rootFieldDepthModelOfOrbit_kernel_properties k L f j hG hj hS hT a.2
    hhigh β horbit hq b v hH hv (r - c) (s - c) hrs' ψ
  exact U.specialFibreKernel_properties_of_presentation V P' Q' hext g hg (𝟙 _)
    (Category.id_comp _) φ ψ hψ

end Core

/-- **KP Lemma C.5.3 for roots without higher multiples.** The conclusion of
`UnramifiedRootDepthKernelStatement`, restricted to relative roots `a` of the actual maximal
unramified building data such that no multiple `n • a` with `n ≥ 2` is a relative root. -/
def UnramifiedNoHigherRootDepthKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom] (C : MaximalUnramified.BuildingData F G)
    (x : C.Apartment) (a : relativeRoots C.i),
    RelativeRoot.HasNoHigherRoots C.i a →
    ∀ (r s : ℝ), r ≤ s →
    ∀ (U : RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
        C.apartment x a r)
      (V : RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
        C.apartment x a s)
      (f : V.rootGroup ⟶ U.rootGroup),
      f ≫ U.inclusion = V.inclusion →
      ∀ φ : V.model.Hom U.model f,
        Smooth (kernel φ.specialFibreMap).X.hom ∧
          ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
            IsUnipotent (kernel φ.specialFibreMap)

attribute [local instance] rootsGaloisAction

/-- Proof of `UnramifiedNoHigherRootDepthKernelStatement`: the torus centralizer of the
maximal split torus is a maximal torus split by a finite Galois extension, so the core
comparison `specialFibreKernel_properties_of_rootOrbit` applies. -/
theorem unramifiedNoHigherRootDepthKernel :
    UnramifiedNoHigherRootDepthKernelStatement.{u} := by
  intro F _ _ _ _ G _ C x a hhigh r s hrs U V g hg φ
  have hG := C.isConnectedReductive
  have hi := C.isMaximalSplitTorus
  have hQS := MaximalUnramified.isQuasiSplit F hG
  have : Smooth G.X.hom := hG.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  obtain ⟨Z, j, hj, hjc⟩ :=
    fieldCentralizerRepresentability (inertiaFixedField F) C.S G hi.1.1.isAffineHom C.i
  have hZ : IsTorus Z := isTorus_of_quasiSplit_torusCentralizer
    quasiSplitTorusCentralizerExistence maximalSplitTorusConjugacy hQS hi hj
  let T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))) :=
    { Z with comm := hZ.isCommMonObj }
  let jT : T.toGrp ⟶ G := j
  let t : C.S ⟶ T := Additive.ofMul (torusCentralizerFactor C.i hj)
  have : IsAffineHom T.toGrp.X.hom := hjc.isAffineHom
  have : LocallyOfFiniteType T.toGrp.X.hom := hjc.locallyOfFiniteType
  have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have : IsAffineHom C.S.toGrp.X.hom := hi.1.1.isAffineHom
  have : IsAffine C.S.toGrp.X.left := isAffine_of_isAffineHom C.S.toGrp.X.hom
  have hit : CommGroupScheme.groupHom t ≫ jT = C.i := torusCentralizerFactor_comp C.i hj
  have hself : torusCentralizer jT = SubgroupFunctor.range jT :=
    le_antisymm ((torusCentralizer_le_of_factor jT C.i (torusCentralizerFactor C.i hj)
      (torusCentralizerFactor_comp C.i hj)).trans hj.2.symm.le) (range_le_torusCentralizer jT)
  have hjm : IsMaximalTorus jT := isMaximalTorus_of_torusCentralizer_eq hZ hjc hself
  obtain ⟨L, _, _, _, _, hK⟩ := torusFiniteGaloisSplitting (inertiaFixedField F) Z hZ
  have hjK := isMaximalTorus_baseChange_of_torusCentralizer_eq L hZ hjc hself
  have : Algebra.IsAlgebraic (inertiaFixedField F) L :=
    Algebra.IsAlgebraic.of_finite (inertiaFixedField F) L
  obtain ⟨J, _, P, hP, -⟩ := rootDatumExistence L
    ((GroupScheme.baseChange (algebraBaseMap (inertiaFixedField F) L)).obj G)
    (hG.baseChange_of_algebraicExtension (K := L))
    ((CommGroupScheme.baseChange (algebraBaseMap (inertiaFixedField F) L)).obj T) hK
    ((GroupScheme.baseChange (algebraBaseMap (inertiaFixedField F) L)).map jT) hjK
  have hmaxf : IsMaximalSplitTorus (CommGroupScheme.groupHom t ≫ jT) := hit ▸ hi
  have hcent' : (torusCentralizer (CommGroupScheme.groupHom t ≫ jT)).IsRepresentedBy jT :=
    hit ▸ hj
  have ha' : (a : characterLattice C.S) ∈ relativeRoots (CommGroupScheme.groupHom t ≫ jT) := by
    rw [hit]
    exact a.2
  have hne := rootRestrictionFiber_nonempty (inertiaFixedField F) L jT t hi.1.1 hK ⟨a, ha'⟩
  have horbit := rootOrbit_eq_restrictionFiber_of_torusCentralizer (inertiaFixedField F) L t jT
    hmaxf hjc hcent' hK hP a hne.some_mem
  exact specialFibreKernel_properties_of_rootOrbit (inertiaFixedField F) L t jT
    (MaximalUnramified.valuation F) (MaximalUnramified.valuation_surjective F)
    (MaximalUnramified.valuationSubring_isHenselian F) (MaximalUnramified.valuationSubring_eq F)
    (IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F)
    hG hjm hi.1.1 hi hit hjc hj hK hjK C.apartment C.centralizer C.isOmegaCompatible x a hhigh
    hne.some hne.some_mem horbit hrs U V g hg φ

end Langlands.BruhatTits.IntegralModels

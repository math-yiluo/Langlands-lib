import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement
import Langlands.BruhatTits.IntegralModels.Transport.Model
import Langlands.Geometry.Building.UnramifiedZeroTransport
import Langlands.Geometry.Building.UnramifiedZeroIndependenceStatement
import Langlands.Geometry.Building.UnramifiedQuasiSplitStatement
import Langlands.Geometry.Building.KPZeroDatumConstruction
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Reducing KP 8.4.15 to apartment subsets and compatible zero data -/


noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building
open scoped Pointwise CategoryTheory.MonObj

namespace Langlands.Geometry.Building.UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}

/-- Replace the torus of a zero datum by a prescribed maximally split maximal
torus `j : M → H`, keeping its derived subgroup and simply connected cover and
choosing a finite Galois splitting field of `M` inside `F^sep`. -/
def withTorus (E : UnramifiedZeroDatum F H)
    {M : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (j : M.toGrp ⟶ H) (hj : IsMaximallySplitMaximalTorus j) : UnramifiedZeroDatum F H := by
  classical
  let : IsAffineHom H.X.hom := E.isSimplyConnectedDerivedCover.isConnectedReductive.isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsClosedImmersion j.hom.hom.left := hj.1.2.1
  let : IsAffine M.X.left := isAffine_of_isAffineHom j.hom.hom.left
  let hsplit :=
    exists_finiteGaloisSplittingField_inside (SeparableClosure F) M.toGrp hj.1.1
  exact {
    T := M
    isAffine := inferInstance
    i := j
    isMaximallySplitMaximalTorus := hj
    L := hsplit.choose
    finiteDimensional := hsplit.choose_spec.1
    isGalois := hsplit.choose_spec.2.1
    isSplitTorus := hsplit.choose_spec.2.2
    D := E.D
    C := E.C
    d := E.d
    π := E.π
    isSimplyConnectedDerivedCover := E.isSimplyConnectedDerivedCover }

@[simp] theorem withTorus_i (E : UnramifiedZeroDatum F H)
    {M : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (j : M.toGrp ⟶ H) (hj : IsMaximallySplitMaximalTorus j) :
    (E.withTorus j hj).i = j :=
  rfl

/-- If the ambient group is quasi-split, every maximal split torus `a` lies in a
maximally split maximal torus representing its centralizer, and some zero datum
has that torus. -/
theorem exists_isRepresentedBy_torusCentralizer (E : UnramifiedZeroDatum F H)
    (hquasi : IsQuasiSplit H)
    {A : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    {a : A.toGrp ⟶ H} (ha : IsMaximalSplitTorus a) :
    ∃ E' : UnramifiedZeroDatum F H, (torusCentralizer a).IsRepresentedBy E'.i := by
  let : IsAffineHom H.X.hom := E.isSimplyConnectedDerivedCover.isConnectedReductive.isAffineHom
  let : Smooth H.X.hom := E.isSimplyConnectedDerivedCover.isConnectedReductive.smooth
  obtain ⟨M, j, hj, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType H a ha.1.1.isTorus ha.1.2
  have hms : IsMaximallySplitMaximalTorus j := ⟨hj, A, a, f, ha, hf⟩
  exact ⟨E.withTorus j hms,
    quasiSplitMaximalTorusCentralizer _ H hquasi M A j a f hj ha hf⟩

end Langlands.Geometry.Building.UnramifiedZeroDatum

namespace Langlands.BruhatTits.IntegralModels

private instance unramifiedModelKernelReductionAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- Conjugating by `g⁻¹` carries the pointwise fixer of a `g`-translate of a set
of the reduced building onto the pointwise fixer of the set. -/
theorem pointwiseFixer_smul_image_map_conj
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (Y : Set C.ReducedBuilding) :
    (C.pointwiseFixer ((fun y => g • y) '' Y)).map (MulAut.conj g⁻¹).toMonoidHom =
      C.pointwiseFixer Y := by
  change (fixingSubgroup (rationalPoints (baseChanged F (inertiaFixedField F) G))
      ((fun y => g • y) '' Y)).map (MulAut.conj g⁻¹).toMonoidHom =
    fixingSubgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)) Y
  apply SubMulAction.fixingSubgroup_map_conj_eq
  rw [Set.image_smul, inv_smul_smul]

/-- **KP Proposition 8.4.15 in the apartment, for a compatible zero datum.**
The special case of `UnramifiedModelKernelStatement` with no translation
(`g = 1`, the sets `Ωa ⊆ closure Ωa'` taken directly in the apartment of `C`)
and with a zero datum `E` whose torus represents the centralizer of the maximal
split torus of `C`. This is an internal reduction target, not a statement from
the literature. -/
def UnramifiedCompatibleModelKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G)),
    (torusCentralizer C.i).IsRepresentedBy E.i →
    ∀ (Ωa Ωa' : Set C.Apartment),
    Ωa.Nonempty →
    (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa')) →
    Ωa ⊆ @closure C.Apartment
      (⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) Ωa' →
    ∀ (N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
        (baseChanged F (inertiaFixedField F) G)),
      N.IsSmooth → N'.IsSmooth →
      N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ωa) →
      N'.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ωa') →
      ∀ ψ : N'.Hom N (𝟙 _),
        Smooth (kernel ψ.specialFibreMap).X.hom ∧
          ConnectedSpace (kernel ψ.specialFibreMap).X.left ∧
            IsUnipotent (kernel ψ.specialFibreMap)

set_option maxHeartbeats 1600000 in
/-- Transporting a model by the inner automorphism `Int(g⁻¹)` turns the integral
points `E(0) ∩ G(K)_{g Y}` into `E'(0) ∩ G(K)_Y` for any second zero datum `E'`,
given the independence of `G(K)^0` from the zero datum. -/
theorem integralPoints_transport_innerIso
    (hind : UnramifiedZeroPointsIndependenceStatement.{u})
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E E' : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (Y : Set C.Apartment)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hM : M.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Y)) :
    (M.transport ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹)).integralPoints =
      E'.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Y) := by
  have hzero : E.zeroPoints.map
      (rationalPoints.map ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹).hom) =
        E'.zeroPoints := by
    rw [← UnramifiedZeroDatum.zeroPoints_transport]
    exact hind F _ _ _
  have hset : (fun x => g • C.apartmentMap x) '' Y = (fun y => g • y) '' (C.apartmentMap '' Y) :=
    (Set.image_image _ _ _).symm
  have hfix : (C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Y)).map
      (rationalPoints.map ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹).hom) =
        C.pointwiseFixer (C.apartmentMap '' Y) := by
    rw [hset, rationalPoints_map_innerIso]
    exact pointwiseFixer_smul_image_map_conj C g _
  have h1 := IntegralModel.transport_integralPoints M
    ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹)
  have h2 := congrArg (Subgroup.map
    (rationalPoints.map ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹).hom)) hM
  have h3 := Subgroup.map_inf_eq E.zeroPoints
    (C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Y))
    (rationalPoints.map ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹).hom)
    (rationalPoints_map_injective_of_iso _)
  exact h1.trans (h2.trans (h3.trans (by rw [hzero, hfix])))

omit [IsAffineHom G.X.hom] in
/-- The special-fibre map of a transported identity-generic model morphism is the
original special-fibre map, so the kernel conclusions agree. -/
theorem kernel_transportId_iff
    {N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G)}
    (ψ : N'.Hom N (𝟙 _))
    (e : baseChanged F (inertiaFixedField F) G ≅ baseChanged F (inertiaFixedField F) G) :
    (Smooth (kernel (ψ.transportId e).specialFibreMap).X.hom ∧
        ConnectedSpace (kernel (ψ.transportId e).specialFibreMap).X.left ∧
          IsUnipotent (kernel (ψ.transportId e).specialFibreMap)) ↔
      (Smooth (kernel ψ.specialFibreMap).X.hom ∧
        ConnectedSpace (kernel ψ.specialFibreMap).X.left ∧
          IsUnipotent (kernel ψ.specialFibreMap)) :=
  Iff.rfl

set_option maxHeartbeats 1600000 in
/-- **Reduction of KP Proposition 8.4.15 to the apartment and a compatible zero
datum.** Given that connected reductive groups over the maximal unramified
extension are quasi-split and that `G(K)^0` does not depend on the zero datum,
the special case `UnramifiedCompatibleModelKernelStatement` implies the full
`UnramifiedModelKernelStatement`. The two hypotheses are published unproved
statements; this theorem does not prove the host statement. -/
theorem unramifiedModelKernel_of_compatible
    (hquasi : UnramifiedQuasiSplitStatement.{u})
    (hind : UnramifiedZeroPointsIndependenceStatement.{u})
    (hcore : UnramifiedCompatibleModelKernelStatement.{u}) :
    UnramifiedModelKernelStatement.{u} := by
  intro F _ _ _ _ G _ C E g Ωa Ωa' hne hbdd hcl N N' hN hN' hNpts hN'pts ψ
  obtain ⟨E', hE'⟩ := E.exists_isRepresentedBy_torusCentralizer
    (hquasi F _ C.isConnectedReductive) C.isMaximalSplitTorus
  have hpts := integralPoints_transport_innerIso hind C E E' g Ωa N hNpts
  have hpts' := integralPoints_transport_innerIso hind C E E' g Ωa' N' hN'pts
  have key := hcore F G C E' hE' Ωa Ωa' hne hbdd hcl
    (N.transport ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹))
    (N'.transport ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹)) hN hN' hpts hpts'
    (ψ.transportId ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹))
  exact (kernel_transportId_iff ψ _).1 key

end Langlands.BruhatTits.IntegralModels
